#pragma once

#include <tpcc/stdlike/atomic.hpp>
#include <tpcc/support/bit_twiddling.hpp>
#include <tpcc/support/compiler.hpp>

#include <limits>
#include <thread>
#include <vector>
#include <iostream>

#define hash_fix 191838341164625791ull

namespace tpcc {
namespace solutions {
////////////////////////////////////////////////////////////////////////////////

template <typename T>
class AtomicMarkedPointer {
 public:
  struct MarkedPointer {
    MarkedPointer(T* ptr, bool marked) : ptr_(ptr), marked_(marked) {
    }

    bool operator==(const MarkedPointer& that) const {
      return (ptr_ == that.ptr_) && (marked_ == that.marked_);
    }

    T* ptr_;
    bool marked_;
  };

  using PackedMarkedPointer = size_t;

 public:
  AtomicMarkedPointer(T* ptr = nullptr) : packed_ptr_{Pack({ptr, false})} {
  }

  MarkedPointer Load() const {
    return Unpack(packed_ptr_.load());
  }

  T* LoadPointer() const {
    const auto marked_ptr = Load();
    return marked_ptr.ptr_;
  }

  void Store(MarkedPointer marked_ptr) {
    packed_ptr_.store(Pack(marked_ptr));
  }

  void Store(T* ptr) {
    Store(MarkedPointer{ptr, false});
  }

  AtomicMarkedPointer& operator=(T* ptr) {
    Store(MarkedPointer{ptr, false});
    return *this;
  }

  bool TryMark(T* ptr) {
    return CompareAndSet({ptr, false}, {ptr, true});
  }

  bool Mark() {
    T* ptr = LoadPointer();
    while (true) {
      if (CompareAndSet({ptr, false}, {ptr, true}))
        return true;
      if (IsMarked())
        return false;
      ptr = LoadPointer();
    }
  }

  bool TryRemoveMark(T* ptr) {
    return CompareAndSet({ptr, true}, {ptr, false});
  }

  bool RemoveMark() {
    T* ptr = LoadPointer();
    while (true) {
      if (CompareAndSet({ptr, true}, {ptr, false}))
        return true;
      if (!IsMarked())
        return false;
      ptr = LoadPointer();
    }
  }

  bool IsMarked() const {
    return packed_ptr_.load() & 1;
  }

  bool CompareAndSet(MarkedPointer expected, MarkedPointer desired) {
    auto expected_packed = Pack(expected);
    const auto desired_packed = Pack(desired);
    return packed_ptr_.compare_exchange_strong(expected_packed, desired_packed);
  }

 private:
  static PackedMarkedPointer Pack(MarkedPointer marked_ptr) {
    return reinterpret_cast<size_t>(marked_ptr.ptr_) ^
           (marked_ptr.marked_ ? 1 : 0);
  }

  static MarkedPointer Unpack(PackedMarkedPointer packed_marked_ptr) {
    const auto marked = static_cast<bool>(packed_marked_ptr & 1);
    const auto ptr = reinterpret_cast<T*>(packed_marked_ptr ^ marked);
    return {ptr, marked};
  }

 private:
  tpcc::atomic<PackedMarkedPointer> packed_ptr_;
};

////////////////////////////////////////////////////////////

template <typename T>
struct KeyTraits {
  static T LowerBound() {
    return std::numeric_limits<T>::min();
  }

  static T UpperBound() {
    return std::numeric_limits<T>::max();
  }
};

//////////////////////////////////////////////////////////////////////////////////

template <typename V, class TTraits = KeyTraits<size_t>>
class LockFreeHashSet {
 private:
  struct Node {
    size_t key_;
    V val_;
    AtomicMarkedPointer<Node> next_;

    Node(size_t key, const V& val) : key_(key), val_(val), next_(nullptr) {
    }

    Node(size_t key) : key_(key), next_(nullptr) {
    }

    bool IsMarked() const {
      return next_.IsMarked();
    }
  };

  struct EdgeCandidate {
    Node* pred_;
    Node* curr_;

    EdgeCandidate(Node* pred, Node* curr) : pred_(pred), curr_(curr) {
    }
  };
  class TableStack {
   public:
    struct Table {
      std::vector<Node*>* table_{nullptr};
      Table* next_ = nullptr;
      Table(std::vector<Node*>* table, Table* next)
          : table_(table), next_(next) {
      }
    };

    std::vector<Node*>* GetTable() const {
      return table_.load()->table_;
    }

    void PushFirstTable(std::vector<Node*>* new_table) {
      table_.store(new Table(new_table, nullptr));
    }

    bool PushTable(std::vector<Node*>* old_table,
                   std::vector<Node*>* new_table) {
      Table* ptr = table_.load();
      Table* new_ptr = new Table(new_table, ptr);
      if (ptr->table_ == old_table &&
          table_.compare_exchange_strong(ptr, new_ptr))
        return true;
      else
        delete new_ptr;
      return false;
    }
    ~TableStack() {
      DeleteTable(table_.load());
    }

   private:
    void DeleteTable(Table* ptr) {
      if (ptr) {
        DeleteTable(ptr->next_);
        delete ptr;
      }
    }
    std::atomic<Table*> table_{nullptr};
  };

 public:
  explicit LockFreeHashSet() {
    CreateEmptyList();
    table_.PushFirstTable(new std::vector<Node*>(2, head_));
  }

  bool Insert(const V& val) {
    size_t hash = hash_function_(val) * hash_fix;
    std::vector<Node*>* table = table_.GetTable();
    Node* new_node = new Node(hash, val);
    EdgeCandidate edge(nullptr, nullptr);
    bool pred_marked;
    do {
      edge = Locate(table, hash, val);
      if (edge.curr_->key_ == hash && edge.curr_->val_ == val) {
        delete new_node;
        if (edge.curr_->next_.RemoveMark()) {
          size_.fetch_add(1);
          return true;
        } else
          return false;
      }
      new_node->next_.Store(edge.curr_);
      pred_marked = edge.pred_->next_.IsMarked();
    } while (!edge.pred_->next_.CompareAndSet({edge.curr_, pred_marked},
                                              {new_node, pred_marked}));
    size_.fetch_add(1);
    long long d = fullsize_.fetch_add(1) - table->size();
    if (d >= 0 && !(d % 10)) {
      Rehash(table, 2 * table->size());
    }
    return true;
  }

  bool Remove(const V& val) {
    size_t hash = hash_function_(val) * hash_fix;
    std::vector<Node*>* table = table_.GetTable();
    EdgeCandidate edge(nullptr, nullptr);
    do {
      edge = Locate(table, hash, val);
      if (edge.curr_->key_ > hash || edge.curr_->val_ != val ||
          edge.curr_->next_.IsMarked())
        return false;
    } while (!edge.curr_->next_.Mark());
    size_.fetch_sub(1);
    return true;
  }

  bool Contains(const V& val) const {
    size_t hash = hash_function_(val) * hash_fix;
    std::vector<Node*>* table = table_.GetTable();
    EdgeCandidate edge(nullptr, nullptr);
    edge = Locate(table, hash, val);
    return edge.curr_->key_ == hash && edge.curr_->val_ == val &&
           !edge.curr_->next_.IsMarked();
  }

  size_t GetSize() const {
    return size_.load();
  }

  ~LockFreeHashSet() {
    DeleteNode(head_);
  }

 private:
  void DeleteNode(Node* ptr) {
    if (ptr) {
      DeleteNode(ptr->next_.LoadPointer());
      delete ptr;
    }
  }

  void CreateEmptyList() {
    // create sentinel nodes
    head_ = new Node(TTraits::LowerBound());
    head_->next_ = new Node(TTraits::UpperBound());
  }

  void Rehash(std::vector<Node*>* old_table, size_t new_size) {
    EdgeCandidate edge(head_, head_->next_.LoadPointer());
    int j = 0;
    std::vector<Node*>* new_table = new std::vector<Node*>(new_size);
    for (size_t i = 0; i + TTraits::UpperBound() / new_size > i;
         i += TTraits::UpperBound() / new_size) {
      while (edge.curr_->key_ < i) {
        edge.pred_ = edge.curr_;
        edge.curr_ = edge.curr_->next_.LoadPointer();
      }
      (*new_table)[j++] = edge.pred_;
    }
    if (!table_.PushTable(old_table, new_table)) {
      delete new_table;
    }
  }

  EdgeCandidate Locate(std::vector<Node*>* table, size_t hash,
                       const V& val) const {
    Node* begin = (*table)[hash / (TTraits::UpperBound() / table->size())];
    EdgeCandidate edge(begin, begin->next_.LoadPointer());
    while (edge.curr_->key_ < hash ||
           (edge.curr_->key_ == hash && edge.curr_->val_ < val)) {
      edge.pred_ = edge.curr_;
      edge.curr_ = edge.curr_->next_.LoadPointer();
    }
    return edge;
  }

 private:
  std::atomic<size_t> size_{0};
  std::atomic<size_t> fullsize_{0};
  Node* head_{nullptr};
  std::hash<V> hash_function_;
  TableStack table_;
};

}  // namespace solutions
}  // namespace tpcc
