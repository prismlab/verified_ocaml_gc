#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdio>
#include <future>
#include <iostream>
#include <set>
#include <thread>
#include <unordered_set>
#include <vector>

#ifdef USE_BDWGC
#include "bdwgc/include/gc.h"
#endif
using namespace std::literals::string_literals;

// #define USE_DEALLOC

struct AllocatorStats {
  size_t cur_free_wsz;
  size_t total_wsz;
  size_t min_expansion_wsz;
};

struct HeapRange {
  size_t first_header;
  size_t rightmost_value;
};

extern "C" uint8_t *alloc(unsigned long long);
extern "C" void dealloc(uint8_t *);
extern "C" void sweep(void);
extern "C" void mark(uintptr_t val);
extern "C" AllocatorStats get_allocator_stats();
extern "C" HeapRange get_heap_range();
extern "C" size_t get_freelist_head();

#ifdef USE_VERIFIED_SWEEP
extern "C" uint64_t Impl_GC7_sweep1_with_free_list(uint8_t *g,
                                                   uint64_t *h_index,
                                                   uint64_t *free_list_ptr,
                                                   uint64_t limit);
#endif

#ifdef USE_VERIFIED_MARK
extern "C" void Impl_GC7_mark_heap5(uint8_t *g, uint64_t *st, uint64_t *st_top);
#endif

template <typename T>
// requires(std::is_default_constructible_v<T>)
class DynamicCArr {
  std::unique_ptr<T[]> ptr;
  std::size_t capacity;

public:
  DynamicCArr(size_t sz = 1) : ptr(std::make_unique<T[]>(sz)), capacity(sz) {
    static_assert(std::is_default_constructible<T>::value);
  }
  void resize(size_t new_sz) {
    if (capacity >= new_sz) {
      return;
    }
    ptr = std::make_unique<T[]>(new_sz);
    capacity = new_sz;
  }
  T *get_underlying_ptr() const { return ptr.get(); }
};

class Gc {
  static inline std::set<uintptr_t> roots;
  static inline uintptr_t stack_top;

  static inline DynamicCArr<uintptr_t> stack;

public:
  static inline size_t tot_allocations = 0;
  static inline size_t tot_collections = 0;

public:
  template <typename T> class Ptr {
    // This stores pointer to the header
    T *underlying_ptr;

    uintptr_t *get_header_ptr() {
#ifdef USE_VERIFIED_MARK
      return reinterpret_cast<uintptr_t *>(underlying_ptr);
#else
      return reinterpret_cast<uintptr_t *>(
          reinterpret_cast<uintptr_t>(this->underlying_ptr) -
          sizeof(uintptr_t));
#endif
    }

  protected:
    T *get_underlying_ptr() const { return this->underlying_ptr; }

  public:
    Ptr(T *ptr)
        :
#ifdef USE_VERIFIED_MARK
          underlying_ptr{(T *)((uintptr_t)(ptr))}
#else
          underlying_ptr{reinterpret_cast<T *>(
              reinterpret_cast<uintptr_t>(ptr) + sizeof(uintptr_t))}
#endif
    {
    }

    Ptr(const Ptr<T> &other) : underlying_ptr{other.get_underlying_ptr()} {}
    void free() {
#ifdef USE_DEALLOC
      if (this->is_null()) {
        return;
      }
      std::destroy_at(this->get_val_ptr());
      dealloc(reinterpret_cast<uint8_t *>(this->get_val_ptr()));
#endif
    }

    T *get_val_ptr() {
      return reinterpret_cast<T *>(
          reinterpret_cast<uintptr_t>(this->get_header_ptr()) +
          sizeof(uintptr_t));
    }

    T &operator*() {
#ifdef USE_VERIFIED_MARK
      assert(this->get_underlying_ptr() != NULL);
#else
      assert((uintptr_t)(this->get_underlying_ptr()) - sizeof(uintptr_t) !=
             (uintptr_t) nullptr);
#endif
      return *this->get_val_ptr();
    }
    T *operator->() {

#ifdef USE_VERIFIED_MARK
      assert(this->get_underlying_ptr() != NULL);
#else
      assert((uintptr_t)(this->get_underlying_ptr()) - sizeof(uintptr_t) !=
             (uintptr_t) nullptr);
#endif
      return this->get_val_ptr();
    }
    bool is_null() {
#ifdef USE_VERIFIED_MARK
      assert(this->get_underlying_ptr() != NULL);
#else
      assert((uintptr_t)(this->get_underlying_ptr()) - sizeof(uintptr_t) !=
             (uintptr_t) nullptr);
#endif
      // Null is something with zero size
      return (*(this->get_header_ptr())) >> 10 == 0;
    }
  };

  // template <class U> Ptr(U *) -> Ptr<U>;

  template <typename T> class Root : public Ptr<T> {
  public:
    template <typename F> Root(F f) : Root(handle_exn(f)) {}

  private:
    template <typename F>
    // requires std::is_same_v<decltype(std::declval<F>()()), Gc::Ptr<T>>
    static Ptr<T> handle_exn(F &&f) {

      try {
        return f();
      } catch (std::runtime_error e) {
        std::cerr << e.what() << std::endl;
        throw e;
      }
    }
    Root(T *ptr) : Ptr<T>(ptr) {
      Gc::roots.insert(reinterpret_cast<uintptr_t>(this->get_underlying_ptr()));
    }
    Root(Ptr<T> ptr) : Ptr<T>(ptr) {
      Gc::roots.insert(reinterpret_cast<uintptr_t>(this->get_underlying_ptr()));
    }

  public:
    ~Root() {
      Gc::roots.erase(reinterpret_cast<uintptr_t>(this->get_underlying_ptr()));
#ifdef USE_DEALLOC
      this->free();
#endif
    }
  };

  template <typename T>
  // requires(sizeof(T) % sizeof(uintptr_t) == 0 && sizeof(T) > 0)
  static Gc::Ptr<T> alloc() {
    static_assert(sizeof(T) % sizeof(uintptr_t) == 0 && sizeof(T) > 0);
    size_t wsz = sizeof(T) / sizeof(uintptr_t);

    uint8_t *mem = NULL;
    {
      tot_allocations++;
      mem = ::alloc(wsz);
    }

    int got_null_cnt = 0;
  again:
    if ((uintptr_t)mem - sizeof(uintptr_t) == (uintptr_t) nullptr) {
      got_null_cnt++;

      if (got_null_cnt == 2) [[unlikely]] {
        throw std::runtime_error(
            "Memory left: "s +
            std::to_string(get_allocator_stats().cur_free_wsz));
      }

      // printf("About to collect\n");
      Gc::collect();
      // printf("Collection Completed\n");
      mem = ::alloc(wsz);
      goto again;
    }

    // must return header to maintain compatibility with mark implementation
    mem = mem - sizeof(uintptr_t);
    return reinterpret_cast<T *>(mem);
  }
  static void collect() {
    Gc::tot_collections++;

#ifdef USE_VERIFIED_MARK
    auto stat = get_allocator_stats();
    // size_t stack_size = (stat.total_wsz - stat.cur_free_wsz) + 10;
    Gc::stack.resize(stat.min_expansion_wsz);
    Gc::stack_top = 0;
#endif

    for (auto ptr : roots) {
#ifdef USE_VERIFIED_MARK
      Gc::stack.get_underlying_ptr()[Gc::stack_top++] =
          reinterpret_cast<uintptr_t>(ptr);

      Impl_GC7_mark_heap5((uint8_t *)NULL, Gc::stack.get_underlying_ptr(),
                          std::addressof(Gc::stack_top));
#else
      assert(((*reinterpret_cast<uintptr_t *>(ptr - sizeof(uintptr_t)) >> 8) &
              0b11) == 0b01);
      mark(reinterpret_cast<uintptr_t>(ptr));
#endif
    }
    assert(Gc::stack_top == 0);

#ifdef USE_VERIFIED_SWEEP
    auto heap_range = get_heap_range();
    uint64_t *freelist_starting_value = (uint64_t *)get_freelist_head();
    uint64_t freelist_starting_header_value =
        ((uint64_t)freelist_starting_value) -
        sizeof(uintptr_t); // this is like a starting entry in free list, this
                           // is never actually allocated

    uint64_t prev_ptr = freelist_starting_header_value;
    *freelist_starting_value -= 8U;
    Impl_GC7_sweep1_with_free_list(NULL, &heap_range.first_header, &prev_ptr,
                                   heap_range.rightmost_value);
    if (freelist_starting_header_value == prev_ptr) {
      *freelist_starting_value += 8U;
    } else {
      prev_ptr += 8U;
      *(uint64_t *)prev_ptr = 0U;
    }
#else
    ::sweep();
#endif
  }
};

class gcnullptr_t {
public:
  const uintptr_t zero;
  const uintptr_t padding1;
  const uintptr_t padding2;
  constexpr gcnullptr_t() : zero(0b1100000000), padding1(0), padding2(0) {}
  template <typename T> Gc::Ptr<T> to_ptr() {
#ifdef USE_VERIFIED_MARK
    return Gc::Ptr<T>(reinterpret_cast<T *>(this));
#else
    return Gc::Ptr<T>(reinterpret_cast<T *>(reinterpret_cast<uintptr_t>(this) +
                                            sizeof(uintptr_t)));
#endif
  }
};
gcnullptr_t gcnullptr = gcnullptr_t();

struct BinaryTree {
  Gc::Ptr<BinaryTree> l;
  Gc::Ptr<BinaryTree> r;
  BinaryTree() = delete;
  BinaryTree(const BinaryTree &) = delete;
  ~BinaryTree() {
// #define USE_DEALLOC
#ifdef USE_DEALLOC
    this->l.free();
    this->r.free();
#endif
  }

  static Gc::Root<BinaryTree> create(size_t d) {
    Gc::Root<BinaryTree> node =
        Gc::Root<BinaryTree>([d]() { return Gc::alloc<BinaryTree>(); });
    node->l = gcnullptr.to_ptr<BinaryTree>();
    node->r = gcnullptr.to_ptr<BinaryTree>();
    static std::function<void(size_t, Gc::Ptr<BinaryTree> &)> f =
        [&](size_t d, Gc::Ptr<BinaryTree> &to_be_assigned) -> void {
      Gc::Ptr<BinaryTree> node = Gc::alloc<BinaryTree>();
      node->l = gcnullptr.to_ptr<BinaryTree>();
      node->r = gcnullptr.to_ptr<BinaryTree>();
      to_be_assigned = node;
      if (d != 0) {
        f(d - 1, node->l);
        f(d - 1, node->r);
      }
    };
    f(d - 1, node->l);
    f(d - 1, node->r);
    return node;
  }
  size_t check() {
    if (this->l.is_null()) {
      return 1;
    } else {
      return 1 + this->l->check() + this->r->check();
    }
  }
};

struct BinaryTreeWithRawPtr {
  BinaryTreeWithRawPtr *l;
  BinaryTreeWithRawPtr *r;
  BinaryTreeWithRawPtr(BinaryTreeWithRawPtr *l, BinaryTreeWithRawPtr *r)
      : l(l), r(r) {}
  BinaryTreeWithRawPtr(const BinaryTreeWithRawPtr &) = delete;
  ~BinaryTreeWithRawPtr() {}

  static std::unique_ptr<BinaryTreeWithRawPtr> create(size_t d) {
    return std::make_unique<BinaryTreeWithRawPtr>(_create(d - 1),
                                                  _create(d - 1));
  }
  static BinaryTreeWithRawPtr *_create(size_t d) {
    if (d == 0)
      return nullptr;
    return new BinaryTreeWithRawPtr(_create(d - 1), _create(d - 1));
  };
  size_t check() {
    if (this->l == nullptr) {
      return 1;
    } else {
      return 1 + this->l->check() + this->r->check();
    }
  }
};
struct BinaryTreeBDWGC {
  BinaryTreeBDWGC *l;
  BinaryTreeBDWGC *r;
  BinaryTreeBDWGC(BinaryTreeBDWGC *l, BinaryTreeBDWGC *r) : l(l), r(r) {}
  BinaryTreeBDWGC(const BinaryTreeBDWGC &) = delete;
  ~BinaryTreeBDWGC() {}

  static BinaryTreeBDWGC *create(size_t d) {
#ifdef USE_BDWGC
    BinaryTreeBDWGC *node =
        (BinaryTreeBDWGC *)GC_malloc(sizeof(BinaryTreeBDWGC));
    node->l = nullptr;
    node->r = nullptr;
    if (d == 0)
      return node;
    node->l = create(d - 1);
    node->r = create(d - 1);
    return node;
#endif
    return nullptr;
  }
  size_t check() {
#ifdef USE_BDWGC
    if (this->l == nullptr) {
      return 1;
    } else {
      return 1 + this->l->check() + this->r->check();
    }
#endif
    return 0;
  }
};

#ifdef USE_MALLOC
using BTree = BinaryTreeWithRawPtr;
#elif USE_BDWGC
using BTree = BinaryTreeBDWGC;
#else
using BTree = BinaryTree;
#endif

struct Worker {
  size_t iterations;
  size_t depth;
  std::future<size_t> check_val;
};

int main(int argc, char **argv) {
  int n = (argc > 1) ? atoi(argv[1]) : 4;
  if (n < 1) {
    perror("Can't work with negative depth");
    exit(1);
  }
#ifdef USE_BDWGC
  GC_INIT();
#endif

  size_t mindepth = 4;
  size_t maxdepth = mindepth + 2 > n ? mindepth + 2 : n;
  int stretchdepth = maxdepth + 1;

  {
    auto stretch = BTree::create(stretchdepth);
    printf("stretch tree of depth %u\t check: %li\n", stretchdepth,
           stretch->check());
  }
  std::vector<Worker> workers;

  auto long_lived = BTree::create(maxdepth);
  for (size_t depth = mindepth; depth <= maxdepth; depth += 2) {
    size_t iterations = 1 << (maxdepth - depth + mindepth);
    Worker w{.iterations = iterations,
             .depth = depth,
             .check_val = std::async(std::launch::deferred, [=]() -> size_t {
               size_t check = 0;
               for (size_t i = 1; i <= iterations; i++) {
                 auto tree = BTree::create(depth);
                 check += tree->check();
               }
               return check;
             })};
    workers.push_back(std::move(w));
  }
  printf("---------------------------------------------------\n");
  for (auto &worker : workers) {
    auto check_val = worker.check_val.get();
    printf("%zu\t trees of depth %zu\t check: %zu\n", worker.iterations,
           worker.depth, check_val);
  }
  printf("long lived tree of depth %zu\t check: %zu\n", maxdepth,
         long_lived->check());

  printf("---------------------------------------------------\n");

#ifdef USE_BDWGC
  GC_prof_stats_s stats;
  GC_get_prof_stats(&stats, sizeof(stats));
  printf("Total no. of collections:%zu\n", stats.gc_no);
#else
  printf("Total no. of collections:%zu\n", Gc::tot_collections);
#endif
}
