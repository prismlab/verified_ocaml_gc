CC?=gcc -g
CXX?=g++ -g
LINKDIR?=target/release
DISTDIR?=dist
# CARGO_FLAGS?=--features "no_expand_heap" --features "check_invariants"
CARGO_FLAGS?=--features "no_expand_heap"

rust-release:
	cargo build --release $(CARGO_FLAGS)
rust-debug:
	cargo build $(CARGO_FLAGS)
main: rust-release
	$(CC) $(C_FLAGS) -o main main.c -L $(LINKDIR) -l rust_allocator
binarytree_gc_verified_mark: rust-release
	$(CXX) -DUSE_VERIFIED_MARK  $(C_FLAGS) -o $@ binarytree.cpp -L $(DISTDIR) -l graph -L $(LINKDIR) -l rust_allocator
binarytree_gc_verified_mark_and_sweep: rust-release
	$(CXX) -DUSE_VERIFIED_MARK -DUSE_VERIFIED_SWEEP  $(C_FLAGS) -o $@ binarytree.cpp -L $(DISTDIR) -l graph -L $(LINKDIR) -l rust_allocator
binarytree_gc_unverified: rust-release
	$(CXX) $(C_FLAGS) -o $@ binarytree.cpp -L $(LINKDIR) -l rust_allocator
binarytree_explicit_free: rust-release
	$(CXX) -DUSE_DEALLOC $(C_FLAGS) -o $@ binarytree.cpp -L $(LINKDIR) -l rust_allocator
binarytree_explicit_free_with_glibc: rust-release
	$(CXX) -DUSE_MALLOC $(C_FLAGS) -o $@ binarytree.cpp -L $(LINKDIR) -l rust_allocator
binarytree_bdwgc: rust-release
	$(CXX) -DUSE_BDWGC $(C_FLAGS) -o $@ binarytree.cpp -L $(LINKDIR) -l rust_allocator -L $(BDWGC_DIR) -l gccpp -L $(BDWGC_DIR) -l gc

binary_tree: binarytree_gc_verified_mark_and_sweep binarytree_gc_verified_mark binarytree_gc_unverified binarytree_bdwgc

all: binary_tree

clean:
	cargo clean
	rm -rf crash main *~
