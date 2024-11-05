TYPE=release
all: libvergc.a librust_allocator.a

%.o: %.c
	$(CC) $(CFLAGS) -g -O2 -c $< -o $@

libvergc.a: LowStar_Prims.o Spec.o alloc.o Impl_GC_closure_infix_ver3.o
	$(AR) rcs $@ $^

librust_allocator.a:
	$(MAKE) -C allocator rust-$(TYPE)
	cp allocator/target/$(TYPE)/librust_allocator.a .

clean:
	$(MAKE) -C allocator clean
	rm -f *.o *.a *~
