FSTAR=fstar.exe -d --timing --cache_checked_modules \
    --cache_dir cache.boot --hint_dir hints --use_hints --use_hint_hashes \
    --record_hints --quake 1/3

all: cache.boot/Spec.Graph3.fsti.checked cache.boot/Spec.Graph3.fst.checked \
	cache.boot/DFS2.fst.checked cache.boot/Spec.GC_part1.fsti.checked \
	cache.boot/Spec.GC_part2.fsti.checked cache.boot/Spec.GC_part3.fsti.checked \
	cache.boot/Spec.GC_part4.fsti.checked cache.boot/Spec.GC_part5.fsti.checked \
	cache.boot/Spec.GC_part6.fsti.checked cache.boot/Spec.GC_part7.fsti.checked \
	cache.boot/Spec.GC_part8.fsti.checked cache.boot/Spec.GC_part9.fsti.checked \
	cache.boot/Spec.GC_part10.fsti.checked cache.boot/Spec.GC_part11.fsti.checked \
	cache.boot/Spec.GC_part12.fsti.checked cache.boot/Spec.GC_part13.fsti.checked \
	cache.boot/Spec.GC_part14.fsti.checked cache.boot/Spec.GC_infix_closure_ver3.fsti.checked

cache.boot/%.fsti.checked: %.fsti
	$(FSTAR) $<

cache.boot/%.fst.checked: %.fst
	$(FSTAR) $<
