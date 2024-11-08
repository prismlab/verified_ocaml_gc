ifdef PROOF_RECOVERY 
PROOF_RECOVERY = --proof_recovery
endif

FSTAR=fstar.exe -d --timing --cache_checked_modules \
    --cache_dir cache.boot --hint_dir hints --use_hints --use_hint_hashes \
    --record_hints --quake 1/3 $(PROOF_RECOVERY)

all: cache.boot/Spec.Graph3.fsti.checked cache.boot/Spec.Graph3.fst.checked \
	cache.boot/DFS2.fst.checked cache.boot/Spec.GC_part01.fsti.checked \
	cache.boot/Spec.GC_part02.fsti.checked cache.boot/Spec.GC_part03.fsti.checked \
	cache.boot/Spec.GC_part04.fsti.checked cache.boot/Spec.GC_part05.fsti.checked \
	cache.boot/Spec.GC_part06.fsti.checked cache.boot/Spec.GC_part07.fsti.checked \
	cache.boot/Spec.GC_part08.fsti.checked cache.boot/Spec.GC_part09.fsti.checked \
	cache.boot/Spec.GC_part10.fsti.checked cache.boot/Spec.GC_part11.fsti.checked \
	cache.boot/Spec.GC_part12.fsti.checked cache.boot/Spec.GC_part13.fsti.checked \
	cache.boot/Spec.GC_part14.fsti.checked cache.boot/Spec.GC_part15.fsti.checked \
	cache.boot/Spec.GC_infix_closure_ver3.fsti.checked \
	cache.boot/Spec.GC_infix_closure_ver3.fst.checked

cache.boot/%.fsti.checked: %.fsti
	$(FSTAR) $<

cache.boot/%.fst.checked: %.fst
	$(FSTAR) $<

force-clean:
	rm -rf cache.boot
	rm -rf hints
