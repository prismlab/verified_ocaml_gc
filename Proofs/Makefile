FSTAR=fstar.exe -d --timing --cache_checked_modules \
    --cache_dir cache.boot --hint_dir hints --use_hints --use_hint_hashes \
    --record_hints --quake 1/3

all: cache.boot/Spec.GC_infix_closure_ver3.fsti.checked

cache.boot/%.fsti.checked: %.fsti
	$(FSTAR) $^
