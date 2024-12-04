ifdef PROOF_RECOVERY 
PROOF_RECOVERY = --proof_recovery
endif

FSTAR=fstar.exe -d --timing --cache_checked_modules \
    --cache_dir cache.boot --hint_dir hints --use_hints --use_hint_hashes \
    --record_hints --quake 1/3 $(PROOF_RECOVERY)

SOURCE_FSTI = Spec.Graph3.fsti Spec.GC_infix_closure_ver3.fsti \
  						Impl.GC_closure_infix_ver3.fsti

SOURCE_FST = Spec.Graph3.fst DFS2.fst Spec.GC_infix_closure_ver3.fst \
						 Spec.Loops.fst C.Loops.fst Impl.GC_closure_infix_ver3.fst

CHECKED_LAX = $(addprefix cache.boot/,$(SOURCE_FSTI:.fsti=.fsti.checked.lax)) \
          		$(addprefix cache.boot/,$(SOURCE_FST:.fst=.fst.checked.lax))

CHECKED_FULL = $(addprefix cache.boot/,$(SOURCE_FSTI:.fsti=.fsti.checked)) \
          		$(addprefix cache.boot/,$(SOURCE_FST:.fst=.fst.checked))

all: checked_lax checked_full

warmup_lax:
	while [ ! -f cache.boot/DFS2.fst.checked.lax ]; do \
		$(FSTAR) --lax DFS2.fst; \
	done; \
	while [ ! -f cache.boot/Spec.Loops.fst.checked.lax ]; do \
		$(FSTAR) --lax Spec.Loops.fst; \
	done; \
	while [ ! -f cache.boot/C.Loops.fst.checked.lax ]; do \
		$(FSTAR) --lax C.Loops.fst; \
	done 

warmup_full:
	while [ ! -f cache.boot/Spec.Graph3.fsti.checked ]; do \
		$(FSTAR) Spec.Graph3.fsti; \
	done; \
	while [ ! -f cache.boot/DFS2.fst.checked ]; do \
		$(FSTAR) DFS2.fst; \
	done; \
	while [ ! -f cache.boot/Spec.Loops.fst.checked ]; do \
		$(FSTAR) Spec.Loops.fst; \
	done; \
	while [ ! -f cache.boot/C.Loops.fst.checked ]; do \
		$(FSTAR) C.Loops.fst; \
	done 

checked_lax: warmup_lax $(CHECKED_LAX) $(CHECKED_LAX)

checked_full: checked_lax warmup_full $(CHECKED_FULL)

cache.boot/%.fsti.checked: %.fsti
	$(FSTAR) $<

cache.boot/%.fst.checked: %.fst
	$(FSTAR) $<

cache.boot/%.fsti.checked.lax: %.fsti
	$(FSTAR) --lax $<

cache.boot/%.fst.checked.lax: %.fst
	$(FSTAR) --lax $<

clean: 
	rm -rf cache.boot
	rm -rf hints
