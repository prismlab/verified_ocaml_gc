ifdef PROOF_RECOVERY 
PROOF_RECOVERY = --proof_recovery
endif

FSTAR=fstar.exe -d --timing --cache_checked_modules \
    --cache_dir cache.boot --hint_dir hints --use_hints --use_hint_hashes \
    --record_hints --ext context_pruning --quake 1/3 $(PROOF_RECOVERY)

SOURCE_FSTI = Spec.Graph3.fsti Spec.GC_part01.fsti \
	Spec.GC_part02_01.fsti Spec.GC_part02_02.fsti \
  Spec.GC_part03.fsti Spec.GC_part04.fsti Spec.GC_part05.fsti \
  Spec.GC_part06.fsti Spec.GC_part07.fsti Spec.GC_part08.fsti \
  Spec.GC_part09.fsti Spec.GC_part10.fsti Spec.GC_part11.fsti \
  Spec.GC_part12.fsti Spec.GC_part13.fsti Spec.GC_part14.fsti \
  Spec.GC_part15.fsti Spec.GC_infix_closure_ver3.fsti
  

SOURCE_FST = Spec.Graph3.fst DFS2.fst Spec.GC_part01.fst Spec.GC_part02_01.fst \
						 Spec.GC_part02_02.fst #Spec.GC_infix_closure_ver3.fst

CHECKED_LAX = $(addprefix cache.boot/,$(SOURCE_FSTI:.fsti=.fsti.checked.lax)) \
          		$(addprefix cache.boot/,$(SOURCE_FST:.fst=.fst.checked.lax))

CHECKED_FULL = $(addprefix cache.boot/,$(SOURCE_FSTI:.fsti=.fsti.checked)) \
          		$(addprefix cache.boot/,$(SOURCE_FST:.fst=.fst.checked))

all: checked_lax checked_full

warmup_lax:
	while [ ! -f cache.boot/DFS2.fst.checked.lax ]; do \
		$(FSTAR) --lax DFS2.fst; \
	done

warmup_full:
	while [ ! -f cache.boot/Spec.Graph3.fsti.checked ]; do \
		$(FSTAR) Spec.Graph3.fsti; \
	done; \
	while [ ! -f cache.boot/DFS2.fst.checked ]; do \
		$(FSTAR) DFS2.fst; \
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
