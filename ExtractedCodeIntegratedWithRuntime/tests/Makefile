%.byte: %.ml
	@echo "Building: " $@
	@../ocaml-4.14-unchanged/_install/bin/ocamlc -custom -cclib -L../ocaml-4.14-hacked-gc/runtime/verified_gc -cclib -lvergc -cclib -lrust_allocator -o $@ $<

benchmark: binarytrees.csv fasta.csv quicksort.csv fannkuchredux.csv count_change.csv

test: binarytrees.byte fasta.byte quicksort.byte fannkuchredux.byte count_change.byte
	@echo "Running binarytrees"
	MIN_EXPANSION_WORDSIZE=134217728 '../ocaml-4.14-hacked-gc/runtime/ocamlrun' binarytrees.byte 16
	@echo "Running fasta"
	MIN_EXPANSION_WORDSIZE=134217728 '../ocaml-4.14-hacked-gc/runtime/ocamlrun' fasta.byte 2_500_000
	@echo "Running quicksort"
	MIN_EXPANSION_WORDSIZE=8000000 '../ocaml-4.14-hacked-gc/runtime/ocamlrun' quicksort.byte 5_000_000
	@echo "Running fannkuchredux"
	'../ocaml-4.14-hacked-gc/runtime/ocamlrun' fannkuchredux.byte 11
	@echo "Running count_change"
	MIN_EXPANSION_WORDSIZE=20000000 ../ocaml-4.14-hacked-gc/runtime/ocamlrun ./count_change.byte 150
	@echo "Running nbodies"

count_change.csv: count_change.byte
	MIN_EXPANSION_WORDSIZE=20000000 hyperfine -P param 100 150 -D 10 --export-csv $@ '../ocaml-4.14-hacked-gc/runtime/ocamlrun $< {param}' '../ocaml-4.14-bdwgc/runtime/ocamlrun $< {param}' '../ocaml-4.14-unchanged/runtime/ocamlrun $< {param}'

binarytrees.csv: binarytrees.byte
	MIN_EXPANSION_WORDSIZE=134217728 hyperfine -P depth 11 16  --export-csv $@ '../ocaml-4.14-hacked-gc/runtime/ocamlrun $< {depth}' '../ocaml-4.14-bdwgc/runtime/ocamlrun $< {depth}' '../ocaml-4.14-unchanged/runtime/ocamlrun $< {depth}'

fasta.csv: fasta.byte
	MIN_EXPANSION_WORDSIZE=134217728 hyperfine -P param 5_00_000 2_500_000 -D 5_00_000 --export-csv $@ '../ocaml-4.14-hacked-gc/runtime/ocamlrun $< {param}' '../ocaml-4.14-bdwgc/runtime/ocamlrun $< {param}' '../ocaml-4.14-unchanged/runtime/ocamlrun $< {param}'

quicksort.csv: quicksort.byte
	MIN_EXPANSION_WORDSIZE=8000000 hyperfine -P param 1_000_000 5_000_000 -D 1_000_000 --export-csv $@ '../ocaml-4.14-hacked-gc/runtime/ocamlrun $< {param}' '../ocaml-4.14-bdwgc/runtime/ocamlrun $< {param}' '../ocaml-4.14-unchanged/runtime/ocamlrun $< {param}'

fannkuchredux.csv: fannkuchredux.byte
	hyperfine -P param 8 11 -D 1 --export-csv $@ '../ocaml-4.14-hacked-gc/runtime/ocamlrun $< {param}' '../ocaml-4.14-bdwgc/runtime/ocamlrun $< {param}' '../ocaml-4.14-unchanged/runtime/ocamlrun $< {param}'

HACKED_GC=../ocaml-4.14-hacked-gc/runtime/ocamlrun
BDWGC=../ocaml-4.14-bdwgc/runtime/ocamlrun
UNCHANGED=../ocaml-4.14-unchanged/runtime/ocamlrun

nbodies.bench: nbodies.byte
	hyperfine --export-csv $@.csv \
		'$(HACKED_GC) nbodies.byte 100000' \
		'$(BDWGC) nbodies.byte 100000' \
		'$(UNCHANGED) nbodies.byte 100000'

binarytrees.bench: binarytrees.byte
	MIN_EXPANSION_WORDSIZE=134217728 \
	hyperfine --export-csv $@.csv \
		'$(HACKED_GC) binarytrees.byte 16' \
		'$(BDWGC) binarytrees.byte 16' \
		'$(UNCHANGED) binarytrees.byte 16' \

knucleotide.bench: knucleotide.byte
	MIN_EXPANSION_WORDSIZE=5288608 \
	hyperfine --export-csv $@.csv \
		'$(HACKED_GC) knucleotide.byte' \
		'$(BDWGC) knucleotide.byte' \
		'$(UNCHANGED) knucleotide.byte'

spectralnorm.bench: spectralnorm.byte
	hyperfine --export-csv $@.csv \
		'$(HACKED_GC) spectralnorm.byte 1000' \
		'$(BDWGC) spectralnorm.byte 1000' \
		'$(UNCHANGED) spectralnorm.byte 1000'

mandelbrot.bench: mandelbrot.byte
	hyperfine --export-csv $@.csv \
		'$(HACKED_GC) mandelbrot.byte 1000' \
		'$(BDWGC) mandelbrot.byte 1000' \
		'$(UNCHANGED) mandelbrot.byte 1000'

fasta.bench: fasta.byte
	MIN_EXPANSION_WORDSIZE=$$((134217728 / 4)) \
	hyperfine --export-csv $@.csv \
		'$(HACKED_GC) fasta.byte 5_000_000' \
		'$(BDWGC) fasta.byte 5_000_000' \
		'$(UNCHANGED) fasta.byte 5_000_000' \

count_change.bench: count_change.byte
	MIN_EXPANSION_WORDSIZE=20000000 \
	hyperfine --export-csv $@.csv \
		'$(HACKED_GC) count_change.byte 200' \
		'$(BDWGC) count_change.byte 200' \
		'$(UNCHANGED) count_change.byte 200'

fannkuchredux.bench: fannkuchredux.byte
	hyperfine --export-csv $@.csv \
		'$(HACKED_GC) fannkuchredux.byte 10' \
		'$(BDWGC) fannkuchredux.byte 10' \
		'$(UNCHANGED) fannkuchredux.byte 10' \

quicksort.bench: quicksort.byte
	MIN_EXPANSION_WORDSIZE=8000000 \
	hyperfine --export-csv $@.csv \
		'$(HACKED_GC) quicksort.byte 2_500_000' \
		'$(BDWGC) quicksort.byte 2_500_000' \
		'$(UNCHANGED) quicksort.byte 2_500_000'

cpdf.bench: cpdf-unchanged cpdf-bdwgc cpdf-vergc
	MIN_EXPANSION_WORDSIZE=134217728 \
	hyperfine --export-csv $@.csv \
		'./cpdf-src/cpdf-vergc -blacktext metro_geo.pdf -o /dev/null' \
		'./cpdf-src/cpdf-bdwgc -blacktext metro_geo.pdf -o /dev/null' \
		'./cpdf-src/cpdf-unchanged -blacktext metro_geo.pdf -o /dev/null'

.PHONY: %.bench

bench: nbodies.bench binarytrees.bench fasta.bench count_change.bench fannkuchredux.bench quicksort.bench cpdf.bench

cpdf-src:
	git clone https://github.com/johnwhitington/cpdf-source $@
	cd $@; git checkout v2.6.2; opam install . --deps-only

cpdf-src-clean:
	rm -rf cpdf-src || true

cpdf-vergc: cpdf-src
	PWD=$(shell pwd)
	make -j -C $< clean
	BCSUFFIX='-vergc' ALL_LDFLAGS='-use-runtime $(PWD)/../ocaml-4.14-hacked-gc/runtime/ocamlrun' $(MAKE) -C $< bc
	@echo "Running cpdf with verified gc runtime"
	MIN_EXPANSION_WORDSIZE=134217728 cpdf-src/cpdf-vergc -merge $</*.pdf -o /dev/null

cpdf-bdwgc: cpdf-src
	PWD=$(shell pwd)
	make -j -C $< clean
	BCSUFFIX='-bdwgc' ALL_LDFLAGS='-use-runtime $(PWD)/../ocaml-4.14-bdwgc/runtime/ocamlrun' $(MAKE) -C $< bc
	@echo "Running cpdf with bdwgc gc runtime"
	MIN_EXPANSION_WORDSIZE=134217728 cpdf-src/cpdf-bdwgc -merge $</*.pdf -o /dev/null

cpdf-unchanged: cpdf-src
	PWD=$(shell pwd)
	make -j -C $< clean
	BCSUFFIX='-unchanged' ALL_LDFLAGS='-use-runtime $(PWD)/../ocaml-4.14-unchanged/runtime/ocamlrun' $(MAKE) -C $< bc
	@echo "Running cpdf with unchanged gc runtime"
	MIN_EXPANSION_WORDSIZE=134217728 cpdf-src/cpdf-unchanged -merge $</*.pdf -o /dev/null

ydump:
	PWD=$(shell pwd)
	cd yojson; opam install yojson camlp-streams; HACKED_GC_PATH=$(PWD)/../ocaml-4.14-hacked-gc/ dune build ydump.bc
	# triggers a few gc cycles too
	MIN_EXPANSION_WORDSIZE=8388608 $(HACKED_GC) yojson/_build/default/ydump.bc -c yojson/sample.json

clean-csvs:
	rm *.csv || true

clean-ydump:
	cd yojson; dune clean

clean: clean-csvs cpdf-src-clean clean-ydump
	rm -f *.cmi *.cmo *.cmx *.o *.byte
