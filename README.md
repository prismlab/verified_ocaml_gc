# Verified OCaml GC

This is an artifact submitted along with the paper "A Mechanically Verified Garbage Collector for OCaml". This document explains the installation of tools required for verifying and integrating the F\*/Low\* GC with the OCaml runtime and then running the benchmarks.

## Tools required

- Git
- [Opam](https://opam.ocaml.org/doc/Install.html) for F\*/Low\*
- [Rust toolchain](https://www.rust-lang.org/tools/install)
- [Hyperfine](https://github.com/sharkdp/hyperfine) for running benchmarks
- [difftastic](https://github.com/Wilfred/difftastic) to see diffs clearly
- Have a global installation of a stable version of
  [bdwgc](https://github.com/ivmai/bdwgc). Instructions available at:
  https://github.com/ivmai/bdwgc?tab=readme-ov-file#building-and-installing) .
  Global installation is required because we just link `bdwgc` to our runtime
  through `-lgc`, so it should be in the system path. (You'll see this in
  `ExtractedCodeIntegratedWithRuntime` directory, which is explained later below
  as well )


## Setup FStar

For `karamel`, **python2.7 installation is needed.**

``` sh
$ opam switch create fstar-fresh 4.14.0
$ eval $(opam env --switch=fstar-fresh)
$ opam pin add fstar --dev-repo
```

`karamel` requires GNU make. If you are on macOS, you can install it using
`brew`. The following steps are only for macOS. If you are on Linux, skip to the
`karamel` installation step.

```bash
$ brew install make
$ alias make=`gmake` # create an alias in the current shell
$ make --version # verify 
gmake: getcwd: No such file or directory
GNU Make 4.4.1
Built for aarch64-apple-darwin24.0.0
Copyright (C) 1988-2023 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.
```

Now install `karamel`:

```bash
$ opam pin add karamel --dev-repo
```

You can verify everything is set up correctly by using the following commands:

``` sh
$ fstar.exe --version
F* 2024.09.05~dev
platform=Linux_x86_64
compiler=OCaml 4.14.0
date=2024-10-24 17:40:26 -0700
commit=8b6fce63ca91b16386d8f76e82ea87a3c109a208
$ krml -version
KaRaMeL version: 87384b244a98a0c41a2e14c65b872d885af7c8df
```

**Both of them should give some valid output(like above but won't necessarily be
exactly the same)**


## Editor Setup

- Setup Visual studio code setup for development and type checking
https://github.com/FStarLang/fstar-vscode-assistant
- (Alternative) Use [fstar-mode.el](https://github.com/FStarLang/fstar-mode.el) if you prefer Emacs

# Artifacts Directory Structure

## Proofs

- This directory contains all the proof files(.fst and .fsti files). They can be readily checked in VS
  Code/Emacs(once you've followed the setup instructions).
  
### Specification Files
- **Spec.GC_infix_closure_ver3.fsti** - Bridge GC spec between graph world and low level GC code world.
- **Spec.GC_infix_closure_ver3.fst** - Corresponding implementation file.
- **Spec.Graph3.fsti** - Graph interface
- **Spec.Graph3.fst** - Graph implementation
- **DFS.fst** - Depth First Search.

### Implementation File
- **Impl.GC_infix_closure_ver3.fsti** - Low level GC code interface.
- **Impl.GC_infix_closure_ver3.fst** - Low level GC code implementation.

### How to typecheck?

- In your editor of choice(Emacs or VSCode), open the
  **Impl.GC_infix_closure_ver3.fst** file and put the cursor at the end of the
  file. Then, press `Ctrl .` in VSCode or `Ctrl-c Ctrl-Ret` in Emacs. This will
  typecheck all the files involved because this is the extractable Low\* file
  and will need all other proofs to typecheck.

### Features in the version

This version has the following features and verified properties.
1. A stop the world mark and sweep GC.
2. Object header has the same layout as in OCaml
3. Varying field length.
4. Same tri-color abstraction as in OCaml
5. Field values can be pointers as well as integers.
6. Support for closure objects, infix objects and no scan objects.
7. DFS-Mark equivalence is proved.
8. All reachable and only the reachable objects after the mark are black in colour.
9. After mark, there are no grey objects remaining in the heap, thus proving the absence of any dangling pointers.
10. If started with a well-formed heap, that is a heap where all allocated objects point to allocated objects only heap, the mark is guaranteed to produce a well-formed heap as the result.
11. The allocated object graph formed before and after the mark are the same.
12. After mark finishes, all the successors of a black object in the final heap are black in color
13. After sweep, only white and blue objects remain.
14. After sweep, all the allocated and only the allocated objects are white in color in the final heap.
15. After sweep , all black objects and only the black objects before the sweep are white in color after the sweep.
16. After sweep , all white or blue objects and only the white or blue objects before the sweep are blue in color after the sweep.
17. After sweep, all the allocated objects in the final heap, have their field reads preserved with respect to the original heap.
18. After sweep, all the allocated objects in the final heap, have their wosize and tag in header preserved with respect to the original heap.
19. After sweep, all the allocated objects are subset of the allocated objects in the original heap.
20. The mark and sweep are efficient procedures due to the use of colour bits to distinguish the traversal state of an object.
21. The low level code is proven to have memory safety properties such as no buffer overflow, no dangling pointers, live memory usage, and spec equivalence.

From, 12 and 15, 
After sweep finishes, all the successors of a white object in the final heap are white in color.

From, 13 and 14,

After sweep finishes, all the successors of a white object in the final heap are members of the allocated object set.

This proves the well-formedness criteria for the sweep.

**TODO:** Need to update after sweep reachability is proved.


## ExtractableVerifiedCode

- This directory contains everything that the `Proofs` contains but in a
  slightly different structure, suitable for extraction. You can verify that
  they are indeed the same by running the script(which diffs these files) that we have included.
  ```sh
  $ ./diff-proofs-and-extractable-verified-code.sh
  ```
  
### Extraction Instructions

- cd inside the directory using `cd ExtractableVerifiedCode`.
- Make sure you are still in the same opam switch we created at the started `fstar-fresh`.
- Run the following command (with appropriate substitution for `<fstar-version>` and `<karamel-version>`):

```sh
$ FSTAR_HOME=$(opam var prefix)/.opam-switch/build/fstar.<fstar-version>/ KRML_HOME=$(opam var prefix)/.opam-switch/build/karamel.<karamel-version>/ SOURCE_DIR=$(pwd)  OTHERFLAGS="--admit_smt_queries true" make all
```

In the above command, replace `<fstar-version>` by the version you see when you
run `opam info fstar` (which happens to be `2024.09.05~dev` for me at the time
of writing). Similarly, replace `<karamel-version>` with the version value from
`opam info karamel`(which happens to be `1.0.0` for me at the time of writing).


- To clean the directory:

``` sh
$ FSTAR_HOME=$(opam var prefix)/.opam-switch/build/fstar.<fstar-version>/ KRML_HOME=$(opam var prefix)/.opam-switch/build/karamel.<karamel-version>/ SOURCE_DIR=$(pwd) make clean
```


> NOTE: We use "--admit_smt_queries true" in order to cut down on extraction
> time(which would be a lot without it). Since, the files are same and
> you can verify that they typecheck in `Proofs` directory, it is not
> problematic to use the flag.


## ExtractedCodeIntegratedWithRuntime

### Directories and Files

* `ocaml-4.14-unchanged` -- The unchanged OCaml 4.14 compiler. Used for
    compiling OCaml programs.
* `ocaml-4.14-hacked-gc` -- The hacked OCaml 4.14 compiler. This contains the
    modified `ocamlrun` used to run the modified GC(the verified one)
* `ocaml-4.14-bdwgc` --  Hacked Ocaml 4.14 runtime that uses Boehm GC
* `tests` -- contains some test, the directory has a bunch of Makefiles and README that should help with running the tests.
* `original-runtime-changes-for-bdwgc-integration.diff` : This has the diff for the changes in OCaml runtime needed to integrate `BDWGC`.
* `original-runtime-changes-for-verified-gc-integration.diff` : This has the
  diff for the changes in OCaml runtime needed to integrate `verified-gc`. NOTE:
  This was done on top of the `BDWGC` changes, so has some code changes leaking
  in, and we have added changes in a whole new directory inside the `runtime`
  called `verified_gc`, which has other code(verified + patch code) and we talk
  more about them in this README.

### Build

```bash
$ cd ExtractedCodeIntegratedWithRuntime
#Build all the runtimes(unchanged, hacked-gc and bdwgc)
$ make all
```


### Navigating tests directory

> Many of these are taken from [sandmark](https://github.com/ocaml-bench/sandmark)

**NOTE**: You must have all the tools mentioned in [Prerequisites section](#prerequisites) and you should have completed all the steps given in [Build section](#build)

We have a bunch of targets set up in the `Makefile` in `tests` directory.

- **`bench` target** : Running `make bench` will build and run all some relevant examples with all three configuration(`verified-gc`, `bdwgc` and `unchanged OCaml GC`). 

- Targets of the format `<example>.bench` will also run the `<example>` with all three configuration.

- Targets of the format `<example>.csv` will run the `<example>` with all three configuration and some varying parameters and produce a csv with the same name, which has execution information.

- Target named `ydump` is present which is also from [sandmark](https://github.com/ocaml-bench/sandmark/tree/main/benchmarks/yojson).

### Misc Information

- The `allocator`'s source code is located at
  `ExtractedCodeIntegratedWithRuntime/ocaml-4.14-hacked-gc/runtime/verified_gc/allocator/`
  from the top-level.
- The `MIN_EXPANSION_WORDSIZE` variable is used to tweak the size of heap(which
  will be `MIN_EXPANSION_WORDSIZE * 8 bytes`) for the allocator. We operate solely with that much heap and we will 
  be OOM if we can't find any space(after a verified GC). This can be seen in
  the `Makefile` in `tests` directory.

### Generated Code to Integrated code mapping and seeing the differences

We needed to write some patches to integrate with the runtime. You can see the
modifications to the verified code by running the following script. The patched code is available at ``

``` sh
$ ./diff-extracted-code-and-integrated-code.sh
```

There are other files as well for the purpose of integration in `ExtractedCodeIntegratedWithRuntime/ocaml-4.14-hacked-gc/runtime/verified_gc` directory.

- **allocator/** : The code for the `allocator`.
- **alloc.c** : This has some handwritten code which is needed for interfacing
  the verified code, allocator code and the OCaml runtime. 
- **LowStar_Prims.c** : Handwritten code to define some arithmetic operations, which is generated by F\*. (We don't want to link krml libraries,
  so we do this. )
- **internal/alias.h** :  Has macros for KRML specific things. (Again, we don't want to have krml headers,
  so we do this. )
