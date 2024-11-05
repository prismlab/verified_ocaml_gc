# Verified OCaml GC

This is an artifact submitted along with the paper "A Mechanically Verified
Garbage Collector for OCaml". This document explains the installation of tools
required for verifying and integrating the F\*/Low\* GC with the OCaml runtime
and then running the benchmarks.

## Tools required

- Git
- [Opam](https://opam.ocaml.org/doc/Install.html) for F\*/Low\*
- [Rust toolchain](https://www.rust-lang.org/tools/install)
- [Hyperfine](https://github.com/sharkdp/hyperfine) for running benchmarks.
- [difftastic](https://github.com/Wilfred/difftastic) visualise the diffs better.
- Have a global installation of a stable version of
  [bdwgc](https://github.com/ivmai/bdwgc). Instructions available at:
  https://github.com/ivmai/bdwgc?tab=readme-ov-file#building-and-installing).
  Global installation is required because we only link `bdwgc` to our runtime
  through `-lgc`, so it should be in the system path. You'll see this in
  `ExtractedCodeIntegratedWithRuntime` directory, which is explained later below
  as well.

## Setup FStar

``` sh
$ opam switch create fstar-fresh 4.14.0
$ eval $(opam env --switch=fstar-fresh)
$ opam pin add fstar --dev-repo
```

For `karamel`, **python2.7 installation is needed.** `karamel` requires GNU
make. If you are on macOS, you can install it using `brew`. The following steps
are only for macOS. If you are on Linux, skip to the `karamel` installation
step.

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

**Both of them should give some valid output (like above but won't necessarily
be exactly the same)**


## Editor Setup

- Setup Visual studio code setup for development and type checking
https://github.com/FStarLang/fstar-vscode-assistant
- (Alternative) Use [fstar-mode.el](https://github.com/FStarLang/fstar-mode.el)
  if you prefer Emacs

# Artifacts Directory Structure

## Proofs

- This directory contains all the proof files (.fst and .fsti files). They can
  be readily checked in VS Code/Emacs.

### Specification Files
- **Spec.GC_infix_closure_ver3.fsti** - Bridge GC spec between graph world and low-level GC code.
- **Spec.GC_infix_closure_ver3.fst** - Corresponding implementation file.
- **Spec.Graph3.fsti** - Graph interface.
- **Spec.Graph3.fst** - Graph implementation.
- **DFS.fst** - Depth First Search.

### Implementation File
- **Impl.GC_infix_closure_ver3.fsti** - Low-level GC code interface.
- **Impl.GC_infix_closure_ver3.fst** - Low-level GC code implementation.

### How to typecheck?

- In your editor of choice (Emacs or VSCode), open the
  **Impl.GC_infix_closure_ver3.fst** file. Place the cursor at the end of the
  file. Then, press `Ctrl .` in VSCode or `Ctrl-c Ctrl-Ret` in Emacs. This will
  typecheck all the files involved because this is the extractable Low\* file
  and will need all other proofs to typecheck.

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
- Run the following command (with appropriate substitution for `<fstar-version>`
  and `<karamel-version>`):

```sh
$ FSTAR_HOME=$(opam var prefix)/.opam-switch/build/fstar.<fstar-version>/ \
  KRML_HOME=$(opam var prefix)/.opam-switch/build/karamel.<karamel-version>/ \ 
  SOURCE_DIR=$(pwd)  OTHERFLAGS="--admit_smt_queries true" make all
```

In the above command, replace `<fstar-version>` by the version you see when you
run `opam info fstar` (which happens to be `2024.09.05~dev` for me at the time
of writing). Similarly, replace `<karamel-version>` with the version value from
`opam info karamel`(which happens to be `1.0.0` for me at the time of writing).


To clean the directory:

``` sh
$ FSTAR_HOME=$(opam var prefix)/.opam-switch/build/fstar.<fstar-version>/ \
  KRML_HOME=$(opam var prefix)/.opam-switch/build/karamel.<karamel-version>/ 
  SOURCE_DIR=$(pwd) make clean
```


> NOTE: We use "--admit_smt_queries true" in order to cut down on extraction
> time (which would be a lot without it). Since, the files are same and
> you can verify that they typecheck in `Proofs` directory.

## ExtractedCodeIntegratedWithRuntime

### Directories and Files

* `ocaml-4.14-unchanged` -- The unchanged OCaml 4.14 compiler. Used for
  compiling OCaml programs.
* `ocaml-4.14-veried-gc` -- The OCaml 4.14 compiler with the verified GC. This
  contains the modified `ocamlrun` used to run the verified GC.
* `ocaml-4.14-bdwgc` --  The OCaml 4.14 runtime that uses Boehm GC.
* `tests` -- contains some test, the directory has a bunch of Makefiles and
  README that should help with running the tests.
* `original-runtime-changes-for-bdwgc-integration.diff` -- This has the diff for
  the changes in OCaml runtime needed to integrate `BDWGC`.
* `original-runtime-changes-for-verified-gc-integration.diff` -- This has the
  diff for the changes in OCaml runtime needed to integrate `verified-gc`.
  NOTE: This was done on top of the `BDWGC` changes, so has some code changes
  leaking in, and we have added changes in a whole new directory inside the
  `runtime` called `verified_gc`, which has other code(verified + patch code)
  and we talk more about them in this README.

### Build

```bash
$ cd ExtractedCodeIntegratedWithRuntime
$ make all #Build all the runtimes (unchanged, veried-gc and bdwgc)
```
### Navigating tests directory

> Many of these are taken from [sandmark](https://github.com/ocaml-bench/sandmark)

You must have all the tools mentioned in [Prerequisites section](#prerequisites)
and you should have completed all the steps given in [Build section](#build).

We have a bunch of make targets set up in the `Makefile` in `tests` directory.

- **`bench` target** : Running `make bench` will build and run all some relevant
  examples with all three configuration (`verified-gc`, `bdwgc` and `unchanged
  OCaml GC`).
- Targets of the format `<example>.bench` will also run the `<example>` with all
  three configuration.
- Targets of the format `<example>.csv` will run the `<example>` with all three
  configuration and some varying parameters and produce a csv with the same
  name, which has execution information.
- Target named `ydump` is present which is also from
  [sandmark](https://github.com/ocaml-bench/sandmark/tree/main/benchmarks/yojson).

### Misc Information

- The `allocator`'s source code is located at
  `ExtractedCodeIntegratedWithRuntime/ocaml-4.14-hacked-gc/runtime/verified_gc/allocator/`
  from the top-level.
- The `MIN_EXPANSION_WORDSIZE` variable is used to tweak the size of heap(which
  will be `MIN_EXPANSION_WORDSIZE * 8 bytes`) for the allocator. We operate
  solely with that much heap and we will be OOM if we can't find any space(after
  a verified GC). This can be seen in the `Makefile` in `tests` directory.

### Generated Code to Integrated code mapping and seeing the differences

We needed to write some patches to integrate with the runtime. You can see the
modifications to the verified code by running the following script. The patched
code is available at ``

``` sh
$ ./diff-extracted-code-and-integrated-code.sh
```

There are other files as well for the purpose of integration in
`ExtractedCodeIntegratedWithRuntime/ocaml-4.14-hacked-gc/runtime/verified_gc`
directory.

- **allocator/** : The code for the `allocator`.
- **alloc.c** : This has some handwritten code which is needed for interfacing
  the verified code, allocator code and the OCaml runtime. 
- **LowStar_Prims.c** : Handwritten code to define some arithmetic operations,
  which is generated by F\*. (We don't want to link krml libraries, so we do
  this.)
- **internal/alias.h** :  Has macros for KRML specific things. (Again, we don't
  want to have krml headers, so we do this.)
