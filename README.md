# This is the "Mathematical Components" book.
[![build](https://github.com/math-comp/mcb/actions/workflows/build.yml/badge.svg)](https://github.com/math-comp/mcb/actions/workflows/build.yml)

## This (forked) repository

The aim is to update the examples of <https://github.com/math-comp/mcb/coq> 
in <https://github.com/AlainLich/mcb/coq> in order to

- Be compatible with "The Coq Proof Assistant, version 8.20.1;  compiled with OCaml 4.14.2"
- Accomodate HB (Hierarchy Builder) in Chapters 7 and following.
- In practice, I am using the Platform version `CP.~8.20~2025.01`, running in a container on an Apple M2, and accessed via `VScoq` <https://github.com/rocq-prover/vsrocq>.
- The added directory [coq/exercises](./coq/exercises)  contains (possibly cleaned up) versions of the exercises done while preparing this. The updates in the original files are (intended) minimal, with details in the `exercise`s. The file names designate the starting point file in `coq`. Detailed notes in [coq/exercises/ExerciseNotes.md](coq/exercises/ExerciseNotes.md).
 
**Notes** 
  - I have found the HB changes quite disruptive, when (naively) trying to experiment with the 
tutorial. Therefore this is made available in case it might be of help. 

  - References found most useful in this exercise:
	1. "Tutorial: Hierarchy Builder", from <https://github.com/rocq-prover/platform-docs?tab=readme-ov-file>,
the tutorial <https://github.com/rocq-prover/platform-docs/blob/main/src/Tutorial_hierarchy_builder.v> by Quentin Vermande.

	1. "Hierarchy Builder: algebraic hierarchies made easy in Coq with Elpi", 
      by C. Cohen, K. Sakaguchi and E. Tassi, <https://inria.hal.science/hal-02478907>,
      including the examples and testing material from 
            <https://github.com/math-comp/hierarchy-builder.git>.

    1.  "How to declare MathComp instances": <https://github.com/math-comp/math-comp/wiki/How-to-declare-MathComp-instances>


# From original repository

## Building
To build the book using Nix, run
```ShellSession
# without flakes, check out the repo first
$ NIXPKGS_ALLOW_UNFREE=1 nix-build
# with flakes
$ NIXPKGS_ALLOW_UNFREE=1 nix build github:math-comp/mcb --impure
```

Alternatively you may fetch the latest artifact produced by the CI for
the master branch
[here](https://github.com/math-comp/mcb/actions?query=branch%3Amaster).

The `tex/` directory contains the sources.  TexLive 2014, 2021 is
known to work.

The `coq/` directory contains snippets corresponding to the chapters
of the book.

The `docs/` directory contains the website of the book.

The `artwork/` directory contains the graphics used in the book.

### Homepage

Link to the [homepage of the book](https://math-comp.github.io/mcb)

