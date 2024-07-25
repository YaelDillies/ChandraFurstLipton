# Chandra-Furst-Lipton

[![.github/workflows/push.yml](https://github.com/YaelDillies/ChandraFurstLipton/actions/workflows/push.yml/badge.svg)](https://github.com/YaelDillies/ChandraFurstLipton/actions/workflows/push.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/YaelDillies/ChandraFurstLipton)

The purpose of this repository is to *digitise* some mathematical definitions, theorem statements
and theorem proofs. Digitisation, or formalisation, is a process where the source material,
typically a mathematical textbook or a pdf file or website or video, is transformed into definitions
in a target system consisting of a computer implementation of a logical theory (such as set theory
or type theory).

## The source

The definitions, theorems and proofs in this repository are taken from the now classic [multi-party protocols paper of Chandra-Furst Lipton](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/multiparty-vdw.pdf).

## The target

The formal system which we are using as a target is Lean 4, a theorem prover based on the Calculus of Inductive Constructions, a dependent type theory. Lean is a project being developed at AWS and Microsoft Research by Leonardo de Moura and his team.

## Content of this project

### Code organisation

The Lean code is contained in the directory `src/`. The subdirectories are:
* `Mathlib`: Material missing from existing Mathlib developments
* `Prereqs`: New developments to be integrated to Mathlib

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).
Alternatively, click on the button below to open a Gitpod workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/YaelDillies/ChandraFurstLipton)

In either case, run `lake exe cache get` and then `lake build` to build the project.

## Build the blueprint

See instructions at https://github.com/PatrickMassot/leanblueprint/.

## Acknowledgements

Our project builds on Mathlib. We must therefore thank its numerous contributors without whom this
project couldn't even have started.

Much of the project infrastructure has been adapted from
* [sphere eversion](https://leanprover-community.github.io/sphere-eversion/)
* [liquid tensor experiment](https://github.com/leanprover-community/liquid/)
* [unit fractions](https://github.com/b-mehta/unit-fractions/)

## Source reference

`[CFL]` : https://www.cs.umd.edu/~gasarch/BLOGPAPERS/multiparty-vdw.pdf

[CFL]: https://www.cs.umd.edu/~gasarch/BLOGPAPERS/multiparty-vdw.pdf
