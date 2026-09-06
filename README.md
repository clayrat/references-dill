# DILLref

A Rocq development of a two-zone linear λ-calculus with an additive pair,
the `!` modality and linear references (`new`, `swap`, `free`), with a
linear/affine switch on the resource zone. It centers on three executable
algorithms: a type checker with leftover contexts, a small-step evaluator
with a store and proved resource safety, and Girard's translation from the
simply typed λ-calculus. Everything is extracted to a single OCaml tool.

## Status

The scaffold builds end to end: types, the de Bruijn core syntax, order-
preserving context splitting with its laws, example programs, extraction and
an OCaml driver that prints the examples. The judgments, the three algorithms
and their proofs are not implemented yet.

| Component | Status |
|---|---|
| types and core AST with independent resource/shared indices | formalized |
| `Split` with unit, commutativity, associativity and permutation lemmas | formalized |
| availability masks as OPEs: `select`, positioned `view`, identity, composition, `ren`, category laws | formalized |
| `Split` as complementary masks; pointwise `SplitU` as `Split` on positioned views | formalized |
| example programs as core AST | written, not yet typed or run |
| declarative typing with the linear/affine flag and availability masks | planned |
| checker `check` with `check_sound`, `check_complete`, `check_frame` | planned |
| store, `step`, `runFuel`, preservation, progress, ownership acyclicity, `no_leak` | planned |
| `girard`, `girard_typing`, `girard_simulation` | planned |
| named surface syntax and name resolution | planned |
| OCaml tool `dillref` with `check`, `run`, `girard` and `--affine` | driver prints examples only |

Unfinished results are marked as TODOs, without `Admitted`, axioms, or
checker stubs that report success.

## Building and running

Rocq with Stdlib, GNU Make, and an OCaml compiler must be available in
`PATH`. The initial setup uses Rocq 9.1.1 and OCaml 4.14.2. No external Rocq
libraries, Dune, or additional OCaml packages are required.

```sh
make          # compile Rocq modules and proved examples
make extract  # extract to ocaml/generated/dillref.ml and dillref.mli
make demo     # build and run the OCaml tool
make check    # run all available checks: Rocq + extraction + OCaml
make clean    # remove build artifacts
```

The tool commands can be overridden: `make ROCQ=rocq OCAMLC=ocamlc`.
`_CoqProject` defines the `DILLref` namespace. Example import:

```coq
From DILLref Require Import Ty Syntax OPE Split.
```

`make demo` currently prints the bundled example programs in core notation,
where `x0` is the innermost resource binder and `u0` the innermost shared
binder, and checks that none of them mentions a store address.

## Project structure

| Path | Purpose |
|---|---|
| `theories/Ty.v` | Types and decidable equality |
| `theories/Syntax.v` | Linear/affine flag, core AST, binding conventions, `loc_free` |
| `theories/OPE.v` | Availability masks as order-preserving embeddings: `select`, `view`, composition, `ren` |
| `theories/Split.v` | Order-preserving context splitting, `SplitU`, their laws and correspondence with masks |
| `theories/Examples.v` | Example programs |
| `theories/ExtractDILLref.v` | Extraction, compiled by `make extract` |
| `ocaml/main.ml` | Driver for the extracted code |
| `docs/roadmap.md` | Milestone tracking |
| `lecture/README.md` | Lecture outline |

`ExtractDILLref.v` is not listed in `_CoqProject` so that the library build
never depends on generated OCaml files. Edit the `.v` files and
`ocaml/main.ml`; `ocaml/generated/` is regenerated automatically and the build
fails if extraction introduces `Obj.magic`.

## Design notes

Both zones use the same types. Resource hypotheses are consumed exactly once
in linear mode and at most once in affine mode; shared hypotheses may be copied
and dropped. Application, tensor pairs, `+`, `swap` and the `let` forms divide
the resource zone with `Split`; the additive pair `⟨e₁, e₂⟩` and the branches
of `if` share it. `!e` needs an empty resource zone and evaluates as a thunk
that is re-run at each use.

The core uses de Bruijn indices with separate scopes for the two zones. A
consumed resource keeps its position; a separate availability mask records
consumption so that the remaining indices keep their meaning. A mask is an
order-preserving embedding of the available sub-scope into the full scope,
with the same `drop`/`keep` shape as the OPEs of the System T normalizer, and
two complementary masks are exactly a `Split`. `Loc` is a runtime-only
constructor and is rejected in source programs.

References are exclusive rights to a cell: `swap` performs a strong update and
returns the old contents together with the rebound reference, and `free`
accepts only `ref unit`. The planned safety results for typed programs started
from the empty store are absence of dangling references and double frees in
both modes, and an empty final store for closed programs of type `nat` in
linear mode. The last result relies on an ownership-acyclicity invariant in
addition to the resource balance.

Rocq verification and trust in the extraction and OCaml toolchain remain
separate assurance boundaries.
