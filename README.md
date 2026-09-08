# DILLref

A Rocq development of a two-zone linear λ-calculus with an additive pair,
the `!` modality, iteration over natural numbers and linear references
(`new`, `swap`, `free`), with a linear/affine switch on the resource zone.
It centers on three executable
algorithms: a type checker with leftover contexts, a small-step evaluator
with a store and proved resource safety, and Girard's translation from the
simply typed λ-calculus. Everything is extracted to a single OCaml tool.

## Status

The project builds end to end: types, named source syntax and its resolution
to the de Bruijn core, scope and typing judgments, context and mask laws,
typed renaming and substitution,
type uniqueness, typed store balance and ownership acyclicity, proofs for
the bundled source and store examples, an executable source type checker with
leftover masks, extraction and an OCaml driver that checks the source catalog.
The checker is proved sound, complete and stable under framing. The evaluator
and the translation are not implemented yet.

| Component | Status |
|---|---|
| types and core AST with independent resource/shared indices | formalized |
| natural literals, `Succ`, linear `Iter`; derived addition | syntax and source typing defined; evaluation planned |
| `Split` with unit, commutativity, associativity, permutation transport and keyed correspondence | formalized |
| availability masks as OPEs: equality, positional consumption, `select`, positioned `view`, identity, composition, `ope_index`, category laws | formalized |
| zero/singleton masks, inclusion, intersection, relative remainder and `SplitM` laws | formalized |
| `Split` as complementary masks; pointwise `SplitM` as `Split` on positioned views | formalized |
| lexical scope and source typing with the linear/affine flag and availability masks | formalized |
| typing implies valid mask length, lexical scope and absence of addresses; linear-to-affine inclusion | proved |
| type uniqueness at fixed scopes, allowing different masks and modes | proved |
| two-zone renaming and substitution preserve scoping; typed substitution in both modes | proved |
| shared weakening/contraction, resource scope extension and adjacent resource exchange | proved |
| 37 source examples as core AST | classification, lexical scoping and exact checker results proved for the entire catalog; evaluation planned |
| type inference `infer` with leftover masks | implemented and extracted with regression checks; soundness, mode-sensitive completeness and framing proved |
| `check_open` and `check_program` for open terms and closed programs | proved sound and complete: linear mode requires every available resource to be consumed |
| finite stores, runtime typing, typed resource balance and ownership acyclicity | formalized; primitive root swap preserves acyclicity |
| cyclic store, ownership chains, strong update and invalid ownership examples | configuration proofs and rejection proofs in Rocq |
| `step`, `runFuel`, preservation, progress, acyclicity of all steps, `no_leak` | planned |
| `girard`, `girard_typing`, `girard_simulation` | planned |
| named source AST, lexical shadowing across zones and name resolution | implemented and extracted; declarative resolution correspondence and scope safety proved; 19 resolution checks |
| text parser and detailed name diagnostics | not implemented; named inputs use AST constructors |
| OCaml tool `dillref` with `check`, `run`, `girard` and `--affine` | `check [--affine] NAME` over the bundled catalog via the proved `check_program`; `run` and `girard` planned |

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
make check    # compile proofs and check extraction + OCaml
make clean    # remove build artifacts
```

The tool commands can be overridden: `make ROCQ=rocq OCAMLC=ocamlc`.
`_CoqProject` defines the `DILLref` namespace. Example import:

```coq
From DILLref Require Import Ty Syntax Mask OPE Split.
```

`make demo` prints the bundled example programs in core notation, where `x0`
is the innermost resource binder and `u0` the innermost shared binder. It runs
the extracted checker on all 37 programs in both modes and on 19 open or
malformed edge cases, comparing exact types and leftovers with independently
specified results. Five additional checks exercise renaming and substitution
under binders and preservation of runtime addresses. Three store-update checks,
two address-traversal checks and nineteen name-resolution checks also run after
extraction.
Configuration typing and acyclicity are propositions
proved in Rocq; the driver does not decide them or run an evaluator.

The built tool also accepts subcommands:

```sh
./_build/dillref list                       # bundled programs in core notation
./_build/dillref check counter tensor_fst   # closed programs, linear mode
./_build/dillref check --affine tensor_fst  # affine mode
```

`check` uses `check_program`: a closed program is accepted only if its type
checks and, in linear mode, no available resource is left unused. A rejected
program prints `rejected` and makes the exit code nonzero.

## Project structure

| Path | Purpose |
|---|---|
| `theories/Ty.v` | Types and decidable equality |
| `theories/Syntax.v` | Linear/affine flag, core AST, binding conventions, `loc_free`, values and address occurrences |
| `theories/Index.v` | Index maps, lifting, scope bounds and preservation of entries in polymorphic lists |
| `theories/Mask.v` | `mask := list bool`, decidable equality, positional consumption, inclusion, intersection, remainder and `SplitM` laws |
| `theories/OPE.v` | Masks as order-preserving embeddings: `select`, `view`, `ope_index` and composition laws |
| `theories/Split.v` | Order-preserving context splitting, permutation transport, keyed correspondence and mask bridges |
| `theories/Scoping.v` | Lexical scope bounds for the two independent variable zones |
| `theories/NamedSyntax.v` | Named source AST, binder zones and lexical scope representation |
| `theories/Resolve.v` | Name lookup and resolution, declarative correspondence, scope safety and absence of addresses |
| `theories/Typing.v` | Declarative source typing, general affine weakening, generation, invariants and type uniqueness |
| `theories/Infer.v` | Executable type inference with leftover resource masks, `check_open` and `check_program` |
| `theories/Renaming.v` | Two-zone renaming, identity/composition, scoping, typed scope extension and shared contraction |
| `theories/Substitution.v` | Simultaneous substitution, typed environments, substitution theorems and adjacent resource exchange |
| `theories/Graph.v` | Positive paths, acyclicity, decreasing ranks and edge updates over arbitrary vertex types |
| `theories/NatMap.v` | `NatMap A := list (nat * A)`, domain, lookup, replacement and key uniqueness laws |
| `theories/NatMapMask.v` | Keys selected by positional masks, monotonicity, domain membership and disjointness under unique keys |
| `theories/Store.v` | Stores and signatures as `NatMap term` and `NatMap ty`, reference edges and acyclicity under cell replacement |
| `theories/StoreTyping.v` | Term typing with address resources, source embedding, typed cells, global balance, configuration invariant and root swap acyclicity |
| `theories/Examples.v` | Source classification, named programs and resolution checks, context permutations, store configurations and rejection proofs |
| `theories/ExtractDILLref.v` | Extraction, compiled by `make extract` |
| `ocaml/main.ml` | Driver for the extracted code |
| `docs/roadmap.md` | Milestone tracking |
| `docs/examples.md` | Typing coverage and manual expected values and store traces |
| `docs/store-invariant.md` | Runtime resource balance, cyclic counterexample and the strong-update argument |
| `lecture/README.md` | Lecture outline |

`ExtractDILLref.v` is not listed in `_CoqProject` so that the library build
never depends on generated OCaml files. Edit the `.v` files and
`ocaml/main.ml`; `ocaml/generated/` is regenerated automatically and the build
fails if extraction introduces `Obj.magic`.

## Design notes

Both zones use the same types. Resource hypotheses are consumed exactly once
in linear mode and at most once in affine mode; shared hypotheses may be copied
and dropped. Application, tensor pairs, `Iter`, `swap` and the `let` forms divide
the resource zone with `Split`; the additive pair `⟨e₁, e₂⟩` and the branches
of `if` share it. `!e` needs an empty resource zone and evaluates as a thunk
that is re-run at each use.

Typing is synthesis, not checking: binders are annotated and there is no
polymorphism or subtyping, so every term has at most one type and `infer`
computes it in one structural pass, with the leftover mask as its second
output. The type comparisons it performs are equalities between synthesized
types. A bidirectional algorithm with a checking mode is only needed once
binder annotations are dropped (Pierce, *Types and Programming Languages*,
§9.3 and §10.2; Dunfield and Krishnaswami, *Bidirectional Typing*, ACM
Computing Surveys 54(5), 2021, §1).

Natural numbers have literals `Nat n`, strict successor `Succ e`, and the
fully applied iterator `Iter count step seed`. For each accumulator type `A`,
its argument types are `nat`, `!(A ⊸ A)` and `A`, and its result type is `A`.
The resource context is split among all three arguments. The intended CBV
semantics evaluates them in that order, including the seed at count zero.
The boxed step's body is evaluated afresh on each iteration; at zero it is
not evaluated. An accumulator can own a reference and pass it to the next
iteration. The step thunk cannot capture an external resource under promotion.

Addition is the ordinary program
`λm:nat. λn:nat. iter n !(λr:nat. succ r) m`, used by the counter example.
Curried application preserves left-to-right evaluation of its two arguments.
The bundled iterator examples cover zero iterations, a reference accumulator,
effects in the step thunk, an unboxed step, mismatched step/seed types, resource
capture, duplicated use and affine dropping of the accumulator. Every bundled
source program has a proved classification in both modes. The catalog includes
the modal maps, counter, references inside closures and cells, lazy sharing,
branch leftovers and local weakening. [Example coverage](docs/examples.md)
records the proofs and manual expected execution traces. Operational semantics
remains pending; general recursion and a normalization theorem are outside the
scope of this project.

`scoped g l e` checks only lexical bounds, so runtime addresses are admitted by
that judgment. Source typing has no address rule and implies `loc_free e = true`.
The mask length is also a consequence of typing. `TyWeak` admits larger masks
at any node in affine mode; promotion's body still uses a zero mask.
`Infer.v` implements the separate executable inference with leftovers; its
soundness theorem reconstructs a declarative demand and split from every
successful check. Completeness returns the exact declarative remainder in
linear mode and a supermask of it in affine mode, while every result remains a
submask of the input. Framing proves that resources outside the checker's
actual demand pass through unchanged.

`typing_generation` exposes the last syntax-directed rule through any outer
affine weakening. `typing_unique` proves that a fixed term in fixed shared and
resource scopes has at most one type, even across different masks and modes.

The core uses de Bruijn indices with separate scopes for the two zones. A
consumed resource keeps its position; a separate availability mask records
consumption so that the remaining indices keep their meaning. A mask is an
order-preserving embedding of the available sub-scope into the full scope,
with the same `drop`/`keep` shape as the OPEs of the System T normalizer, and
two complementary masks are exactly a `Split`. `Loc` is a runtime-only
constructor and is rejected in source programs.

The named AST has a single `NVar name` constructor. `NLam` and `NLetPair`
introduce resource binders; `NLetBang` introduces a shared binder. The nearest
binder with that name wins, including across zones. Each zone has its own
index count. In `NLetPair x y`, `y` is innermost; if the names coincide it
shadows `x`. Pattern names scope over the body only.

`resolve E e` takes a lexical stack of names with zone tags and returns
`Some core` or `None` for an unbound name. It traverses suspended bodies and
all iterator arguments, even at count zero. It does not consult types or
availability: consuming a resource cannot expose an older shadowed binding.
The input is a named AST; a text parser and detailed error diagnostics are
not yet provided.

`resolve_iff` proves equivalence with the independent `resolves` relation;
`resolve_source` proves valid scope bounds and absence of `Loc` in every
successful result. A named program is typable when resolution succeeds and
the resulting core satisfies `has_type` in the chosen mode and contexts.
Typing rules are defined once, for the core. The named examples connect
successful resolution to the existing typing and rejection proofs.

`Mask.v` defines the transparent alias `mask := list bool` and the mask
operations and laws, including `SplitM`, using only Stdlib. Source typing
depends on this library directly; embedding and list-splitting correspondences
live in `OPE.v` and `Split.v`.

`split_permutation_transport` moves an ordered split through a permutation
of its whole list, producing permutations of the two parts. Repeated entries
are allowed. `split_permutation_iff` gives the converse of `split_permutation`
up to order within the parts. `split_keyed_permutation_iff` additionally
transports uniqueness of a chosen key projection; uniqueness concerns keys,
not complete bindings or their types.

For named contexts represented as identifier/payload pairs, the key projection
is `fst`. The keyed theorem characterizes permutation-based division with
unique identifiers as an ordered split into reordered parts. Resolving names
to de Bruijn positions and typing under arbitrary resource permutations are
separate statements. The existing typing exchange theorem handles the adjacent
case and renames the term.

Mask constructors take a scope size: `mask_id n`, `mask_zero n` and
`mask_single n i` produce masks of length `n`; `mask_wk n` adds an unavailable
position before `n` available ones. Typing rules supply `length L` explicitly.

`mask_count U` counts available positions. The composition laws in `Mask.v`
use lengths and counts: the left identity has size `length U`, the right
identity has size `mask_count U`, and associativity assumes
`length V = mask_count U`. `ope_count` connects the count to the embedded
scope's length; `ope_comp_id_l`, `ope_comp_id_r` and `ope_comp_assoc` specialize
these laws to embedding derivations.

`Index.v` provides index maps and their lifting independently of term syntax.
Its `ren_context` relation preserves entries of arbitrary `list A` contexts;
it permits distinct positions carrying equal entries to have the same image.
The syntax traversals and their typing theorems use these shared definitions.

`rename ru rl` and `subst su sl` traverse both zones independently and leave
`Loc` unchanged. Under a binder, substitution shifts free indices in both
sets of images, then adds an identity image for the bound zone. `LetPair`
lifts twice; `LetBang` binds only a shared variable.

`typing_subst` requires resource-free images for shared variables and a
`linear_env` that partitions the target resources among available source
variables using `SplitM`. This includes affine derivations with weakening
at any node. `typing_subst_l` consumes a resource binder with an explicit
split between the argument and the remaining body; `typing_subst_u` allows
a resource-free term to replace a shared binder. These are source typing
theorems; runtime preservation with store addresses remains to be developed.

Typed scope extension uses OPEs and inserts unavailable resource positions
in either mode. Adding available but unused resources uses `TyWeak` and is
restricted to affine mode. Shared renaming permits contraction; adjacent
resource exchange permutes the scope, mask and term together.

`NatMap.v` provides association lists with natural-number keys and polymorphic
operations `natmap_domain`, `natmap_lookup` and `natmap_replace`. Lookup returns
the first matching entry; replacement updates all matching entries and preserves
keys and order. `Store.v` specializes this representation to terms and types.
Unique keys are a separate store-balance requirement.

`NatMapMask.v` relates the two libraries through `masked_key m U k`: key `k`
occurs at a position selected by `U`. The definition and its monotonicity and
domain lemmas are polymorphic in the payload. Disjoint masks imply disjoint
selected keys when `natmap_domain m` has no duplicates. Runtime typing and
store balance use this relation at `m : NatMap ty`.

References are exclusive rights to a cell: `swap` performs a strong update and
returns the old contents together with the rebound reference, and `free`
accepts only `ref unit`. `runtime_type f S G L U R e A` adds an address mask
`R` over the store signature `S`, independently of the lexical mask `U`.
`Loc l` uses an address key; binders never shift it. `store_balance` partitions
the signature's rights among the term, all stored values and an affine
residual. `configuration_typed` additionally requires ownership acyclicity.
Edges include addresses in closures and lazy components. `StoreTyping.v`
develops these judgments in order: terms with addresses, cell typing and
resource balance, then typed configurations. They are propositions erased
by extraction.

`Graph.v` defines the transparent alias `Graph V := V -> V -> Prop` and
develops paths and acyclicity for an arbitrary edge relation.
`Store.v` defines `store_edge` and `store_acyclic` and relates cell
replacement to graph updates. These definitions apply to arbitrary stores;
runtime typing and the balance lemmas in `StoreTyping.v` establish their
exclusive-ownership interpretation.

The cyclic closure example proves that even linear balance alone admits a
self-owned cell. `balanced_swap_acyclic` proves graph preservation for a
primitive swap at the root, using disjoint ownership of the target address.
Strong update is illustrated with a cell whose type changes from `nat` to
`unit`. [The invariant and proof boundaries](docs/store-invariant.md) describe
the remaining runtime substitution, signature transport and operational
preservation obligations.

The planned safety results for typed programs started
from the empty store are absence of dangling references and double frees in
both modes, and an empty final store for closed programs of type `nat` in
linear mode. The last result relies on an ownership-acyclicity invariant in
addition to the resource balance.

Rocq verification and trust in the extraction and OCaml toolchain remain
separate assurance boundaries.
