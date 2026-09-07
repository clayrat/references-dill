# Example typing and expected execution

[Examples.v](../theories/Examples.v) contains the programs and their typing/rejection proofs.
`source_examples_classified` covers every entry of `source_examples`: a program
is accepted with the same type in both modes, accepted only affinely, or rejected
at every type in both modes. `source_examples_scoped` also proves that every
entry is closed and lexically well-scoped, including the negative cases.

The tables and traces below are a manual account of the intended semantics.
Execution and final stores have not yet been checked by a formal evaluator.
The OCaml driver currently checks absence of addresses in source terms and runs
separate binding-operation examples; it does not run a type checker.

## Typing coverage

The polymorphic-looking letters below are parameters of the Rocq examples,
not polymorphism in the object language. The executable catalog instantiates
them with concrete types. A dash denotes rejection at every result type.

| Program | Type when accepted | Linear | Affine | Proof or rejection reason |
|---|---|:---:|:---:|---|
| `linear_id` | `A ⊸ A` | yes | yes | `linear_id_typed` |
| `add` | `nat ⊸ nat ⊸ nat` | yes | yes | `add_typed` |
| `add_two_three` | `nat` | yes | yes | `add_two_three_typed` |
| `iter_zero`, `iter_ref` | `nat` | yes | yes | `iter_ref_typed`, for every count |
| `iter_unboxed_step` | — | no | no | The step has a function type, not a boxed function type. |
| `iter_captures_ref` | — | no | no | The step's promotion captures an external resource. |
| `iter_drops_acc` | `nat` | no | yes | The step discards its bound accumulator; `iter_drops_accumulator_affine` and its linear rejection lemma. |
| `curry` | `(A ⊗ B ⊸ C) ⊸ A ⊸ B ⊸ C` | yes | yes | `curry_typed` |
| `uncurry` | `(A ⊸ B ⊸ C) ⊸ A ⊗ B ⊸ C` | yes | yes | `uncurry_typed` |
| `sym_ten` | `A ⊗ B ⊸ B ⊗ A` | yes | yes | `sym_ten_typed` |
| `with_fst` | `A & B ⊸ A` | yes | yes | `with_fst_typed` |
| `tensor_fst` | `A ⊗ B ⊸ A` | no | yes | The second component is unused; both results are proved for arbitrary `A`, `B`. |
| `counter` | `nat` | yes | yes | `counter_typed`; includes strong update from `ref nat` to `ref unit`. |
| `bang_new_twice` | `ref nat ⊗ ref nat` | yes | yes | `bang_new_twice_typed` |
| `bang_captures_ref` | — | no | no | Promotion cannot capture the allocated reference, including under affine weakening. |
| `affine_leak` | `nat` | no | yes | The false branch leaves the reference unused. |
| `derelict` | `!A ⊸ A` | yes | yes | `derelict_typed` |
| `dig` | `!A ⊸ !!A` | yes | yes | `dig_typed` |
| `dup` | `!A ⊸ !A ⊗ !A` | yes | yes | `dup_typed` |
| `del` | `!A ⊸ unit` | yes | yes | `del_typed` |
| `iter_bad_step` | — | no | no | The step has type `!(unit ⊸ nat)`, whose input and output differ. |
| `iter_bad_seed` | — | no | no | A step of type `!(nat ⊸ nat)` receives a `unit` seed. |
| `iter_duplicates_acc` | — | no | no | The step uses its accumulator twice in `let () = x in x`. |
| `free_both_branches` | `ref unit ⊸ unit` | yes | yes | Each branch uses the same resource mask. |
| `free_one_branch` | `ref unit ⊸ unit` | no | yes | The branch returning `()` requires affine weakening. |
| `free_one_component` | `ref unit ⊸ (unit & unit)` | no | yes | The lazy component returning `()` requires affine weakening. |
| `free_after_branch` | — | no | no | The first branch may consume the reference; a later `free` cannot reuse it. |
| `free_nonunit` | — | no | no | `free (new 0)` supplies `ref nat` instead of `ref unit`. |
| `double_free` | — | no | no | The same index cannot belong to both sequential premise masks. |
| `alias_double_free` | — | no | no | Creating `(r,r)` already duplicates a resource, before the two aliases could be freed. |
| `closure_ref` | `unit` | yes | yes | `closure_ref_typed` |
| `nested_ref` | `unit` | yes | yes | `nested_ref_typed` |
| `lazy_shared_ref` | `unit` | yes | yes | `lazy_shared_ref_typed` |
| `add_effects` | `nat` | yes | yes | `add_effects_typed` |
| `sequential_two_refs` | `ref unit ⊸ ref unit ⊸ unit` | yes | yes | Index 1 remains index 1 after index 0 is consumed. |
| `shadowed_resource` | `nat ⊸ nat ⊸ nat` | no | yes | `λx:nat. λx:nat. x` uses only the inner binder, represented by `LVar 0`. |

All iterator rejection lemmas for mismatched step, mismatched seed and duplicated
accumulator quantify over the count, including zero. The external-capture example
itself uses count zero. Bodies are checked even when evaluation would not force
the step thunk.

## Resource accounting in the derivations

`SplitM` distributes each available position to one multiplicative premise.
For `curry`, the application uses masks `[false; false; true]` for the function
and `[true; true; false]` for its argument pair. The pair then divides the latter
between indices 1 and 0. No resource is copied.

`With` and the two result branches of `If` use a common mask. Consequently
`With (LVar 0) (LVar 0)` is linear, while `Pair (LVar 0) (LVar 0)` is not.
`free_after_branch` is rejected even affinely: the freeing branch forces the
branch mask to include the reference, and the outer sequential split prevents
its use by the following `free`.

`tensor_fst` reaches the body of `LetPair` with both local positions available.
The mask of `LVar 1` omits position 0. `TyWeak` reconciles these masks only in
affine mode. The same issue occurs in `λx:unit. ()`, in the dropped iterator
accumulator, and in `shadowed_resource`; closedness of the whole program does
not permit dropping a locally bound linear resource.

Modal maps consume their resource box once using `LetBang`. The introduced
shared hypothesis can be used zero, one or multiple times. The body of every
new `Bang` still has a zero resource mask. The separate
`promotion_capture_rejected` and `shared_substitution_rejects_resource_capture`
proofs cover attempts to bypass this condition in affine mode.

## Expected values and stores

Traces start in the empty store. `alloc ℓ v` creates a cell, `swap ℓ v → w`
replaces its contents and returns the old contents, and `free ℓ` removes a unit
cell. Addresses follow the specified allocator: zero for an empty store,
otherwise one greater than the maximum live address. Freed addresses can be reused.

| Program | Expected result | Expected final store |
|---|---|---|
| `add_two_three`, `add_effects` | `5` | empty |
| `iter_ref n`, including `iter_zero` | `0` | empty |
| `counter` | `1` | empty |
| `closure_ref`, `nested_ref`, `lazy_shared_ref` | `()` | empty |
| `bang_new_twice` | `(ℓ0, ℓ1)` | `{ℓ0 ↦ 0, ℓ1 ↦ 0}`; both references belong to the returned pair |
| `iter_drops_acc` in affine mode | `0` | empty |
| `affine_leak` in affine mode | `0` | `{ℓ0 ↦ ()}`; the reference was dropped |

For `counter`, the trace is:

```text
alloc 0 0
swap 0 1  → 0
swap 0 () → 1
free 0
add 0 1   → 1
```

The second update changes the reference's content type to `unit`, making it
freeable. Both previously extracted numbers are consumed by `add`.

For `iter_ref n`, seed evaluation allocates cell 0. Every iteration then
allocates and frees a temporary cell 1 before obtaining the identity step.
The identity passes cell 0 to the next iteration. The final `free` removes cell
0. Thus there are `n + 1` allocations and frees. At zero the seed still allocates,
but the thunk does not run; at two, cell 1 is allocated and freed twice. This
trace distinguishes reevaluation of the thunk from memoization.

For `add_effects`, each argument extracts a number from its own fresh cell:

```text
alloc 0 2; swap 0 () → 2; free 0
alloc 0 3; swap 0 () → 3; free 0
add 2 3 → 5
```

CBV application evaluates the first argument before the second. Substituting
arbitrary effectful operands directly into the reversed count/seed positions
of `Iter` would reverse these two observable argument traces.

For `nested_ref`, the trace is `alloc 0 (); alloc 1 ℓ0; swap 1 () → ℓ0;
free 1; free 0`. The update extracts the inner reference before either resource
is discarded. For `closure_ref`, the allocated reference stays in the closure
until its application, which frees it once. For `lazy_shared_ref`, only the
selected component executes `free`; constructing the lazy pair executes neither.

Applied to a freshly allocated unit reference, `free_both_branches` frees it
once regardless of the condition. `free_one_branch` with its false condition
returns `()` and leaves the cell live. `free_one_component` returns a lazy pair:
forcing its first component frees the reference, while choosing its second
component drops the reference in affine mode.

Applied to `!e`, the modal maps have the reductions `derelict !e → e`,
`dig !e → !!e`, `dup !e → (!e,!e)`, and `del !e → ()`. Promotion is a thunk;
deletion does not force its body. In `bang_new_twice`, two uses evaluate `new 0`
separately and allocate distinct live cells.

## Coverage boundaries

`typing_no_loc` rejects source terms containing runtime addresses at the root;
`typing_loc_free` excludes addresses anywhere in a typed source term. The
binding examples separately check that renaming and substitution leave `Loc`
unchanged. `shadowed_resource` records the intended named reading as a core
term; correctness of an actual name resolver remains a separate obligation.

Runtime examples are separate from the source catalog. `cyclic_store_balanced`
and `cyclic_store_rejected` prove that the self-owned closure satisfies balance
in both modes but violates the configuration invariant. Further examples cover
an ownership chain, lazy sharing, strong update, sparse address keys, dangling
addresses, aliases, self-swap, promotion capture and the mode-dependent orphan
cell. [Store invariant](store-invariant.md) gives their interpretation and the
scope of the swap proof. The Girard example still belongs to the translation
work. Formal execution traces and checker agreement remain separate obligations
for the algorithms.
