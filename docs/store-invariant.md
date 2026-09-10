# Typed store balance and ownership

`configuration_typed f s e A` combines two independent conditions: typed
resource balance and an acyclic ownership graph. `StoreTyping.v` develops
term typing under a signature, cell typing and balance, then this combined
configuration judgment.
`StoreTypingInversion.v` provides syntax-directed generation, canonical forms
and typed cell lookup shared by the operational metatheory.
`Preservation.v` proves that every operational step preserves typed resource
balance and ownership acyclicity. The proof treats allocation, strong update
and deallocation explicitly and propagates the invariant through every strict
evaluation position.
`Progress.v` independently proves that a typed balanced configuration can
step unless its term is already a value.
`Safety.v` composes preservation and progress over multi-step execution and
shows that the fuelled runner cannot return `RStuck` from a typed configuration.
Its `configuration_no_dangling` theorem states that every location occurring
in the running term or any cell contents belongs to the concrete store domain.

`Graph.v` supplies positive paths and acyclicity over an arbitrary vertex
type and edge relation. `Store.v` constructs reference edges from store
contents and relates cell replacement to graph updates. The graph is defined
even for untyped stores; its exclusive-ownership interpretation comes from
typing with locations and the balance lemmas in `StoreTyping.v`.

## Typing terms with locations

`NatMap A := list (nat * A)` supplies the common representation and operations
in `NatMap.v`, independently of term syntax. `Store.v` defines `store := NatMap term`
and `store_sig := NatMap ty`: address/value and address/content-type pairs.
A signature entry `(l, A)` supplies the exclusive
right `l : ref A`. Store balance requires unique keys and matching store and
signature order. This order is a representation convention; address keys can
be sparse. For example, key 7 can occupy position 0.

`NatMapMask.v` retains the generic connection between association lists and
positional masks, but runtime typing does not use a positional mask for
locations. Store keys are stable across insertion and removal, so ownership is
represented directly by `store_sig` fragments and divided by `Split`.

`has_type_with_loc f G L U R e A` extends source typing with the owned location
fragment `R : store_sig`. The lexical resource mask `U` still refers to `L`.
The `Loc l` rule owns exactly `[(l, A)]`; the global balance later verifies that
this entry belongs to the current store signature. Lambda and pattern binders
extend only lexical scopes. Typing with locations implies a correct lexical
mask length and lexical scoping. `source_runtime` embeds any source derivation
with an empty location fragment.

Multiplicative rules use `SplitM` for the lexical mask and `Split` for location
fragments. Additive alternatives reuse both inputs. Promotion checks its body
with a zero lexical mask and an empty location fragment, including in affine mode;
`runtime_bang_no_locations` proves that it cannot capture a runtime address.
`TyLocWeak` allows unused lexical rights and a `split_incl` location super-fragment
at any affine derivation node.
It does not duplicate rights or change the promotion premise.

`value` distinguishes strict multiplicative pairs from suspended lambda,
additive and promotion bodies. The iterator is an expression, not a value.
`locations` traverses the entire syntax, including all suspensions. Its result
may contain repeated addresses: alternative occurrences inside one additive
owner are permitted. Graph membership collapses these to one edge; requiring
`NoDup (locations e)` would incorrectly reject lazy sharing.

## Balance

`cells_typed f K s Rcells` walks the signature `K` and store `s` in lockstep.
Each cell contains a value, has empty lexical scopes and receives its own
location fragment. These fragments partition `Rcells` with `Split`.

`store_balance f s e A` existentially packages a full signature and fragments
satisfying:

```text
all signature rights = Rterm ⊎ Rrest
Rrest                = Rcells ⊎ Rfree
```

Each equation is a `Split` proposition. The running term has type `A` with
fragment `Rterm`; all stored contents share `Rcells` by disjoint partition.
In linear mode `Rfree` must be empty. Affine mode permits a residual, and affine
weakening can also assign an unused right to an owner. The runtime graph tracks
actual occurrences, including suspended ones.

Proved consequences include unique store keys, allocation of every mentioned
address, and absence of incoming cell edges to an address owned by the running
term. Preservation carries these properties and ownership acyclicity through
execution. The remaining safety results additionally need reachability facts
for balanced acyclic stores.

## Why balance does not exclude cycles

Take `F = unit ⊸ unit` and the value

```text
v = λx:unit.
      let (g, r) = swap ℓ0 () in
      let () = free r in g x
```

With signature `[(0, F)]`, the value has type `F` and owns address 0. Its body
uses strong update to take out a function and replace the cell by unit, then
frees the returned reference and applies the function. No recursive type is
needed. The store `[(0, v)]` with running term `0 : nat` is balanced even in
linear mode: the cell supplies one right and its own contents consume it.

`cyclic_store_balanced` proves this balance in both modes. But the cell has an
edge `0 → 0`, witnessed by `cyclic_store_self_edge`. Thus
`cyclic_store_not_acyclic` and `cyclic_store_rejected` reject it as a typed
configuration. This is a counterexample to balance alone, not a demonstrated
execution from an empty store.

`graph_path (store_edge s)` contains at least one edge. `store_acyclic s` is
`graph_acyclic (store_edge s)`: it forbids a path from any address back to
itself. The running term is an additional root with no incoming edges, so
testing cell cycles suffices for the full graph.
`source_configuration` proves that a closed source derivation gives a typed
configuration with an empty store.

## The strong-update case

Consider a primitive root redex `swap ℓ v` in a typed configuration. Its
operational rule requires `v` to be a value and a successful lookup of the old
contents `w`. The graph argument itself is stronger: it
applies to any typable operand `v`, without needing those operational premises.

1. The running term owns `ℓ`. By global balance, no stored value can own `ℓ`.
   Hence the old cell graph has no incoming edge to `ℓ`, including hidden
   occurrences in closures or lazy components.
2. The two operands of `swap` have disjoint location fragments. Thus `v` cannot
   mention `ℓ`; this rules out a new self-edge.
3. Replacing the cell changes only outgoing edges of `ℓ`. A new cycle would
   have to pass through `ℓ`, which still has no incoming edge. Cycles avoiding
   `ℓ` would already have existed in the old graph.

`graph_acyclic_update` proves step 3 for arbitrary edge relations, without
requiring decidable vertex equality or a finite graph representation.
`store_replace_edge` relates cell replacement to this update condition;
`store_acyclic_replace` specializes the graph theorem to stores.
`runtime_swap_no_self_reference` and `joint_root_no_incoming` establish
its premises. `joint_swap_acyclic` combines them for a focused swap redex in
either mode. `natmap_replace` preserves keys and store order; it changes
exactly one entry on a store with unique keys and a successful lookup.

The preservation proof performs the following resource transfer:

| Owner | Before swap | After swap |
|---|---|---|
| Running term | `{ℓ} ⊎ V ⊎ Frame` | `W ⊎ {ℓ} ⊎ Frame` |
| Updated cell's contents | `W` | `V` |
| Other cell contents and affine residual | unchanged | unchanged |

Here `V` is the new value's demand and `W` the old contents' demand. If the
cell held type `A` and `v : B`, the new signature replaces `(ℓ, A)` by `(ℓ, B)`;
the returned term `(w, ℓ)` has type `A ⊗ ref B`. This changes the type at an
existing key, so a signature-extension lemma alone cannot justify it.

`Preservation.v` combines address-aware substitution, keyed signature updates,
`Split` interchange, cell typing and the global balance partition. It covers every operational rule, including
allocation, strong update, removal and all strict CBV positions. Unchanged
siblings keep their own fragments; no ambient address mask must be transported
across a store edit.
`swap_before_configuration` and
`swap_after_configuration` verify a concrete update from `nat` to `unit`,
including the returned old natural and the changed reference type.

## Checks and remaining obligations

Rocq examples also establish an acyclic ownership chain, additive sharing,
sparse keys, and rejection of dangling addresses, duplicate keys, root/cell
aliasing, self-swap and address capture in promotion. A discarded unit cell
with a literal result is valid in affine mode and rejected in linear mode.
Seven concrete store operations—replacement, fresh insertion and removal—and
two address traversals are additionally checked by the extracted OCaml driver.
Ten evaluator outcomes additionally check allocation, update and removal in
complete runs. Eight separate event-trace checks record the exact chronological
sequence of `Alloc l`, `Swap l`, and `Free l`. These traces observe execution;
they are not an executable decision procedure for the invariant.

The operational rules and their executable/relational correspondence are now
proved. Substitution with locations, keyed `Split` transformations and
evaluation-context lemmas are also proved. `preservation` carries `store_balance`,
the result type and linear exactness through every `small_step`;
`ownership_acyclic_preserved` carries the graph invariant.
`configuration_preservation` combines them, and executable corollaries are
provided for `step`. Separately, `Progress.v` proves that a typed balanced
configuration is a value or can take a relational step; canonical forms and
typed cell lookup also show that the executable classifier cannot return
`SStuck`. `Safety.v` lifts configuration preservation through `reaches` and
rules out a final `RStuck` result for every fuel bound. It also packages the
balance allocation lemma as the configuration-level no-dangling invariant.
For linear configurations, `linear_runtime_locations_complete` and
`linear_cells_locations_complete` turn exact balance into the statement that
every allocated address is owned by either the running term or another cell.
The finite acyclic graph lemma in `Graph.v` then proves
`linear_configuration_root_reachable`: every cell is reachable from a location
owned by the running term. `Safety.v` combines this result with multi-step
preservation and the canonical form of a final natural-number value to prove
`no_leak`: a terminating closed linear program of type `nat`, started from the
empty store, has an empty final store. The event-domain correspondence gives
every trace an explicit live-address lifetime. Consequently, `no_double_free`
proves that two `Free l` events require an intervening `Alloc l`; address reuse
therefore starts a new lifetime. For a typed configuration, preservation and
no-dangling additionally prove that immediately after `Free l`, the address is
absent from the residual term and every remaining cell.

All current proofs are checked by Rocq without admitted results or project
axioms. Extraction and the OCaml compiler/runtime remain separate trust
boundaries.
