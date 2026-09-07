# Typed store balance and ownership

`configuration_typed f s e A` combines two independent conditions: typed
resource balance and an acyclic ownership graph. `StoreTyping.v` develops
term typing under a signature, cell typing and balance, then this combined
configuration judgment.
The primitive root-swap case preserves acyclicity; a general operational
preservation theorem remains to be developed.

`Graph.v` supplies positive paths and acyclicity over an arbitrary vertex
type and edge relation. `Store.v` constructs reference edges from store
contents and relates cell replacement to graph updates. The graph is defined
even for untyped stores; its exclusive-ownership interpretation comes from
runtime typing and the balance lemmas in `StoreTyping.v`.

## Runtime typing

`NatMap A := list (nat * A)` supplies the common representation and operations
in `NatMap.v`, independently of term syntax. `Store.v` defines `store := NatMap term`
and `store_sig := NatMap ty`: address/value and address/content-type pairs.
A signature entry `(l, A)` supplies the exclusive
right `l : ref A`. Store balance requires unique keys and matching store and
signature order. This order is a representation convention; address keys can
be sparse. For example, key 7 can occupy position 0.

`NatMapMask.v` defines `masked_key m R l` for any payload type: some entry
with key `l` occupies a position selected by `R`. Availability is monotone
under `mask_le` and implies membership in `natmap_domain m`. Under unique
keys, `SplitM` makes the selected key sets disjoint. Runtime address support
specializes these generic results to the store signature.

`runtime_type f S G L U R e A` extends source typing with an address mask `R`
over `S`. The lexical resource mask `U` still refers to `L`. The `Loc l` rule
looks up `(l, A)` at a signature position `i` and selects that position in `R`;
the term itself retains key `l`. Lambda and pattern binders extend only lexical
scopes. Runtime typing implies correct lengths for both masks and lexical
scoping. `source_runtime` embeds any source derivation with zero address demand.

Multiplicative rules split both masks. Additive alternatives use the same two
masks. Promotion checks its body with both masks zero, including in affine mode;
`runtime_bang_no_locations` proves that it cannot capture a runtime address.
`RTWeak` allows unused lexical and address rights at any affine derivation node.
It does not duplicate rights or change the promotion premise.

`value` distinguishes strict multiplicative pairs from suspended lambda,
additive and promotion bodies. The iterator is an expression, not a value.
`locations` traverses the entire syntax, including all suspensions. Its result
may contain repeated addresses: alternative occurrences inside one additive
owner are permitted. Graph membership collapses these to one edge; requiring
`NoDup (locations e)` would incorrectly reject lazy sharing.

## Balance

`cells_typed f S K s Rcells` checks every cell against the full signature `S`.
Each cell contains a value, has empty lexical scopes and receives its own
address mask. These masks partition `Rcells`. The remaining signature `K`
tracks the content type at each store entry; a complete store uses `K = S`.

`store_balance f s e A` packages a signature and masks satisfying:

```text
all signature rights = Rterm ⊎ Rrest
Rrest                = Rcells ⊎ Rfree
```

Each equation is a `SplitM` proposition. The running term has type `A` with
mask `Rterm`; all stored contents share `Rcells` by disjoint partition.
In linear mode `Rfree` must be zero. Affine mode permits a residual, and affine
weakening can also assign an unused right to an owner. The runtime graph tracks
actual occurrences, including suspended ones.

Proved consequences include unique store keys, allocation of every mentioned
address, and absence of incoming cell edges to an address owned by the running
term. Allocation is a static consequence for a balanced configuration; safety
along executions still requires preservation.

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

Consider a primitive root redex `swap ℓ v` in a typed configuration. The
operational interpretation will require `v` to be a value and a successful
lookup of the old contents `w`. The graph argument itself is stronger: it
applies to any typable operand `v`, without needing those operational premises.

1. The running term owns `ℓ`. By global balance, no stored value can own `ℓ`.
   Hence the old cell graph has no incoming edge to `ℓ`, including hidden
   occurrences in closures or lazy components.
2. The two operands of `swap` have disjoint address masks. Thus `v` cannot
   mention `ℓ`; this rules out a new self-edge.
3. Replacing the cell changes only outgoing edges of `ℓ`. A new cycle would
   have to pass through `ℓ`, which still has no incoming edge. Cycles avoiding
   `ℓ` would already have existed in the old graph.

`graph_acyclic_update` proves step 3 for arbitrary edge relations, without
requiring decidable vertex equality or a finite graph representation.
`store_replace_edge` relates cell replacement to this update condition;
`store_acyclic_replace` specializes the graph theorem to stores.
`runtime_swap_no_self_reference` and `balance_root_no_incoming` establish
its premises. `balanced_swap_acyclic` combines them for the root redex in
either mode. `natmap_replace` preserves keys and store order; it changes exactly
one entry on a store with unique keys and a successful lookup.

The resource transfer expected of the full preservation proof is:

| Owner | Before swap | After swap |
|---|---|---|
| Running term | `{ℓ} ⊎ V ⊎ Frame` | `W ⊎ {ℓ} ⊎ Frame` |
| Updated cell's contents | `W` | `V` |
| Other cell contents and affine residual | unchanged | unchanged |

Here `V` is the new value's demand and `W` the old contents' demand. If the
cell held type `A` and `v : B`, the new signature replaces `(ℓ, A)` by `(ℓ, B)`;
the returned term `(w, ℓ)` has type `A ⊗ ref B`. This changes the type at an
existing key, so a signature-extension lemma alone cannot justify it.

The general typed balance transfer is not proved yet. It needs signature
transport for terms that do not own `ℓ`, reassociation of resource partitions,
runtime substitution that accounts for addresses, and evaluation contexts.
The existing source substitution theorem has zero address demand and does
not provide these results. `swap_before_configuration` and
`swap_after_configuration` verify a concrete update from `nat` to `unit`,
including the returned old natural and the changed reference type.

## Checks and remaining obligations

Rocq examples also establish an acyclic ownership chain, additive sharing,
sparse keys, and rejection of dangling addresses, duplicate keys, root/cell
aliasing, self-swap and address capture in promotion. A discarded unit cell
with a literal result is valid in affine mode and rejected in linear mode.
Three concrete store replacements and two address traversals are additionally
checked by the extracted OCaml driver. These are not evaluator traces or an
executable decision procedure for the invariant.

Fresh allocation, removal, operational rules, runtime substitution, signature
transport, preservation for every step, progress and execution safety remain
open. The linear no-leak argument must connect exact balance and finite
acyclic ownership to root reachability of every cell; then a literal natural
result, which owns no addresses, forces an empty store. That general
reachability result is not claimed here.

All current proofs are checked by Rocq without admitted results or project
axioms. Extraction and the OCaml compiler/runtime remain separate trust
boundaries.
