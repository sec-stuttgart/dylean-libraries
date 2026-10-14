# Persistent local state with constrained updates

# Disclaimer

**All of this code was ported directly from DY\* with LLMs. The code in this directory will be revised and potentially change substantially.**

# Description

Import `DY.Actions.PersistentLocalUpdateableState`. The implementation is separate
from `PersistentLocalState`: a handle here is a stable state ID, not the timestamp
of a particular write. Addresses are scoped by state type and participant.

## Backward dependency analysis

The analysis starts with `set_state_invariant`, `get_state` and its specifications,
`state_was_set_twice_implies_update_pred`, and `most_recent_state_update_pred`.

1. A write needs the ordinary state predicate and the update predicate from the
   latest old value, when there is one. Historical-write reasoning needs the
   update predicate's persistence and transitivity; it does **not** need reflexivity.
2. Reads and update proofs need latest-value lookup, an occurrence witness, and
   the fact that its timestamp bounds every other write to the address.
3. Preserving current-value assertions across a computation needs the fact that
   the extension does not modify its address, including writes before failure.
4. Compositional modification analysis needs concatenation, subtraction of a
   prefix, reconstruction, and composition of successive suffixes.
5. Latest-value preservation needs last-match search over a concatenation or
   suffix. No first-match search, entry-equality search, or trace splitting is needed.

This analysis was reported before implementation. The final port uses a projected
last-match search to return the value and timestamp together. Consequently it can
prove the needed concatenation law directly by induction, without translating the
F* indexed-entry arithmetic lemmas.

### Functions not translated

From `DY.Core.Trace.Arithmetic.fst`:

- `append_entry_is_concat_singleton`: the `snoc` equation of `Trace.concat` suffices.
- `trace_concat_get_entry`, `trace_subtract_get_entry`: not needed by the projected
  search proof.
- `trace_subtract_trace_length`: no client needs the suffix length.
- `trace_concat_fmap_trace`, `trace_subtract_fmap_trace`: modification analysis is
  performed on execution traces; existing erasure/prefix lemmas handle proof traces.

From the trace-searching section of `DY.Core.Trace.Base.fst`:

- `trace_search_first`, `trace_find_first`, `trace_find_last`.
- `trace_entry_equiv`, `equiv_entry_at`, `equiv_entry_at_grows`, `equiv_entry_exists`.
- `opt_less_defined`, `trace_search_first_later`, `trace_find_first_later`.
- `find_event_triggered_at_timestamp`, `find_event_triggered_at_timestamp_later`.

These support first-occurrence, exact-entry, or event searches, none of which is
needed for latest-value state. The label-ignoring equality machinery also does not
apply to arbitrary Lean state values, which need not have decidable equality.

From `DY.Core.Trace.Arithmetic.Derived.fst`:

- `trace_subtract_empty_trace`, `trace_concat_append_entry`,
  `trace_subtract_concat_left`: no separate theorem is needed in the Lean proofs.
- `trace_search_first_concat`, `trace_search_first_subtract`.
- `trace_find_first_concat`, `trace_find_last_concat`,
  `trace_find_first_subtract`, `trace_find_last_subtract`.
- `trace_split`, `trace_split_trace_length`, `trace_split_get_entry`,
  `trace_split_fmap`, `trace_split_matches_prefix`, `trace_split_grows`, `trace_split_at`.

From `DY.Core.Trace.Modifies.fst`:

- `lemma_union_empty`, `lemma_empty_union`: propositional sets use ordinary logic.
- The separate `traceful_modifies_bind` and `traceful_modifies_option_bind`
  implementations collapse into one fallible `Traceful.modifies_bind` theorem.
- `traceful_modifies_if_then_else_commutes`: ordinary case analysis suffices.
- Action-specific wrappers `traceful_modifies_get_trace`,
  `traceful_modifies_guard_tr`, `traceful_modifies_add_entry`,
  `traceful_modifies_get_time`, `traceful_modifies_send_msg`,
  `traceful_modifies_recv_msg`, `traceful_modifies_mk_rand`,
  `traceful_modifies_trigger_event`: not dependencies of this state library.
- `trace_does_not_modify_addr`, `traceful_does_not_modify_addr`,
  `traceful_never_modifies_addr`: use negation (and universal quantification when
  needed) of `Trace.modifies` or `Traceful.modifies` directly.

No tagged serialization, tag-dispatch predicate assembly, or tagged/typed bridge
lemmas from `DY.Lib.State.Tagged` and `DY.Lib.State.Typed` are needed: the state
entry is already typed. Their state-operation and update guarantees are provided
directly by the new library. Unrelated invariant, message, event, and compromise
operations are outside this port's dependency roots. As with the non-compromisable
part of `PersistentLocalState`, storing a value contributes no attacker knowledge.

## Mapping and use

| DY* concept | DYLean implementation |
| --- | --- |
| Trace concatenation/subtraction | `Trace.concat`, `Trace.subtract` in `DY/Trace/Arithmetic.lean` |
| Last-match search | `Trace.searchLast`, `Trace.searchLastWith`, `Trace.lastValue` in `DY/Trace/Search.lean` |
| Modified-address set | `Trace.modifies addressOf`, `Traceful.modifies addressOf` in `DY/Trace/Modifies.lean` |
| State/update predicates | `LocalStateInv.invariant`, `LocalStateInv.updatePred` |
| State entries | `State.ExecEntryT StateT`, `State.ProofEntryT StateT` |
| Latest state | `getMostRecentStateFor`, `IsMostRecentStateFor` |
| Historical writes | `StateWasSetAt`, `StateWasSet` |
| Fresh state ID | `computeNewSessionId`, `newSessionId`, `newSessionId.spec` |
| Write/read | `setLocalState`, `getLocalState`, their registered `.spec` theorems |
| Historical update guarantee | `stateWasSetTwice_implies_updatePred`, `mostRecentState_updatePred` |
| Preservation without writes | `isMostRecentStateFor_later`, `traceful_isMostRecentStateFor_later` |

Combine `PersistentLocalUpdateableState.State YourType` into execution and proof
entry types, provide `LocalStateInv YourType`, then combine its `SubTraceInvariant`
and (when needed) `baseAttackerKnowledge`/`SubBaseAttackerKnowledgeTheorem` as usual.
`Examples/UpdateableState.lean` demonstrates configuration and `step` use.

`setLocalState participant stateId value` returns the write's timestamp. It can
initialize an unwritten address or update an existing one. Its precondition demands
validity of the new value and an allowed update from the actual latest value.
Constraints are proof obligations, not runtime checks, matching DY* semantics.
`getLocalState` fails when the address is absent; success establishes both exact
current-value knowledge and the persistent invariant.

`newSessionId` scans prior IDs for this participant and state type; it is not based
on trace length. It does not reserve the ID, so two allocations with no intervening
write can return the same ID, as in DY*. Initialize the ID before relying on a
subsequent allocation being distinct.

`IsMostRecentStateFor` is deliberately **not** registered as unconditionally
monotone. Use `mark_non_monotone` for a caller fact consumed by an update, or prove
that the intervening computation does not modify the address. Historical-write
facts and the invariant/update predicates do have persistence lemmas.

The foundational write/read specifications inspect the trace directly to establish
exact latest-state postconditions; the existing generic append/get specifications
only describe entries at timestamps. Callers compose the new registered specs
with `step`.

`Trace.subtract` is a total length-based operation. Its reconstruction and suffix
composition theorems require the prefix relation, matching DY*'s refined argument.

## Compromise

For compromisable state, combine `PersistentLocalUpdateableState.CompromisableState YourType`
instead of `State YourType`. Assembling its trace invariant and base attacker
knowledge theorem requires only `LocalStateInv YourType`: state and compromise
events contribute no attacker knowledge themselves.

To use the verified compromise operation, include `Network` and provide a
`CompromisableLocalStateInv YourType` instance. This extends `LocalStateInv` with
the obligation that valid state is well formed under
`Bytes.KnowableBy (label participant stateId state)`. The state type also needs a
`Comparse.ParseableSerializeable` instance.

`compromise YourType participant stateId` reads the latest value, logs
`Compromise.CompromiseEvent` with the participant, state ID, and value, then sends
the serialized value to the network. An unwritten address fails without extending
the trace. The registered `compromise.spec` proves trace invariant preservation.

`LocalStateCompromised participant stateId state` records exposure of that exact
address and value, and `label_isCorrupt` connects it to label corruption. The fact
persists through updates, but does not automatically compromise a different value
written later. Reusing the same value at the same address reuses its label.

## Validation

`lake build` and `lake build Examples.UpdateableState` check the new modules and
examples. The examples include kernel-checked concrete evaluations of reads,
participant/type isolation, absence, and fresh IDs; a strict non-reflexive counter
constraint; composition with `step`; and modification tracking through failure.

`lake build Examples.UpdateableStateCompromise` checks the combined compromise
configuration and specification, latest-value disclosure and event ordering,
participant isolation, and failure without trace changes for an absent address.

All source changes are additions. No umbrella imports or existing configuration
files need modification: clients import the new module directly.
