# Database state

Import `DY.Database.All` and open `DY.Database`. This ports the operations and
state guarantees of `DY.Lib.State.Database` using
`PersistentLocalUpdateableState.CompromisableState` for both tables and rows.

A table contains a list of row IDs. Each row lives at a separate updateable-state
address. Configured keys must be individually unique within a table and immutable
across updates. The application supplies row-validity and row-update predicates.
The update predicate must be persistent and transitive; it need not be reflexive.

## Configure a database

Provide `DbTypes RowT` with a list of `Key RowT` values. A key packages its value
type, a `DecidableEq` instance for that type, and its getter. The row type itself
need not have decidable equality. Use distinct row wrapper types for independent
database families.

For example, the checked example in `Tests.lean` uses `Nat × Nat` rows, with the
first field as a unique immutable key and the second field as a strictly increasing
counter:

```lean
instance : DbTypes Row where
  keys := [⟨Nat, inferInstance, Prod.fst⟩]
```

Combine these components into execution entries and proof entries:

```lean
#combine +toplevel into ExecEntryT from
  PersistentLocalUpdateableState.CompromisableState (Db Row),
  PersistentLocalUpdateableState.CompromisableState Row,
  ProtocolEvent (DbEvent Row),
  Network
```

Repeat that list for `ProofEntryT`. Configure bytes and their invariants, provide a
row serializer and `DbPredicate Row` / `DbKnowable Row`, then install the
concrete invariant instances **before** combining `SubTraceInvariant` or
elaborating `TraceInvariant.Has` assumptions:

```lean
instance : PersistentLocalUpdateableState.CompromisableLocalStateInv Row := dbRowCompromisableStateInvariant Row
instance : PersistentLocalUpdateableState.CompromisableLocalStateInv (Db Row) := dbCompromisableStateInvariant Row
instance : ProtocolEvent.EventInv (DbEvent Row) := dbEventInvariant Row
```

`Tests.lean` contains a complete compiling configuration, disjointness witnesses,
operation specifications, `step` composition, and executable regression examples.
State and event components also expose their normal `baseAttackerKnowledge` and
`SubBaseAttackerKnowledgeTheorem` interfaces for integration into attacker proofs.

## Operations

| Operation | Behavior |
| --- | --- |
| `initializeDb RowT participant` | Log an empty-table event, write the empty table, return its stable ID. |
| `addRow participant tableId row` | Check every key before writing; insert the row, log the new pointer list, update the table, return the row ID. |
| `updateRow participant rowId row` | Write a new version at the same row ID. Validity, update constraints, and immutable keys are proof obligations. |
| `dbFind participant tableId query` | Return `(rowId, row)` for the first matching current row, searching newest inserted rows first. |

These use `Traceful`'s built-in failure. Missing tables, duplicate keys during
insertion, and searches without a match fail. An encountered missing row pointer
also fails search; it is not skipped. Invariant traces guarantee that table
pointers resolve. `addRow_failure_sameTrace` proves that insertion failure leaves
the exact trace unchanged.

`getRowOpt` and `getRows` are pure trace inspection functions used in predicates.
`getRows` omits unresolved pointers, matching DY*'s `choose`; the event invariant
requires the result length to equal the pointer-list length.

Table IDs and row IDs are scoped by state type. They may therefore have the same
numeric value. DY*'s `row_sess_id <> sess_id` check is omitted: entry disjointness,
rather than numeric inequality, establishes separation. A fresh ID is not reserved
until its first write, matching the underlying state library.

## Specifications and guarantees

`initializeDb.proof` requires a table/event disjointness witness. `addRow.proof`
requires table/row, table/event, and row/event witnesses. Construct them with
`entriesDisjoint_of_hasStep` from separate branches of a combined entry type;
`Tests.lean` demonstrates this. Different Lean types alone do not prove separation.

Install these explicitly parameterized specifications locally for `step`:

```lean
letI := addRow.proof tableRow tableEvent rowEvent participant tableId row
```

`updateRow.proof` and `dbFind.proof` are registered instances. Successful insertion
and search establish `IsRowInDb`; search also establishes the query predicate.
Updating requires an existing current row, application row validity, the allowed
update relation, and preservation of all keys. As in DY*, these update restrictions
are verified preconditions, not runtime checks.

The main historical guarantees are:

- `isRowInDb_rowPred`: a current database member satisfies the application predicate.
- `isRowInDb_hasLaterVersion`: membership persists on invariant trace extensions,
  possibly with an updated row value.
- `isRowInDb_twice_implies_rowUpdatePred`: versions at one row ID retain all keys
  and are either equal or related by the application update policy.
- `isRowInDb_sameKeys_iff_sameId`: for a configured key, two observations of the
  same database across an invariant trace extension have equal key values exactly
  when they refer to the same row ID.
- `isRowInDb_sameKey_implies_rowUpdatePred`: observations with equal configured
  keys obey the row-update policy, even when obtained at different times.

Table state is justified by a matching logged `DbEvent`. The event establishes
complete pointers and unique keys at its own prefix. `getRows_allKeysSame_later`
and `dbEventPredicate_later` transport those facts using row-update invariants;
`dbEventLogged_implies_predicate` recovers them at the current trace. Table updates
must prepend a nonempty list of pointers, so they cannot delete or reorder rows.

Exact current-row facts are not unconditionally monotone. Consume them with
`mark_non_monotone` when stepping through writes, or use the explicit
noninterference lemmas to prove that an intervening action preserves them.

## Independent row compromise

`DY.Database.Labels` uses the shared updateable-state library's typed compromise
events. There is no database-specific compromise event or serialized-content
compromise helper.

- `participantLabel RowT p`: some row version owned by `p` was compromised.
- `stateLabel RowT p ptr`: some version at that row address was compromised.
- `stateContentLabel RowT p ptr row`: that exact typed row version was compromised.

The proved flow direction is participant → address → value. `DbKnowable RowT`
requires row validity to imply knowability under `participantLabel RowT p`.
`dbRowCompromisableStateInvariant` transports this to the address-and-value label,
retaining the existing row-update policy and immutable-key constraints.
`dbCompromisableStateInvariant` supplies the table instance: serialized tables
contain only public numeric pointers, with row contents stored separately.

Use `PersistentLocalUpdateableState.compromise RowT p ptr` to read and publish one
current row. Its existing `compromise.spec` preserves the trace invariant with no
caller precondition. The database proves:

- `compromiseRow_run`: exactly one typed exposure event and one network message
  containing the selected row are appended.
- `compromiseRow_localStateCompromised_iff`: precisely the selected value label
  becomes corrupt; other value labels retain their prior status.
- `compromiseRow_stateLabel_iff`: precisely the selected participant/address label
  becomes corrupt; every other row address retains its prior status.
- `compromiseRow_missing`: an unwritten address fails without changing the trace.

The label theorems require disjoint network and compromise-event entry families;
`Tests.lean` provides the witness for the concrete configuration. They describe
independent compromise events, not secrecy of bytes shared between rows.
Compromising `Db RowT` exposes the table's pointers using a separate typed event
family. Structural database operations continue to work without serialization.

## Files and port mapping

| File | Contents |
| --- | --- |
| `All.lean` | Public import for the database API and proofs. |
| `Basic.lean` | Keys, typed tables/events, row lookup, uniqueness and event predicates. |
| `Invariants.lean` | Application policy, knowability obligation, concrete row/table/event invariants. |
| `Operations.lean` | Initialization, insertion, update, and query functions. |
| `Execution.lean` | Insertion execution equation and failure atomicity. |
| `Lemmas.lean` | Row evolution, completeness and immutable-key persistence. |
| `Specifications.lean` | Initialization/insertion/update specifications and event invariant extraction. |
| `Search.lean` | Read-only search behavior and specification. |
| `Properties.lean` | Membership persistence and key/row-ID consistency across traces. |
| `Labels.lean` | Labels and flow lemmas over shared typed state-compromise events. |
| `Compromise.lean` | Exact row disclosure and independent row-compromise proofs. |
| `Noninterference.lean` | Entry separation and preservation across unrelated writes/events. |
| `TraceLemmas.lean` | Prefix-invariant helper, marked TODO to move to core. |

DY*'s serialization/tag dispatch is replaced by typed state/event entries.
List helper proofs use Lean's `filterMap`, membership, `Nodup`, and `List.all`
lemmas. F*-specific SMT and tactic utilities (`fully_split_hypothesis`,
`unnorm_term_in_goal`, and the bind-invariant wrappers) are replaced by Lean proofs
and Hoare specifications. The source's unused `get_rows_grows` helper is not
needed: the port proves the stronger complete-list persistence used by the database.

## Validation

```sh
lake build DY.Database.Tests DY.Database.BasicTests DY.Database.NoninterferenceTests
lake build
```

Tests cover specification instantiation and `step`, initialization, insertion,
updates, newest-first search, duplicate-key rejection, missing tables, dangling
pointers, participant isolation, failure atomicity, non-reflexive update policies,
independent row compromise, missing-row compromise, verified row/table disclosure,
and row/table separation when both IDs equal zero. All tests and proofs are
kernel-checked; no `sorry` or axioms are added.
