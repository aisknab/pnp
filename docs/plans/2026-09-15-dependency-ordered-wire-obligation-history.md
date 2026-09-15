# M263: computed dependency-ordered wire obligation histories

## Manuscript anchor and dependency edge

Follow sections 4, 5, 6.1 and 6.2 of the manuscript pinned by
[the legacy archive](../../archive/legacy-v0/ARCHIVE.json): actual materializer
charges, the full/quotient firewall, R5 creation with full-mode R6/R8 discharge,
and obligation sorting through traceable normalization.

The development parent is the verified M262 merge
`c3d4d9a115a357b44ee8104d129ee15e3174ec7f`, tree
`7bd3bc5854b0307330e9e405b5857de658eba54e`.

M251 and M254 already construct full-value discharges for one fixed carrier and
mask, with generated adjacent pairs and a checked LIFO replay. M250 already
transports actual computational fields through physical normalization. M262
already provides arbitrary-support, paid-copy causal expansion. Preserve those
interfaces and do not re-earn them.

Close the missing computational history edge: derive an order from an arbitrary
finite dependency graph, execute actual wire operations across changing physical
carriers, preserve each creation's actual source snapshot, and permit a complete
result only after every generated obligation has a derived full-value discharge.
This supplies the history component needed before a complete Package E calculus;
it is not the complete manuscript carrier or all rewrite families.

## Raw inputs and computed order

Add `PNP.DependencyScheduler` in `lean/PNP/FiniteDependencyScheduler.lean`.
A graph has arbitrarily many finite nodes and a finite list of predecessors per
node. Do not restrict it to one predecessor chain, adjacent pairs, binary
indegree, fixed graph sizes, or a caller-supplied order or rank.

Compute a deterministic ready-node order from the graph alone. Every iteration
must remove one actual remaining node. A nonempty stuck remainder rejects.
The returned schedule must contain every node exactly once and place every
actual predecessor before its consumer. Prove the general target:

```lean
theorem compile_success_iff {nodes : Nat} (graph : Graph nodes) :
    (∃ schedule, compile graph = some schedule) ↔
      WellFounded graph.Depends
```

Also prove rejection exactly when the actual finite dependency relation is not
well-founded. Reuse the existing compiler's constructive proof pattern and
standard list facts without altering its physical NAND semantics.

The wire-history input is one actual `WireCarrier inputs outputs fields` and a
list of raw events. Each raw event supplies a natural-number identity, explicit
dependency IDs, and one supported operation. Decode IDs to finite node indices;
reject duplicate IDs and missing references before scheduling. References to an
R5 creation in a discharge are intrinsic dependencies as well. No input field
may be a successful replay, full-value equality, witness, observer, replacement
truth table, charge, restoration program, or correctness certificate.

Acyclicity guarantees a complete computed order, not semantic admissibility of
every instruction set. Execute and check that computed order. Reject a lifecycle
request that is unavailable at its execution point; do not claim confluence or
acceptance of every possible ordering of an underspecified graph.

## Actual history operations and invariant

Use `PNP.DirectWire.WireObligationHistory` in
`lean/PNP/NANDWireObligationHistory.lean` for raw-event ordering, with internal
physical invariants in `NANDWireObligationHistoryState.lean` and the computed
source-bound trace and closed constructor in `NANDWireObligationHistoryExecution.lean`.
A single evolving physical carrier is executed in the computed order.
The graph is a dependency graph of events, not
a collection of branch circuits whose bookkeeping implies free shared gates.

1. R5 drops an available field, retaining the same physical program and using
   quotient-only padding for that coordinate. It records a fresh creation-event
   ID and the actual pre-drop carrier and source. Only R5 creates obligations.
   The same field may be dropped again after discharge under a fresh ID;
   an already-open field or reused event ID must reject.
2. Physical normalization uses the existing computed closure. Preserve ordinary
   outputs, every available field, and the immutable snapshots of open entries.
   Do not identify projection with normalization: projection alone adds no gate.
3. The source-identity R6 case computes a currently visible representative using
   the canonical original sources and the established full-value transport
   invariant. Reuse the existing representative scan. Never compare bare gate
   numbers from different programs, use forgotten padding as a representative,
   or enumerate semantic truth tables. Rebind the actual current source and
   derive its full value before closing the matching creation ID.
4. R8 locates the exact open creation, computes its real missing-wire materializer
   from the captured carrier, and appends that program to the current carrier.
   Derive the restored source's full value from the actual physical operation.
   Pay the whole appended program. Separate restoration events do not acquire
   free cross-snapshot sharing because a history node is referenced twice.
5. A full-mode read returns a source only for an available field and records
   its actual source binding. Reading an open field must reject.
6. A complete result requires an empty open ledger. Unknown, duplicate or
   premature discharges reject; quotient-only agreement cannot close an entry.

Maintain a constructive invariant connecting every available field and ordinary
output to the original full word, and every open entry to the full value of its
captured source. Derive every witness inside the constructor. A typed proof in
the result is evidence only because the actual raw-input execution constructed
it; do not add a premise asking the caller to supply that invariant.

## Exact general result

Define `compileHistory source rawEvents` as a total, fail-closed constructor.
Its successful result contains the actual final carrier, computed event order,
source-bound creation/discharge/read records, and physical charge accounting.
For arbitrary input, output, field and event dimensions, prove that success
implies all of the following, without a supplied semantic premise:

- every event was executed exactly once in the computed dependency order;
- every creation ID is unique and every final obligation is discharged;
- every discharge and full read names an actual physical source with its
  valuation-wise original full value;
- every ordinary output and every computational field of the final physical
  carrier agrees with the original carrier for every valuation;
- `final gate count + removed gates = initial gate count + charged gates`.

Here charged gates count actual appended materializers, and removed gates come
from the existing physical-normalization savings witnesses. Bookkeeping records
are not physical gates. Restoration may increase size. If exposing a gain result,
check the actual fully charged final size against the original, not a projected
intermediate or an uncharged branch. No execution-time claim follows from the
gate equation or finite termination.

A failure of these general targets stops the milestone. Do not replace the
history constructor with one fixed transcript, a supplied topological order,
an added correctness assumption, or another adjacent-pair replay.

## Source and expectation matrix

| Changed boundary | Expectations prepared with the source | Cheapest check |
| --- | --- | --- |
| Finite dependency scheduler | Exact general types, complete ordered node set, no supplied order, stuck/cyclic rejection | Source contracts and bounded kernel/runtime graph regressions |
| Raw history decoding | Globally fresh IDs, exact explicit and intrinsic dependencies, missing-reference rejection | Positive and hostile source/decoder cases |
| Creation and carrier transport | Actual snapshots, full-value invariant, repeat coordinates with fresh IDs, no open-field use | Targeted arbitrary-dimension Lean examples and small fixtures |
| R6/R8 and physical charges | Actual representative/materializer sources, full discharges, nonzero paid restoration, no free cross-snapshot sharing | Source mutations, kernel theorem/type audit and bounded execution |
| Root and reviewed theorem names | Root import closure, Lean inventory producer, JavaScript required-name contract, audit names | Name-set/source preflight before compiled inventory |
| Publication and current core status | Exact emitted types/axioms/fingerprints, conservative claims, fixed-weight progress history | Focused positive/hostile cases after canonical generation |
| Package scripts and workflow | Closed script fixture, exact new command block and trigger coverage | Independent package/source tests and exact shell-block syntax check |

Keep inherited proof modules unchanged unless a necessary interface gap is
identified. Search existing audits and Lean regressions for each edited module
and declaration. Update affected expectations before testing. Keep general
kernel proofs separate from bounded runtime fixtures; never use native execution
as theorem authority. Do not create a new temporary workflow.

## Verification, progress and publication

Reuse the source- and toolchain-matched dependency cache. Develop with capped
targeted source and constructor checks, then build the changed dependency chain
and explicit root serially. Run the permanent root-imported axiom and regression
commands and the exact new workflow block. Stabilize reviewed names and generator
inputs before inventory extraction; derive fingerprints and counts only from
compiled evidence. Reconcile downstream contracts before one deduplicated full
core suite, normal PR/post-merge checks and exact-object reproduction.

Baseline measures are separate: formal artefact coverage is 238 of 240 current
scoped rows earned; risk-weighted proof completion estimate is 40%; uncertainty
range is 20% to 40%; global gates closed are 0 of 5. No fixed checkpoint is
expected to close solely from this computational history component.

Publication decision: defer PNPLabs unless implementation establishes a broader
load-bearing capability than this planned component or corrects a public claim.
The coherent M262 public release stays pinned and unchanged. Send meaningful
verified core-submilestone notifications independently of website cadence.

Full R7 and other R1-R9 semantics, all N1-N10 transports, noncomputational carrier
records, matched-cost support Pull/Expand, the complete Package E verifier, global
route coverage, unconditional SaturatePositive/BCELReady/ZeroSlack, exact PCCMin,
complete encoded polynomial bounds, deterministic SAT and the eligible root
theorem remain open. Do not award unconditional or polynomial credit here.
