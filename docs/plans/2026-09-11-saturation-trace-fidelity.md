# M234 plan: saturation trace fidelity and metadata cost balance

Status: implementation in progress, not earned. The release branch starts from
actual M233 merge `588167ddab3e0b98fe0e3f96c1954fbe3b6cf5fd`, tree
`0d6732959b53305d565c4ffc8e8dc6827f5be798`. Isolated preparation used the
identical verified M233 feature tree. All M233 PR and post-merge checks passed,
as did independent exact-feature and exact-merge source-bound verification.

## Legacy anchor and load-bearing dependency

Section 3 of the manuscript pinned by
[the archive manifest](../../archive/legacy-v0/ARCHIVE.json) requires the completed
support to be the actual computed saturation. Section 10, RW-SaturatePositive,
uses a deterministic chain ending at the completed saturated support, with full
slack and projection-defect accounting. Its named obligations include
`transparentSaturationCostBalanced` and `firstNontransparentStepRecorded`.

The existing executor returns both canonical `records` and cost-accounting
`replayRecords`. Trace continuity is proved, but the replay endpoint must also
be linked to the canonical saturation. M233 proves structural support
extensionality and retained-profile locality; use that result to identify the
two endpoint ambient implementations and their actual cost snapshots.

Metadata records do not insert a physical gate. Derive their cost transparency
from the actual trace and extractor, rather than supplying a balance certificate
or running another chosen finite instance.

The dependency path is: computed saturation; faithful generated trace; identical
terminal ambient carrier; exact snapshot accounting; transparent/routed
saturation; BCELReady; ZeroSlack. This milestone closes only the trace and
metadata-accounting edges.

## Unbounded theorem interfaces

Quantify over arbitrary finite input, gate, output and profile dimensions,
systems, candidates, executable models, seeds, records and generated events.

Prove event validity from membership in the actual generated trace:

```lean
theorem terminalSaturateTrace_event_valid
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈ (terminalSaturateTrace system seed).events) :
    event.afterRecords = event.required :: event.beforeRecords ∧
      ∃ kind, event.kind? = some kind ∧
        system.requires kind event.dependent event.required = true
```

Strengthen the implementation invariant with dependent membership or record
freshness if needed, but do not add those as caller-supplied correctness premises.

Prove extensional equality of the actual replay and canonical endpoint:

```lean
theorem terminalSaturateTrace_replayRecords_iff
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ (terminalSaturateTrace system seed).replayRecords ↔
      record ∈ terminalSaturateRecords system seed
```

Then specialize to `terminalCandidateSaturationSystem candidate model`.
Establish equality of its two actual ambient implementations and of every cost
snapshot field, except the deliberately order-sensitive stored `records` field.
Use a record update, not a false literal-list equality.

Finally prove:

```lean
theorem terminalCandidateSaturateTrace_metadata_transparent
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (member : event ∈
      (terminalSaturateTrace
        (terminalCandidateSaturationSystem candidate model) seed).events)
    (metadata : ∀ gate, event.required ≠ TerminalPrimitiveRecord.gate gate) :
    TerminalTransparentSaturationStep candidate model event
```

Membership and the record-kind restriction are ordinary domain conditions.
No trace-validity, replay-correctness, observer-congruence or cost-balance
certificate may replace the derived conclusions.

## Implementation and proof order

1. In the existing executable-saturation module, erase trace annotations into
   the already verified work state. Prove step and iteration compatibility.
   Reuse its finite-work-list termination theorem.
2. Preserve a membership invariant relating cost records to processed records
   and remaining seed-origin records. At termination, derive replay membership
   equality without changing the execution algorithm or its output fields.
3. Preserve generated-origin validity through the queue. Derive the first
   actual rule and the exact before/after shape for every emitted event.
4. In a downstream module importing M233 and the existing cost-balance module,
   transfer selected-gate equality to ambient implementation and snapshot
   equality. Avoid unfolding exhaustive minima during elaboration.
5. Apply these results to every generated non-gate event. If useful, expose the
   existing classifier's true result as a consequence, not a new unchecked fast
   path.

Do not redefine `replayRecords` to be canonical `records`, replace the trace
engine, change the influence computation, or weaken a statement to obtain an
easy proof. If the general proof fails, record the precise boundary and stop
that claim; do not substitute fixed examples or an added assumption.

## Regression and expectation plan

Add generic theorem applications and permanent cases for empty/duplicate seeds,
cyclic dependencies, multiple rule candidates, all non-gate record constructors,
and a nonconstant actual candidate observer.

Reject malformed arbitrary events: a missing rule or an unrelated after-state
must not acquire generated-event credit. Include a generated physical gate
whose full minimum does not increase by one, so metadata transparency cannot be
misread as universal transparency. Preserve an open-obligation example:
balanced cost and unchanged observations do not discharge an obligation.

Update producer and consumer contracts with the source: current declaration
lists, explicit root imports, Lean regressions and axiom audits, both reviewed
theorem-name sets, publication fingerprints, the closed package-script fixture,
verifier and durable CI coverage. Extract and execute changed workflow shell
blocks. Run targeted proof and hostile contracts before inventory generation
and the complete required test union.

Derive counts, coordinates and hashes only after source stabilizes. Preserve
existing progress-ledger formatting and historical entries. Generated current
summaries must distinguish evidence coverage from the fixed-weight estimate.

## Remaining blockers and publication decision

The observer/profile model remains supplied data. Influence and semantic minima
still use exhaustive finite reference constructions; this is not a polynomial
algorithm. Physical gate/materializer steps still need forced full-minimum
growth, quotient bounds, ownership and correct routing. Metadata cost balance
does not establish obligation discharge, complete closure safety, global route
coverage, unconditional SaturatePositive, BCELReady, ZeroSlack, deterministic SAT
or the eligible root theorem.

Baseline at M233: formal artefact coverage 209 of 211 current scoped publication
rows earned; risk-weighted proof completion estimate 40%; uncertainty 20% to 40%;
global gates closed 0 of 5. No fixed checkpoint change is anticipated from this
local reconstruction edge alone.

Publication decision: defer. Preserve the coherent published M231 website pin
unless the actual result materially changes the public bottom line. Keep
meaningful proof-stage notifications independent of website releases.
