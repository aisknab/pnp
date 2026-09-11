# M233 plan: retained ambient-profile preservation

Status: implementation and focused verification complete. Start from the actual M232 merge
`caddbfb1a4f1cb333f7aca5d615e10433a44b174`, tree
`0586d261f49b4c5f89b73b600e0717da54d4043a`.
The merge tree equals the fully verified M232 feature tree. Development may
proceed in an isolated checkout while the normal exact post-merge checks run;
do not publish M233 before those checks and the exact M232 reproduction pass.

The four exact M232 post-merge workflows and independent clean reproduction
have now passed. No duplicate Lean build or full unit suite was needed.

## Legacy anchor and dependency edge

Sections 3 and 5 of the manuscript pinned by
[the archive manifest](../../archive/legacy-v0/ARCHIVE.json) require saturated
supports to retain their governed profile dependencies. Section 10's
`RW-SaturatePositive` then requires faithful origin, kernel and obligation
closure before reasoning about transparent cost and routed failures. The
manuscript is the specification, not kernel proof authority.

M232 proves that an omitted gate cannot change a retained profile observation
in any canonical context. It does not yet prove that arbitrary primitive-record
lists normalize to those contexts, or that removing all omitted gates preserves
the observation. Close that entire local edge, rather than adding another
fixed gate, role or finite context as a milestone.

The dependency path is: actual candidate and executable observer; computed
influence and closure; arbitrary-support profile locality; faithful profile
closure reasoning; complete SaturatePositive routing; BCELReady; ZeroSlack.
This milestone closes only locality and retained-profile preservation.

## Unbounded abstraction and theorem interfaces

Quantify over arbitrary finite candidate dimensions, executable models, seeds,
record lists and retained coordinates. No caller-supplied dependency relation,
observer-extensionality proof or support-normalization certificate is allowed.

First establish selected-gate extensionality for the existing support extractor.
Its stored `records` field is allowed to differ; its computed physical boundary,
interface, program, gate count and output word must agree. With common variables:

```lean
variable {inputs gates outputs profileWidth : Nat}
  (candidate : Candidate inputs gates outputs)
  (left right : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth))

theorem extractTerminalSupport_eq_of_gateSelected_eq
    (selectedEqual : terminalGateSelected left = terminalGateSelected right) :
    { extractTerminalSupport candidate left with records := right } =
      extractTerminalSupport candidate right

theorem terminalAmbientSupportImplementation_eq_of_gateSelected_eq
    (selectedEqual : terminalGateSelected left = terminalGateSelected right) :
    terminalAmbientSupportImplementation candidate left =
      terminalAmbientSupportImplementation candidate right
```

Then prove the following with the same dimensions and record types:

```lean
variable
  (model : TerminalCandidateSaturationModel
    (profileWidth := profileWidth) candidate)
  (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
  (coordinate : Fin profileWidth)

theorem terminalCandidateSaturate_profile_locality
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)
    (recordAgreement : ∀ gate,
      TerminalPrimitiveRecord.gate gate ∈
        terminalSaturateRecords
          (terminalCandidateSaturationSystem candidate model) seed →
      (TerminalPrimitiveRecord.gate gate ∈ left ↔
        TerminalPrimitiveRecord.gate gate ∈ right)) :
    model.observe (terminalAmbientSupportImplementation candidate left) coordinate =
      model.observe (terminalAmbientSupportImplementation candidate right) coordinate

theorem terminalCandidateSaturate_profile_preserved
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed) :
    model.observe
        (terminalAmbientSupportImplementation candidate
          (terminalSaturateRecords
            (terminalCandidateSaturationSystem candidate model) seed)) coordinate =
      model.observe
        (terminalAmbientSupportImplementation candidate
          (allTerminalPrimitiveRecords inputs gates outputs profileWidth)) coordinate
```

The membership and agreement premises are ordinary domain conditions, not
correctness certificates. Establish arbitrary-list observation normalization
from structural implementation equality. Use canonical Boolean-mask contexts
and finite gate elimination to discharge the locality proof from M232.
The complete gate universe in the last theorem is the original ambient
implementation, not a newly supplied reference semantics.

## Implementation and rejecting regressions

Add only the extraction bridge to the existing support-extraction module.
Prefer a downstream `ResidualTerminalProfileLocality` module for the observation
normalization, locality and whole-support consequence, with an explicit root
import. Do not change the extraction algorithm or M232's influence definition
merely to simplify the proof.

Prepare these regressions with the source:

- Generic applications at arbitrary dimensions and arbitrary primitive-record
  lists, including noncanonical order, duplicates and non-gate metadata.
- The M232 interaction-sensitive observer: singleton silence must not imply
  independence in a nonempty context.
- A nonconstant observer that reads one actual gate output while another
  independent gate is omitted. The computed saturated support must preserve
  the retained observation of the complete gate set.
- An unretained-profile counterexample with that observer and the empty seed.
  The preservation claim must not silently drop the retained-profile premise.
- Exact theorem types, compiled axiom closures and rejection of supplied
  correctness premises or false global/runtime credit.

If the general theorem fails, report the exact boundary and stop that claim.
Do not substitute finite fixtures, a weakened theorem or an added assumption.

## Producer and expectation reconciliation

| Producer | Synchronized consumers | First rejecting check |
| --- | --- | --- |
| Selected-gate extraction bridge and private helpers | Existing extraction source-shape contract; new audit and generic regression | Exact changed module build and focused axiom closure |
| New downstream locality theorem module | Root import, declaration/type contracts, new Lean regressions and audit | Leaf build, arbitrary-input theorem applications and negative fixture |
| New compiled theorem names | Lean and JavaScript reviewed-name sets, publication row and fingerprint keys | Name-set equality before inventory export; compiled fingerprints afterward |
| Earned evidence row and current coordinate | Core status, progress review, generated report and current summaries | Focused status/progress/public-surface contracts and generated-byte checks |
| New package command and durable workflow block | Closed package-script fixture, verifier and workflow tests | Public-surface preflight; exact shell-block syntax and execution |

Preserve the historical support-extraction audit's original public and reused
declarations. Extend its current source-shape expectation explicitly for
the new helper, and audit the new result under M233 rather than rewriting the
historical audit or its milestone credit. Reconcile the related proper-support,
HResolve, M232, saturation-cost-balance and theorem-inventory consumers before
broad verification. Current generated counts and fingerprints must be derived,
not guessed.

The general locality and preservation proofs, arbitrary-dimension applications,
nonconstant-output and necessary-premise counterexamples, explicit-root axiom
audits, and exact durable workflow block have passed. The canonical compiled
inventory, publication map, status, progress review and current core summaries
have been generated and their focused contracts accepted. The five new theorem
interfaces use only `propext` and `Quot.sound`.

Preflight distinguishes the standalone package-script registry from the
aggregate publication surface. The latter consumes the compiled inventory and
sealed status, so run it after regeneration, before the complete unit suite.
Do not run it against an intentionally unfinished inventory or weaken its check.

## Verification ownership and publication decision

Reuse the M232 cache only after exact source-tree and pinned toolchain checks.
Rebuild the changed dependency chain and explicit root before interpreting an
imported axiom audit. Run focused positive/negative checks first, regenerate
compiled and publication artifacts after source stabilizes, and then cover the
remaining required tests without rerunning unchanged successful test files.
Normal PR and post-merge checks and one exact-merge reproduction remain required.

The supplied ambient observer remains model data. Do not identify it with the
differently typed `profileSystem.observe` without a separate proved bridge.
This result does not derive profile semantics from every valid input, prove
cost transparency or global route completeness, establish unconditional
SaturatePositive/BCELReady/ZeroSlack, or provide a polynomial PCCMin algorithm.
The influence computation still enumerates all subsets.

No fixed weighted checkpoint is earned by this local theorem alone.
Baseline formal artefact coverage: 208 of 210 current scoped rows at M232.
Risk-weighted proof completion estimate: 40%. Uncertainty: 20% to 40%.
Global gates closed: 0 of 5. Derive any eventual coverage change from the
canonical publication ledger; do not predict a generated count.

Publication decision: defer. This local semantic closure result does not by
itself change the published M231 bottom line. Preserve the website's exact
verified source pin and coherent metrics until a major publication is warranted.
Keep meaningful proof-stage notifications independent of website publication.
