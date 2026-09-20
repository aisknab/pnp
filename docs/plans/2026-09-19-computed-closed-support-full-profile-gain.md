# M278: computed closed-support full-profile physical gain

Coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-19-278`.

Formal artefact coverage: 254 of 256 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Legacy anchor and dependency edge

The manuscript pinned by [ARCHIVE.json](../../archive/legacy-v0/ARCHIVE.json)
at `final-pnp-proof-report-docs-hardened-7072f8d-sealed` supplies the
SaturatePositive/RankWF reconstruction objective: a valid positive full-mode
local replacement must induce sound strict physical descent. Its positive
support discovery, interface exposure, first-loss routing and projection
positivity requirements are separate obligations. The legacy specification
is provenance, not proof authority.

M277 computed support observations and field compatibility but did not rebuild
the whole circuit. M278 closes that physical-reconstruction edge using the
actual minimum, input specialization, complement and crossing interface.
This is a proposed explicit reconstruction of the computational-wire-profile
fragment; it is not a claim to have reconstructed the complete manuscript
profile grammar or all SaturatePositive hypotheses.

## Unbounded interface and exact theorem types

Inputs are an arbitrary finite wire carrier, a field keep mask and ordinary
seed records. No replacement, semantic correctness certificate or support
minimum is supplied by the caller. The following checked source statements
are in `PNP.DirectWire.ClosedSupportFullGain`; their exact elaborated types
are independently pinned by the compiled publication contract.

```lean
theorem result_fullEquivalent (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    WireProfile.FullEquivalent target (result target keep seed)

theorem result_gain_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    (result target keep seed).implementation.gateCount +
        (terminalSaturationCostSnapshot target.implementation.candidate
          (WireProfileAmbient.model target keep)
          (ClosedSupportObservation.records target keep seed)).fullSlack =
      target.implementation.gateCount

theorem result_fullSlack_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    WireProfile.fullSlack (result target keep seed) +
        (terminalSaturationCostSnapshot target.implementation.candidate
          (WireProfileAmbient.model target keep)
          (ClosedSupportObservation.records target keep seed)).fullSlack =
      WireProfile.fullSlack target

theorem improvement?_strictGain (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (replacement : WireCarrier inputs outputs fields)
    (found : improvement? target keep seed = some replacement) :
    StrictEquivalentGain target.implementation replacement.implementation
```

## Implementation and evidence order

1. Derive the specialized minimum prefix and uniform retained-source values.
2. Reconstruct the physical complement and every ordinary output and field.
3. Prove exact gate/full-slack accounting and the checked strict-gain adapter.
4. Reconcile source, root imports, audit names, regressions and theorem pins
   before inventory extraction; then seal fingerprints from compiled evidence.
5. Reconcile canonical progress, status, current narratives, package contracts
   and generated artefacts before targeted and broad validation.
6. Reuse unchanged root/inventory evidence, run the required test-file union
   once, and retain independent PR, merge and exact-object release checks.

## Producer and consumer contract

| Producer | Consumers and focused checks |
| --- | --- |
| Two Lean modules and root imports | Source contract, root-target contract, 27-name axiom audit, general/guard/runtime regression |
| Compiled theorem inventory and publication map | Frozen type fingerprints, source-closure seal and hostile publication mutations |
| Status schema and canonical progress ledger | Status-field mutations, unchanged checkpoint/gate checks and current-document preflight |
| Package and durable workflow | Closed package-script fixture, verifier test list, literal shell syntax and exact changed workflow execution |
| Generated status, TeX and PDF | Mirror identity, generation check, report integrity and source-bound verifier |

## Remaining obligations and progress decision

The full-profile minimum, source matching and saturation influence tests remain exhaustive finite reference computations. This does not derive a proper positive support, make whole-span replacements locally VerifyDW-eligible, implement the manuscript's complete noncomputational profile grammar, establish global route coverage or unconditional SaturatePositive, BCELReady or ZeroSlack, or prove complete PCCMin polynomial runtime, output-size or certificate bounds. The eligible root theorem remains absent and P = NP is not proved.

M278 connects an actual computed closed support to a full-profile-preserving whole-circuit replacement, with an exact gate saving and exact retirement of whole-carrier full slack. The reference minimum, physical complement, input bindings and field sources are derived rather than supplied as correctness premises. This closes a bounded positive-branch reconstruction dependency, but not proper-positive support discovery, the complete manuscript profile grammar, terminal-derived families, global route coverage or polynomial minimization. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

Whole-span replacement is not automatically a proper locally admissible
VerifyDW event. The finite reference minimum is exhaustive, so terminating
reference reconstruction supplies no polynomial runtime or encoded-size
bound. Ordinary finite fixtures earn no additional checkpoint weight.

## Publication decision

Publication decision: defer. This completes the physical reconstruction of a computational-field-preserving finite reference improvement, not proper-positive support discovery, complete manuscript profiles, terminal-derived families, global route coverage or polynomial construction. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.
