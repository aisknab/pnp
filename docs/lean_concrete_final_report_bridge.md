# Checked SAT hardness in the conditional final-report bridge

M243 closes the final complexity dependency in Section 18 of the pinned
manuscript: Accepted package implies P=NP and Generated package sufficiency.
M231 already proved the required all-input concrete SAT NP-completeness.
This change connects that result to the existing active bridge instead of
asking its caller to supply the same hardness theorem.

M243 connects the checked all-input Cook-Levin NP-completeness theorem directly to the active final-report bridge. No supplied SAT-hardness parameter remains. The bridge still requires an explicit proof-bearing PCCMin loop certificate containing the concrete residual-band polynomial decider; packaging and acceptance do not construct that certificate.

Formal artefact coverage: 219 of 221 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Exact active interfaces

| Interface | Checked boundary |
| --- | --- |
| `PNP.sat_np_hard_checked` | `SATHard`, with no caller-supplied hardness witness. |
| `PNP.sat_np_complete_checked` | `NPComplete SAT` for the exact concrete CNFSAT predicate. |
| `PNP.accepted_generated_package_implies_p_eq_np` | An explicit proof-bearing loop and its accepted typed package imply concrete P=NP. |
| `PNP.final_report_bridge` | `FinalReportAntecedent → FinalReportConsequent`, with no additional trust parameter. |

The existing active bridge now consumes the compiled M231 theorem.
The unused `CheckerTrustModel` record is removed. The concrete reductions,
typed package construction and canonical-identifier checker retain their
previous mathematical definitions.

## What is still required

The complete PCCMin loop certificate is not constructed. Its
`residualBandDecider` field is a concrete polynomial-time decider with semantic
and runtime proofs, not an identifier. The final antecedent remains:

```lean
∃ loop : PCCMinLoopCertificate, AcceptedGeneratedPackage loop
```

Transparent generation accepts any such explicitly provided certificate;
this does not prove one exists. Historical checker acceptance, string handles
and generated report records cannot discharge that existence obligation.

Unconditional SaturatePositive, BCELReady and ZeroSlack, the complete exact
PCCMin algorithm and its encoded-input polynomial runtime, output and
certificate bounds, deterministic CNFSAT in P, and the eligible theorem
`PNP.Main.p_eq_np` remain open. The publication gate is false.

## Axiom and progress accounting

The four reviewed interfaces use exactly the Lean-standard axioms
`Classical.choice`, `Quot.sound` and `propext`. This is the existing M231
hardness theorem's closure. It is now included in the active bridge's exact
audit; no project-specific axiom or supplied hardness premise is introduced.
The older reduction and package-reflection endpoints keep their narrower
reviewed closures.

M231's hardness checkpoint was already earned. Connecting it here receives
no duplicate points and does not close the final root transport checkpoint.
No fixed checkpoint or global gate closes. Formal artefact coverage changes
independently; the risk-weighted estimate remains unchanged.

## Verification and publication

Exact-type regressions apply the active bridge without a hardness argument and
retain the proof-bearing loop-existence premise. Hostile tests reject restored
trust fields, weakened endpoints, a vacuous antecedent, string certificates
and an incorrectly released root. All affected compatibility tests and the
exact edited workflow blocks are checked alongside the new axiom audit.

Publication decision: **defer PNPLabs**. Its coherent M231 snapshot already
reports concrete NP-completeness; this internal integration does not change
the public bottom line.

See the [milestone plan](plans/2026-09-12-concrete-final-report-bridge.md),
[bridge description](lean_bridge.md), [formal status](FORMAL_RECONSTRUCTION.md),
[typed package boundary](lean_typed_pccpack_reflection.md) and
[fixed progress model](proof_progress.md).
