# Proof progress model

The project reports two independent measurements. They answer different
questions and must never be combined.

## Formal artefact coverage

Formal artefact coverage counts earned rows in the current formal publication
milestone ledger. At
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-24-188`, 164 of 166
current scoped rows are earned, or 98.8 percent of that evidence ledger.

This is not proof completion. Rows are not equal units of mathematical
difficulty, and the denominator can grow when a dependency is discovered or an
obligation is decomposed. New finite, local, conditional, or supplied-data
results can add valuable evidence without retiring a global proof obligation.

## Risk-weighted proof completion estimate

The version 0 model assigns 100 fixed points to load-bearing checkpoints:

| Track | Available | Earned at M188 |
| --- | ---: | ---: |
| Formal foundations and proof infrastructure | 15 | 13 |
| Concrete reductions and locked-NAND route | 20 | 15 |
| Unconditional residual core and ZeroSlack | 35 | 2 |
| Exact PCCMin algorithm, complexity and bounds | 20 | 1 |
| Root theorem and project-axiom elimination | 10 | 4 |
| **Total** | **100** | **35** |

The M188 risk-weighted proof completion estimate is therefore 35 percent, with
a current uncertainty range of 20 to 40 percent. This is a conservative estimate
of how much of the complete formal proof burden has been retired. It is not the
probability that `P = NP`, confidence that the proposed route is correct, or an
estimate of time remaining.

The exact checkpoint definitions, evidence, remaining limitations, gate states,
score-change record requirements, and baseline history are in the canonical
machine-readable ledger:

[`status/PROOF_PROGRESS.json`](../status/PROOF_PROGRESS.json)

The five current global gates are open: Concrete SAT, residual-band minimisation,
unconditional ZeroSlack, polynomial runtime and certificate bounds, and the root
theorem plus axiom audit. The compiled project-specific axiom inventory is empty,
`PNP.Main.p_eq_np` is absent, and the publication gate is false.

The immutable scoring baseline remains M184: 160 of 162 formal artefact rows,
30 risk-weighted points, a 20-to-40-percent uncertainty range, and zero of five
global gates closed. M185 added a finite activation-coherence diagnostic row,
so its coverage was 161 of 163. It did not close a fixed checkpoint or change
the 30-percent estimate. Both reviews are recorded separately
in the canonical ledger history. M186 then makes the report-facing SAT and
locked-NAND endpoints exact concrete finite-pipeline languages, consumes the
compiled all-bitstring reduction without caller trust, and removes
`PNP.LockedNANDThreshold` from the project-axiom inventory. Those compiled
changes close exactly `reductions-final-target-compatibility` and
`axiom-remove-locked-nand-threshold`, moving the score from 30 to 32 and current
coverage to 162 of 164. M187 then makes the residual-band endpoint a concrete
encoded exact-minimum threshold predicate, proves its arbitrary typed-candidate
semantics, replaces the supplied compatibility edge with an identity reduction,
and removes `PNP.ResidualBandExactMinimization` from project-specific proof
authority. That closes exactly `axiom-remove-residual-band-minimum`, moving the
score from 32 to 33 and current coverage to 163 of 165. The uncertainty range
remains 20 to 40 percent and all five global gates remain open. M188 then makes
the PCCPack generator and checker transparent typed definitions over an explicit
loop certificate, removing `PNP.GeneratePCCPack` and
`PNP.CheckPCCPackexp` from project-specific proof authority. Those two fixed
one-point checkpoints move the score from 33 to 35 and coverage to 164 of 166.
The certificate's existence, exactness construction, polynomial runtime,
deterministic SAT theorem, and root theorem remain open; no global gate closes
and the uncertainty range remains 20 to 40 percent. No retrospective score was
invented.

## Changing the score

A future score change must change the state of a fixed checkpoint and record its
old and new state, exact compiled evidence, source coordinate or commit,
load-bearing rationale, remaining track limitations, old and new totals, and an
uncertainty-range decision. The score can decrease when evidence is invalidated,
an assumption returns, hidden exponential work is found, or a new load-bearing
obligation appears.

The following do not automatically earn points: tests, documentation, theorem or
declaration counts, publication rows, fixed instances, schedule slots,
conditional sidecars, supplied-object theorems, regenerated reports, CI work,
refactors, and external review. Polynomial-runtime points require a theorem that
bounds the complete construction uniformly in encoded source-input size.

Validate the ledger against the formal reconstruction status and compiled
theorem inventory with:

```bash
npm run formal:progress
```

The validator checks the fixed 100-point model, recomputes earned points and
formal artefact coverage independently, verifies checkpoint evidence, and rejects
conflicting gate, axiom, root-theorem, or publication states.
