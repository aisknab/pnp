# Proof progress model

The project reports two independent measurements. They answer different
questions and must never be combined.

## Formal artefact coverage

Formal artefact coverage counts earned rows in the current formal publication
milestone ledger. At
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-23-184`, 160 of 162
current scoped rows are earned, or 98.8 percent of that evidence ledger.

This is not proof completion. Rows are not equal units of mathematical
difficulty, and the denominator can grow when a dependency is discovered or an
obligation is decomposed. New finite, local, conditional, or supplied-data
results can add valuable evidence without retiring a global proof obligation.

## Risk-weighted proof completion estimate

The version 0 model assigns 100 fixed points to load-bearing checkpoints:

| Track | Available | Earned at M184 |
| --- | ---: | ---: |
| Formal foundations and proof infrastructure | 15 | 13 |
| Concrete reductions and locked-NAND route | 20 | 14 |
| Unconditional residual core and ZeroSlack | 35 | 2 |
| Exact PCCMin algorithm, complexity and bounds | 20 | 1 |
| Root theorem and project-axiom elimination | 10 | 0 |
| **Total** | **100** | **30** |

The M184 risk-weighted proof completion estimate is therefore 30 percent, with
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
theorem plus axiom audit. Four project-specific axioms remain,
`PNP.Main.p_eq_np` is absent, and the publication gate is false.

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
