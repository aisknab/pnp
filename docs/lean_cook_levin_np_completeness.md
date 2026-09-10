# Concrete CNF-SAT NP-completeness (M231)

M231 proves concrete CNF-SAT NP-hardness and the closed theorem `NPComplete CNFSAT`. It uses M230's complete all-input finite-machine Cook-Levin formula builder and exact polynomial reduction, together with the existing concrete NP verifier. This closes only the fixed two-point concrete NP-hardness checkpoint. Deterministic SAT, unconditional ZeroSlack, full polynomial PCCMin and the eligible root theorem remain open.

Formal artefact coverage: 207 of 209 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Exact theorem boundary

`PNP.Concrete.CookLevin.cnfSAT_np_hard` proves:

```lean
(source : Language) → InNP source → ReducesTo source CNFSAT
```

`PNP.Concrete.CookLevin.cnfSAT_np_complete` proves the closed proposition:

```lean
NPComplete CNFSAT
```

The hardness proof extracts a polynomial-time verifier from membership in the
concrete bounded-certificate NP class. It applies M230's complete
`polynomialReduction` to that verifier; no polynomial reduction, accepting
certificate, execution trace or correctness proof is supplied by the caller.
The existing `FinalUniversalDesign.cnfSATInNP` closes the membership half.
Both theorem closures contain exactly the permitted Lean standard axioms
`Classical.choice`, `Quot.sound` and `propext`. No project axiom is used.

The manuscript anchor is the concrete Cook-Levin/NP-completeness dependency
feeding the SAT-to-locked-NAND route, under the immutable document identity in
[the archive manifest](../archive/legacy-v0/ARCHIVE.json). The reconstruction
plan and remaining downstream blockers are recorded in
[the M231 plan](plans/2026-09-11-concrete-cnf-sat-np-completeness.md).

## Score and remaining obligations

Only `reductions-concrete-np-hardness` changes from open to earned, for its
existing two points. The canonical [progress ledger](../status/PROOF_PROGRESS.json)
records the compiled declarations, coordinate, rationale, old/new score and
unchanged uncertainty range. M230's three-point complete-builder transition
remains a separate historical entry. All fixed weights are unchanged.

NP-completeness does not put SAT in P. The deterministic SAT algorithm,
unconditional terminal-derived residual construction, ZeroSlack, complete
polynomial PCCMin and encoded certificate bounds, and eligible root theorem
remain unproved. The separate final `root-complexity-transport` checkpoint is
not double-counted. The five global gates remain open, the compiled project-axiom
inventory is empty, `PNP.Main.p_eq_np` is absent, and the publication gate is false.
The weighted estimate is not a probability of correctness or a delivery estimate.

## Verification interface

- [Lean source](../lean/PNP/Concrete/CookLevinNPCompleteness.lean)
- [Root-import axiom audit](../lean-audit/PNPConcreteCookLevinNPCompletenessAxiomAudit.lean)
- [Unbounded regressions](../lean-regression/PNPConcreteCookLevinNPCompleteness.lean)
- [Positive and hostile publication tests](../audits/lean-concrete-cook-levin-np-completeness0.test.mjs)
- [Compiled inventory](../status/LEAN_THEOREM_INVENTORY.json)
- [Reviewed publication map](../publication/FORMAL_PUBLICATION_MAP.json)

Run the targeted `npm run audit:m231` contract and the ordinary formal
status, progress, publication, root and axiom checks under the repository's
verification ownership policy. Publication consumes the exact verified core
artifacts; it does not compile the same proof again in PNPLabs.
