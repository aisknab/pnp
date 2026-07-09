# Formal reconstruction programme

## Status

The target theorem is `P = NP`. It is **not formally established by the current repository**.

Public theorem emission is disabled. The previous activation state is superseded by
`status/FORMAL_RECONSTRUCTION_STATUS.json` and is retained only in Git history and the compatibility tombstone at
`status/ACTIVATED_PNP_STATUS.json`.

This change is mathematical, not social. Human review is welcome for bug finding and reproducibility, but it is not a premise and is not required by the formal release gate.

## Why reconstruction is required

The historical JavaScript stack checks record shape, linkage, digests, route labels, selected Boolean fields, and replay consistency. Those checks are useful for artefact integrity, but they do not prove the mathematical propositions named by assertion-bearing records.

The current Lean bridge is also incomplete as a proof of the target theorem. Its complexity witnesses, reductions, and several certificate obligations are represented by abstract handles or strings, and the bridge is parameterized by project-specific trust assumptions. A successful build therefore establishes only the stated conditional bridge in that abstract model.

## Formal release gate

The project may publish a theorem-established status only when all of the following are mechanically true:

1. A closed Lean theorem with the intended concrete statement exists.
2. Languages, machines, reductions, correctness, and running time have concrete semantics.
3. The root theorem has no PNP-specific axioms or trust parameters.
4. The dependency closure contains no `sorry`, `admit`, or equivalent placeholders.
5. The locked-NAND reduction, residual-band minimizer, ZeroSlack result, and polynomial bounds are proved in Lean.
6. The paper theorem inventory is generated from and matches the Lean environment.
7. The public status payload is generated from the formal theorem and axiom audit.

JSON booleans, hashes, JavaScript checker acceptance, release records, and test counts cannot satisfy this gate.

## Current formal obligations

The current status tracks these blocking obligations:

- `Formal.ConcreteComplexityModel`
- `Formal.ConcreteSATAndNPHardness`
- `Formal.DirectWireSemantics`
- `Formal.LockedNANDThreshold`
- `Formal.ResidualBandMinimizerCorrectness`
- `Formal.ZeroSlackCompleteness`
- `Formal.PolynomialRuntimeAndEncodingBounds`
- `Formal.ClosedRootTheoremAndAxiomAudit`

## Work order

The reconstruction order is:

1. Preserve the historical assertion-checker release without allowing it to set current theorem status.
2. Pin the Lean toolchain and formal dependencies.
3. Define concrete NAND direct-wire syntax, semantics, equivalence, size, replacement, and exact minima.
4. Build an independent exact small-model and counterexample laboratory.
5. Prove the locked-NAND threshold theorem and residual-slack bound.
6. Replace string and Boolean certificate fields with propositions and proof-bearing structures.
7. Prove the residual route, selector, blocker, ZeroSlack, exactness, and polynomial-bound theorems.
8. Construct the concrete SAT decider and prove its correctness and polynomial runtime.
9. Generate the paper and public status from the closed Lean theorem and its axiom audit.

## Verification

The current status boundary can be checked with:

```bash
npm ci
npm run proof:formal-reconstruction-status
```

The command verifies that theorem emission remains disabled, that the current and public status payloads agree, and that the historical activation payload is explicitly superseded. It does not prove `P = NP`.
