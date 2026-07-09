# Lean bridge formalization

This directory contains the Lean formalization track for the PNP proof-certificate stack.

It does **not** claim to formalize the full custom JavaScript PCC checker, the full locked-NAND residual-slack development, or all row/package artefacts in Lean yet. Instead, it formalizes the final theorem bridge stated by the proof report:

```text
CheckPCCPackexp(GeneratePCCPack()) = accept => P = NP
```

The report states this accepted proof-report boundary and records the final theorem field as `P = NP` under the checker trust model.

## Files

```text
lean-toolchain
lakefile.lean
lean/PNP.lean
lean/PNP/Complexity.lean
lean/PNP/Bridge.lean
.github/workflows/lean-bridge.yml
```

## Build

With Lean/Lake installed:

```bash
lake build
```

The GitHub workflow `lean-bridge` installs Lean through `elan` and runs `lake build`.

## What Lean proves now

`lean/PNP/Complexity.lean` defines abstract versions of:

```text
Language
ComplexityClass
PClass
NPClass
PEqualsNP
ReducesToPoly
SAT
NPComplete
StandardComplexityAxioms
```

and proves the standard abstract implication:

```lean
theorem np_complete_in_p_implies_p_eq_np
    (H : StandardComplexityAxioms)
    {L : Language}
    (hComplete : NPComplete L)
    (hInP : PClass L) : PEqualsNP
```

The theorem uses only:

```text
P ⊆ NP
polynomial reductions transport P membership
NP-completeness of L
L ∈ P
```

`lean/PNP/Bridge.lean` then defines:

```text
PCCPack
GeneratePCCPack
CheckPCCPackexp
AcceptedGeneratedPackage
CheckerTrustModel
```

and proves:

```lean
theorem final_report_bridge
    (T : CheckerTrustModel) :
    FinalReportAntecedent → FinalReportConsequent
```

where:

```text
FinalReportAntecedent = CheckPCCPackexp GeneratePCCPack = Verdict.accept
FinalReportConsequent = PClass = NPClass
```

## What this pass discharged

The first Lean bridge kept the whole step

```text
NP-complete language in P implies P = NP
```

as a field of `CheckerTrustModel`.  This pass discharges that generic implication as a Lean theorem in `PNP.Complexity`.

## Explicit Lean trust base after this pass

The current Lean bridge keeps the following as fields or axioms:

```text
1. Checker soundness: accepted PCCPack implies SAT ∈ P.
2. SAT NP-completeness for the chosen concrete SAT/P/NP/reduction definitions.
3. Standard complexity closure facts: P ⊆ NP and polynomial reductions transport P membership.
4. Concrete machine-model definitions of P, NP, SAT, and polynomial reduction.
```

This is intentional. It makes the remaining Lean work visible instead of hiding it behind an opaque theorem.

## Next formalization targets

The next Lean passes should discharge the remaining trust-base fields one by one:

```text
1. Replace abstract PClass/NPClass/SAT/ReducesToPoly with concrete definitions.
2. Formalize SAT NP-completeness for those concrete definitions or import it from a trusted math library.
3. Formalize the locked-NAND SAT threshold theorem.
4. Formalize the residual-band exact minimization theorem boundary.
5. Formalize or independently verify the PCC checker soundness theorem.
```

A passing Lean bridge is therefore a real formal artifact, but it is a bridge artifact, not yet a complete Lean reproof of every theorem in the report.
