# Lean bridge formalization

This directory is the first Lean formalization pass for the PNP proof-certificate stack.

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

`lean/PNP/Bridge.lean` defines abstract versions of:

```text
Language
PClass
NPClass
SAT
NPComplete
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

## Explicit Lean trust base

The current Lean bridge keeps the following as fields of `CheckerTrustModel`:

```text
1. Checker soundness: accepted PCCPack implies SAT ∈ P.
2. SAT NP-completeness.
3. Complexity implication: an NP-complete language in P implies P = NP.
4. Concrete machine-model definitions of P, NP, SAT, and polynomial reduction.
```

This is intentional. It makes the remaining Lean work visible instead of hiding it behind an opaque theorem.

## Next formalization targets

The next Lean passes should discharge the trust-base fields one by one:

```text
1. Replace abstract PClass/NPClass/SAT/ReducesToPoly with concrete definitions.
2. Formalize the standard SAT NP-completeness implication or import it from a trusted math library.
3. Formalize the locked-NAND SAT threshold theorem.
4. Formalize the residual-band exact minimization theorem boundary.
5. Formalize or independently verify the PCC checker soundness theorem.
```

A passing Lean bridge is therefore a real formal artifact, but it is a bridge artifact, not yet a complete Lean reproof of every theorem in the report.
