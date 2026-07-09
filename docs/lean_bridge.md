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
lean/PNP/SAT.lean
lean/PNP/LockedNAND.lean
lean/PNP/ResidualBand.lean
lean/PNP/PCCMin.lean
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

`lean/PNP/Complexity.lean` defines a witness-level model:

```text
Language
ComplexityClass
PolyTimeDecider
NondetPolyVerifier
PolyTimeManyOneReduction
PClass
NPClass
ReducesToPoly
SAT
NPComplete
StandardComplexityAxioms
```

In this model:

```text
PClass L = L has a PolyTimeDecider witness
NPClass L = L has a NondetPolyVerifier witness
ReducesToPoly A B = there is a PolyTimeManyOneReduction witness from A to B
```

The machine semantics and polynomial-bound meaning of these witness objects are still abstract handles in this pass. The closure facts, however, are no longer opaque bridge assumptions.

Lean proves:

```lean
theorem p_subset_np_witness_model {A : Language} : PClass A → NPClass A
```

by embedding a deterministic decider as a nondeterministic verifier that ignores its certificate.

Lean proves:

```lean
theorem reduction_transports_p_witness_model {A B : Language} :
    ReducesToPoly A B → PClass B → PClass A
```

by composing a reduction witness with a decider witness.

Lean then proves:

```lean
theorem np_complete_in_p_implies_p_eq_np
    {L : Language}
    (hComplete : NPComplete L)
    (hInP : PClass L) : PEqualsNP
```

The theorem uses witness-model closure theorems, not an external closure-field supplied by `CheckerTrustModel`.

`lean/PNP/SAT.lean` separates SAT-in-NP from SAT-hardness. It defines:

```lean
theorem sat_in_np_witness_model : NPClass SAT

def SATHard : Prop :=
  ∀ {A : Language}, NPClass A → ReducesToPoly A SAT

def sat_np_complete_from_hardness (hHard : SATHard) : NPComplete SAT
```

The SAT-in-NP witness remains an abstract handle in this pass; a later pass should replace it with concrete formula syntax, assignment certificates, and a polynomial verifier.

`lean/PNP/LockedNAND.lean` factors the route through the report's locked NAND threshold language:

```lean
constant LockedNANDThreshold : Language

structure LockedNANDReductionTrust where
  satReducesToLockedNAND : ReducesToPoly SAT LockedNANDThreshold

theorem sat_in_p_from_locked_nand_in_p
    (R : LockedNANDReductionTrust)
    (hLockedInP : PClass LockedNANDThreshold) : PClass SAT
```

`lean/PNP/ResidualBand.lean` factors locked NAND threshold through the report's residual-band exact-minimization theorem:

```lean
constant ResidualBandExactMinimization : Language

structure ResidualBandReductionTrust where
  lockedNANDReducesToResidualBand :
    ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization

theorem locked_nand_in_p_from_residual_band_in_p
    (R : ResidualBandReductionTrust)
    (hResidualInP : PClass ResidualBandExactMinimization) :
    PClass LockedNANDThreshold
```

`lean/PNP/PCCMin.lean` now separates the PCCMin residual-band algorithm certificate from the bare statement `ResidualBandExactMinimization ∈ P`:

```lean
structure PCCMinAlgorithmCertificate where
  algorithmName : String
  pccMinReturnsExactMinimum : String
  residualSlackBounded : String
  zeroSlackSound : String
  gainLoopDescends : String
  certificateEncodingPolynomial : String
  certificateSizePolynomial : String

theorem residual_band_in_p_from_pccmin_certificate
    (cert : PCCMinAlgorithmCertificate) :
    PClass ResidualBandExactMinimization
```

The certificate fields are digest/ledger handles in this pass. Later Lean passes should replace them by concrete proofs about the normalized gain loop, ZeroSlack, exactness, certificate size, and polynomial runtime.

This mirrors the report route:

```text
accepted package -> accepted PCCMin residual-band certificate
accepted PCCMin certificate -> residual-band exact minimization in P
locked NAND threshold reduces to residual-band exact minimization
therefore locked NAND threshold in P
SAT reduces to locked NAND threshold
therefore SAT in P
```

`lean/PNP/Bridge.lean` defines:

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

Earlier Lean passes left the following as trust-base fields:

```text
NP-complete language in P implies P = NP
P ⊆ NP
polynomial reductions transport P membership
SAT-in-NP as part of an opaque SAT NP-completeness field
accepted package directly implies SAT ∈ P
accepted package directly implies locked NAND threshold ∈ P
accepted package directly implies residual-band exact minimization ∈ P
```

The current pass keeps the first three discharged at the witness-model level, proves SAT-in-NP as a witness-model theorem, factors SAT-in-P through locked NAND threshold, factors locked-NAND-in-P through residual-band exact minimization, and factors residual-band-in-P through an explicit PCCMin algorithm certificate.

## Explicit Lean trust base after this pass

The current Lean bridge keeps the following as fields or semantic assumptions:

```text
1. Checker/reflection soundness: accepted PCCPack emits an accepted PCCMin residual-band exact-minimization certificate.
2. Semantic adequacy of PCCMinAlgorithmCertificate fields for the executable PCCMin algorithm.
3. Residual-band reduction: locked NAND threshold reduces to residual-band exact minimization.
4. Locked NAND SAT reduction: SAT reduces to the locked NAND threshold language.
5. SAT NP-hardness for the witness-model reduction relation.
6. Semantic adequacy of the witness model relative to a concrete machine model.
```

This is intentional. It makes the remaining Lean work visible instead of hiding it behind an opaque theorem.

## Next formalization targets

The next Lean passes should discharge the remaining trust-base fields one by one:

```text
1. Replace PCCMinAlgorithmCertificate string handles with concrete ZeroSlack and PCCMin proof objects.
2. Replace witness handles with concrete machine syntax and polynomial-bound semantics.
3. Formalize SAT NP-hardness for those concrete definitions or import it from a trusted math library.
4. Formalize the locked-NAND SAT threshold theorem.
5. Formalize the residual-band exact minimization theorem boundary.
6. Formalize or independently verify the PCC checker soundness theorem.
```

A passing Lean bridge is therefore a real formal artifact, but it is a bridge artifact, not yet a complete Lean reproof of every theorem in the report.
