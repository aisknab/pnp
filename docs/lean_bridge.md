# Lean bridge formalization

This directory contains the Lean formalization track for the PNP proof-certificate stack.

The current Lean development formalizes the theorem bridge stated by the report:

```text
CheckPCCPackexp(GeneratePCCPack()) = accept => P = NP
```

It does **not** yet constitute a complete Lean reproof of the custom JavaScript checker, the full residual-slack package, the complete SAT reduction, or the concrete machine-complexity model. The explicit purpose of the Lean track is to replace each trust-base item with a checked theorem in visible stages.

## Build

```bash
lake build
```

The GitHub workflow `.github/workflows/lean-bridge.yml` installs Lean through `elan` and runs the build.

## Files

```text
lean-toolchain
lakefile.lean
lean/PNP.lean
lean/PNP/Complexity.lean
lean/PNP/SAT.lean
lean/PNP/LockedNANDMacros.lean
lean/PNP/LockedNAND.lean
lean/PNP/ResidualBand.lean
lean/PNP/ZeroSlack.lean
lean/PNP/PCCMin.lean
lean/PNP/Bridge.lean
docs/lean_locked_nand_macros.md
```

## Complexity bridge

`lean/PNP/Complexity.lean` defines the witness-level objects:

```text
Language
PolyTimeDecider
NondetPolyVerifier
PolyTimeManyOneReduction
PClass
NPClass
ReducesToPoly
NPComplete
```

and proves:

```lean
theorem p_subset_np_witness_model {A : Language} :
    PClass A → NPClass A

theorem reduction_transports_p_witness_model {A B : Language} :
    ReducesToPoly A B → PClass B → PClass A

theorem np_complete_in_p_implies_p_eq_np
    {L : Language}
    (hComplete : NPComplete L)
    (hInP : PClass L) : PEqualsNP
```

The witness objects still use abstract code handles. Concrete machine syntax, semantics, and polynomial bounds remain future work.

## SAT layer

`lean/PNP/SAT.lean` separates SAT membership in NP from SAT hardness:

```lean
theorem sat_in_np_witness_model : NPClass SAT

def SATHard : Prop :=
  ∀ {A : Language}, NPClass A → ReducesToPoly A SAT

def sat_np_complete_from_hardness (hHard : SATHard) : NPComplete SAT
```

The SAT verifier is still an abstract witness handle in this pass.

## Concrete locked-NAND macro layer

`lean/PNP/LockedNANDMacros.lean` is a concrete Boolean formalization of the report's local macros.

It defines every displayed gate for:

```text
M=  equality macro
M1  constant-one macro
M0  constant-zero macro
MN  NAND trace-check macro
four-gate final conjunction
```

Lean proves the distinguished-output identities by exhaustive Boolean case analysis:

```lean
(equalityMacro r u s).a8 = r && boolEq u s
(constantOneMacro r u).b2 = r && u
(constantZeroMacro r u).d3 = r && !u
(traceMacro l t u v).q16 = l && boolEq t (boolNand u v)
finalConjunction4 z t y = z && t && y
```

Lean also computes every exposed single-instance truth signature and checks that:

```text
10 equality outputs are pairwise distinct
2 constant-one outputs are pairwise distinct
3 constant-zero outputs are pairwise distinct
18 trace outputs are pairwise distinct
all exposed outputs are nonconstant
all exposed outputs differ from every positive projection
```

These results are assembled into:

```lean
def lockedNANDMacroCertificate : LockedNANDMacroCertificate
```

See `docs/lean_locked_nand_macros.md` for the exact scope.

## Global locked-NAND layer

`lean/PNP/LockedNAND.lean` keeps the full SAT builder and threshold theorem abstract:

```lean
constant LockedNANDThreshold : Language

structure LockedNANDReductionTrust where
  satReducesToLockedNAND : ReducesToPoly SAT LockedNANDThreshold
```

The local macro truth laws are no longer part of that trust object. Remaining global work includes carrier freshness, cross-instance separation, prefix coverage, baseline exactness, trace equivalence, final-lock lower bounds, the polynomial builder, the threshold equivalence, and the residual-slack-at-most-four theorem.

## Residual-band, ZeroSlack, and PCCMin layers

`lean/PNP/ResidualBand.lean` factors locked-NAND threshold through residual-band exact minimization:

```lean
structure ResidualBandReductionTrust where
  lockedNANDReducesToResidualBand :
    ReducesToPoly LockedNANDThreshold ResidualBandExactMinimization
```

`lean/PNP/ZeroSlack.lean` exposes structured certificate boundaries for:

```text
HResolveSidecarCertificate
BudgetSidecarCertificate
SelectorSilenceCertificate
HBClosureCertificate
BCELContradictionCertificate
ZeroSlackCertificate
PCCOracleCertificate
```

`lean/PNP/PCCMin.lean` exposes the structured loop certificate and constructs the witness-model residual-band decider from it.

Most fields in these certificate objects are still digest/ledger handles. Replacing those handles by actual propositions and proofs is a major remaining task.

## Final bridge

`lean/PNP/Bridge.lean` proves:

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

The current route is:

```text
accepted PCC package
-> structured PCCMin/ZeroSlack certificate
-> residual-band exact minimization in P
-> locked NAND threshold in P
-> SAT in P
-> P = NP
```

## Discharged by Lean so far

```text
1. P is a subset of NP in the witness model.
2. Polynomial reductions transport P membership in the witness model.
3. An NP-complete language in P implies P = NP.
4. SAT-in-NP plus SAT hardness gives SAT NP-completeness.
5. The displayed local locked-NAND macro Boolean identities.
6. Single-instance macro output distinctness and nonconstant/nonprojection checks.
7. The abstract bridge composition from PCCMin through residual band, locked NAND, SAT, and P = NP.
```

## Explicit trust base after this pass

```text
1. Checker/reflection soundness: accepted PCCPack emits a semantically valid structured PCCMin loop certificate.
2. Semantic adequacy of the PCCMin and ZeroSlack certificate fields.
3. The locked-NAND-to-residual-band reduction theorem.
4. The global SAT-to-locked-NAND builder and threshold theorem beyond the checked local macros.
5. SAT NP-hardness for concrete complexity definitions.
6. Semantic adequacy of the witness model relative to a concrete machine model.
```

## Next formalization targets

The highest-value next targets are:

```text
1. Replace key ZeroSlack string handles with propositions and prove the contradiction chain.
2. Formalize cross-instance locked-NAND freshness and baseline distinctness.
3. Formalize trace equivalence and the locked threshold theorem.
4. Replace witness handles with concrete machine syntax and polynomial-bound semantics.
5. Formalize or import SAT NP-hardness for those definitions.
6. Formalize checker/reflection soundness for the PCC package.
```

A passing Lean build is a real checked artifact. At this stage it is a narrowing formal bridge, not yet a complete independent Lean proof of every report theorem.
