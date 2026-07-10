# Lean bridge formalization

This directory contains the Lean formalization track for the PNP proof-certificate stack.

The current Lean development contains a conditional theorem bridge corresponding to the report:

```text
CheckPCCPackexp(GeneratePCCPack()) = accept => P = NP
```

That bridge still depends on five project-specific axioms and does **not** constitute a Lean proof of
`P = NP`. It is also not a complete Lean reproof of the custom JavaScript checker, the full
residual-slack package, the complete SAT reduction, or the concrete machine-complexity model. The
purpose of the Lean track is to replace each trust-base item with a checked theorem in visible
stages.

## Build

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPBridgeAxiomAudit.lean
```

The GitHub workflow `.github/workflows/lean-bridge.yml` verifies a checksum-pinned Elan 4.2.3
archive, installs the exact `leanprover/lean4:v4.31.0` toolchain, builds the explicit `PNP` root, and
prints the axiom dependencies of both the root-status declarations and conditional bridge.

## Files

```text
lean-toolchain
lakefile.lean
lean/PNP.lean
lean/PNP/Main.lean
lean/PNP/Complexity.lean
lean/PNP/SAT.lean
lean/PNP/LockedNANDMacros.lean
lean/PNP/LockedNANDPrefix.lean
lean/PNP/LockedNAND.lean
lean/PNP/ResidualBand.lean
lean/PNP/ZeroSlack.lean
lean/PNP/PCCMin.lean
lean/PNP/Bridge.lean
lean-audit/PNPBridgeAxiomAudit.lean
docs/lean_locked_nand_macros.md
docs/lean_locked_nand_prefix.md
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

## Root status

`lean/PNP/Main.lean` exposes `PNP.Main.rootTheoremStatus`, an assumption-free structure recording
that formal reconstruction is in progress, external assumptions remain, and no public theorem has
been released. There is deliberately no declaration named `PNP.Main.p_eq_np` in the current root.
Building this status is evidence that the complete import root compiles; the status is not a theorem
of `P = NP`.

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

## Concrete locked-NAND prefix layer

`lean/PNP/LockedNANDPrefix.lean` formalizes the report's two-gate prefix-conjunction node and the complete conjunction of a supplied check list.

It proves:

```lean
theorem prefixAndMacro_neg_spec (a b : Bool) :
    (prefixAndMacro a b).neg = !(a && b)

theorem prefixAndMacro_out_spec (a b : Bool) :
    (prefixAndMacro a b).out = (a && b)

theorem prefixConjunction_spec (checks : List Bool) :
    prefixConjunction checks = allChecks checks

theorem prefixConjunction_eq_true_iff (checks : List Bool) :
    prefixConjunction checks = true ↔
      ∀ b ∈ checks, b = true
```

For a nonempty list with `n` checks, Lean also proves that the construction has `n - 1` prefix nodes and exactly `2(n - 1)` NAND gates. The two exposed outputs of a prefix node are checked to be distinct, nonconstant, and nonprojection.

These results are assembled into:

```lean
def lockedNANDPrefixCertificate : LockedNANDPrefixCertificate
```

See `docs/lean_locked_nand_prefix.md` for the exact scope.

## Global locked-NAND layer

`lean/PNP/LockedNAND.lean` keeps the full SAT builder and threshold theorem abstract:

```lean
axiom LockedNANDThreshold : Language

structure LockedNANDReductionTrust where
  satReducesToLockedNAND : ReducesToPoly SAT LockedNANDThreshold
```

The local macro truth laws and supplied-list prefix exactness are no longer part of that trust object. Remaining global work includes constructing the exact global distinguished-check list, carrier freshness, cross-instance separation, global baseline exactness, trace equivalence, final-lock lower bounds, the polynomial builder, the threshold equivalence, and the residual-slack-at-most-four theorem.

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

The source audit permits exactly these five project-specific axioms in the current root closure:

```text
PNP.SAT
PNP.LockedNANDThreshold
PNP.ResidualBandExactMinimization
PNP.GeneratePCCPack
PNP.CheckPCCPackexp
```

`lean-audit/PNPBridgeAxiomAudit.lean` confirms that the root-status declarations depend on no axioms
and prints those project assumptions (along with Lean's logical infrastructure dependencies) for
the conditional bridge. The audit fails closed if another `axiom`, a `constant`/`opaque`
declaration, or a `sorry`/`admit` placeholder appears in the tracked root closure.

## Discharged by Lean so far

```text
1. P is a subset of NP in the witness model.
2. Polynomial reductions transport P membership in the witness model.
3. An NP-complete language in P implies P = NP.
4. SAT-in-NP plus SAT hardness gives SAT NP-completeness.
5. The displayed local locked-NAND macro Boolean identities.
6. Single-instance macro output distinctness and nonconstant/nonprojection checks.
7. The two-gate prefix conjunction semantics.
8. Exact supplied-list prefix coverage and the true-iff-all-checks theorem.
9. The exact 2(n-1) prefix gate count for nonempty check lists.
10. Prefix-node exposed-output distinctness and nonconstant/nonprojection checks.
11. Conditional composition from PCCMin through residual band, locked NAND, SAT, and the witness-model equality proposition, assuming the disclosed project axioms.
```

## Explicit trust base after this pass

```text
1. Checker/reflection soundness: accepted PCCPack emits a semantically valid structured PCCMin loop certificate.
2. Semantic adequacy of the PCCMin and ZeroSlack certificate fields.
3. The locked-NAND-to-residual-band reduction theorem.
4. The global SAT-to-locked-NAND builder and threshold theorem beyond the checked local macro and prefix semantics.
5. SAT NP-hardness for concrete complexity definitions.
6. Semantic adequacy of the witness model relative to a concrete machine model.
```

## Next formalization targets

The highest-value next targets are:

```text
1. Construct the exact global distinguished-check list and prove each required check appears exactly once.
2. Formalize cross-instance locked-NAND freshness and baseline distinctness.
3. Formalize the direct-wire output lower bound and baseline gate count.
4. Formalize trace equivalence and the locked threshold theorem.
5. Replace key ZeroSlack string handles with propositions and prove the contradiction chain.
6. Replace witness handles with concrete machine syntax and polynomial-bound semantics.
7. Formalize or import SAT NP-hardness for those definitions.
8. Formalize checker/reflection soundness for the PCC package.
```

A passing Lean build is a real checked artifact. At this stage it checks an assumption-free status
declaration, local results, and an explicitly assumption-bearing conditional bridge. It is not a
root theorem or an independent Lean proof of the report's conclusion.
