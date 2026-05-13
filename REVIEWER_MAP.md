# Reviewer Map for the Hardened Final PNP Proof-Report Release

This map is intended for hostile external review. It tells a reviewer where each major theorem claim is represented in the manuscript and in the executable proof-report stack.

## Public claim

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

The release does not ask a reviewer to accept a direct unqualified `P = NP` claim before package acceptance. The public theorem is conditional on the accepted generated package.

## Canonical release facts

```text
source commit:
7072f8d0bda6d44d240f9bb3fad624fd357e1278

source tag:
final-pnp-proof-report-hardened-7072f8d

sealed artifact tag:
final-pnp-proof-report-artifacts-hardened-7072f8d-sealed

artifact bundle:
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/

validation:
1121 tests, 1121 pass, 0 fail
```

The hardened release seal is:

```text
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/release-seal.json
```

## Main review chain

The proof stack should be read in this order.

### 1. Locked NAND threshold

Mathematical role:

```text
SAT instance φ
→ locked NAND word W^NAND_φ
→ baseline B^NAND_φ
→ φ ∈ SAT iff μ(W^NAND_φ) > B^NAND_φ
→ residual slack ≤ 4
```

Executable surfaces:

```text
pcc-gpack0.mjs
test/pcc-gpack0.test.mjs
```

Key checker facts:

```text
CheckGPack0
CheckRowFamG0
BaselineDerivation0
TraceDerivation0
ThresholdDerivation0
G.BaselineCert.proof
G.TraceCert.proof
G.ThresholdCert.proof
```

Reviewer attacks:

```text
- Does BaselineDistinct really imply the stated lower bound?
- Does trace coherence prove the exact NAND trace equivalence?
- Does G.ThresholdCert.proof depend on the baseline and trace proof nodes?
- Are proof nodes typed, non-opaque, and acyclic?
- Is residual slack bounded by 4 without hidden minimization?
```

### 2. Global proof DAG linkage

Mathematical role:

```text
G.ThresholdCert.proof
→ Package.G.LockedNANDThreshold
→ Final.AcceptedPackageImpliesSATinP
```

Executable surfaces:

```text
pcc-global-proof-dag0.mjs
test/pcc-global-proof-dag0.test.mjs
```

Key checker facts:

```text
CheckGlobalProofDAG0
GlobalGLockedNANDProofs0NF
Package.G.LockedNANDThreshold depends on G.ThresholdCert.proof
Final.AcceptedPackageImpliesSATinP depends on Package.G.LockedNANDThreshold
```

Reviewer attacks:

```text
- Can Package.G.LockedNANDThreshold be accepted without G.ThresholdCert.proof?
- Can the final SAT-in-P theorem be accepted without Package.G.LockedNANDThreshold?
- Are opaque proof materials rejected?
- Are premise edges earlier, typed, and acyclic?
```

### 3. Final integration

Mathematical role:

```text
accepted GPack
+ accepted GlobalProofDAG
+ final framework match
+ SAT decision rule
+ polynomial bounds
→ final integration accepted
```

Executable surfaces:

```text
pcc-final-framework0.mjs
test/pcc-final-framework0.test.mjs
```

Key checker facts:

```text
CheckFinalIntegration0
CheckGlobalProofDAG0
FinalIntegrationGlobalGLinkage0NF
SATDecision.LockedWord.gpackDigest = accepted GPack digest
FinalMatch.PG.gpackDigest = accepted GPack digest
```

Reviewer attacks:

```text
- Can SATDecision drift from the accepted GPack?
- Can FinalMatch drift from the accepted GPack?
- Can GlobalProofDAG omit G.ThresholdCert.proof?
- Can FinalIntegration accept without global G linkage?
```

### 4. Final theorem

Mathematical role:

```text
accepted final integration
+ SAT ∈ P implication
+ SAT NP-complete
→ P = NP
```

Executable surfaces:

```text
pcc-final0.mjs
test/pcc-final0.test.mjs
```

Key checker facts:

```text
CheckFinal0
FinalTheoremGLinkage0NF
PCCMinBridge cites:
  ResidualBandExactMinimization
  LockedNANDThreshold
  GlobalProofDAG.Package.G.LockedNANDThreshold
  G.ThresholdCert.proof
  SATDecision
AcceptedPackageImpliesSATinP assumptions cite:
  CheckPCCPackexp(P)=accept
  CheckGPack0(GPack)=accept
  CheckGlobalProofDAG0(GlobalProofDAG)=accept
  CheckFinalIntegration0(FinalIntPack)=accept
  Package.G.LockedNANDThreshold
  G.ThresholdCert.proof
  Lambda(WNAND_phi)<=4
```

Reviewer attacks:

```text
- Can SAT-in-P be derived without the G locked NAND threshold?
- Can the final theorem accept if the final integration digest drifts?
- Can the public theorem claim P = NP before package acceptance?
```

### 5. Concrete package coverage

Mathematical role:

```text
materialized PCCPack
→ concrete coverage confirms every required checker/linkage field
→ CheckPCCPackexp0 accepts only if final G proof-chain coverage is complete
```

Executable surfaces:

```text
pcc-final-integration-concrete-materialized0.mjs
pcc-pack-concrete-materialized0.mjs
pcc-check-pcc-pack-exp0.mjs
test/pcc-final-integration-concrete-materialized0.test.mjs
test/pcc-pack-concrete-materialized0.test.mjs
test/pcc-check-pcc-pack-exp0.test.mjs
```

Key required coverage fields:

```text
globalProofDAGHasGThresholdProofNode
globalProofDAGPackageGDependsOnGThresholdProof
globalProofDAGFinalSATinPDependsOnPackageG
finalIntegrationGlobalGLinkageComplete
finalTheoremGLinkageComplete
finalTheoremUsesGlobalGThreshold
finalTheoremUsesGThresholdProofRef
finalTheoremUsesFinalIntegrationGlobalGLinkage
```

Reviewer attacks:

```text
- Can CheckPCCPackexp0 accept if finalTheoremGLinkageComplete is false?
- Can CheckPCCPackexp0 accept if GlobalProofDAG lacks G.ThresholdCert.proof?
- Can concrete coverage be stale relative to recomputed coverage?
```

### 6. RunAll acceptance route

Mathematical role:

```text
integrated pipeline
+ accepted CheckPCCPackexp0
+ accepted public conclusion boundary
→ public status complete
```

Executable surfaces:

```text
pcc-runall0.mjs
test/pcc-runall0.test.mjs
```

Key checker facts:

```text
RunAll0 includes CheckPCCPackexp0 in checker coverage.
RunAll0 executes CheckPCCPackexp0.
RunAll0 rejects if CheckPCCPackexp0 final G proof-chain coverage is missing.
RunAll0 public conclusion remains conditional.
```

Reviewer attacks:

```text
- Can RunAll0 emit public conclusion without CheckPCCPackexp0?
- Can RunAll0 accept if CheckPCCPackexp0 rejects?
- Can RunAll0 accept if final theorem G linkage is missing?
```

## Reviewer priority list

A hostile review should focus in this order:

1. Locked NAND threshold: mathematical correctness of BaselineDistinct, trace coherence, and threshold equivalence.
2. Residual-band exact minimization: whether residual slack ≤ 4 really makes exact minimization polynomial under the stated model.
3. No-hidden-minimization discipline: whether exact minimization is only used as a theorem target, not an executable oracle.
4. Proof-ref soundness: whether proof nodes are typed, acyclic, and non-opaque across GPack, RowFamG, GlobalProofDAG, FinalIntegration, Final0, and CheckPCCPackexp0.
5. Public theorem boundary: whether the release ever claims P = NP before the accepted generated-package antecedent.

## Minimal reviewer commands

```bash
npm ci
npm run validate

sha256sum -c proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS
sha256sum -c proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS.sha256

node --test test/pcc-gpack0.test.mjs
node --test test/pcc-global-proof-dag0.test.mjs
node --test test/pcc-final-framework0.test.mjs
node --test test/pcc-final0.test.mjs
node --test test/pcc-check-pcc-pack-exp0.test.mjs
node --test test/pcc-runall0.test.mjs
```

Expected validation summary:

```text
tests 1121
pass 1121
fail 0
```
