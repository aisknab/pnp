# External Review Handoff: Hardened 8b45da4 PNP Proof-Report Release

Status: **ready for hostile external review package handoff**.

This note is a cover sheet for reviewers. It is not a substitute for mathematical review. Its purpose is to give reviewers a deterministic path through the repository, the proof-report artefacts, and the specific theorem blocks that should be attacked first.

## Public theorem boundary

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

The release asserts the final theorem under the explicit checker/package acceptance boundary. Reviewers should verify that no public `P = NP` conclusion is emitted before the accepted generated-package antecedent and accepted final proof-report path.

## Canonical release identifiers

```text
source commit:
8b45da4ed604a709d244c35acb886c5eee0889cd

source tag:
final-pnp-proof-report-hardened-8b45da4

artifact JSON commit:
c3d3915f7c37737924377076b9216efd2233037f

sealed artifact tag:
final-pnp-proof-report-artifacts-hardened-8b45da4-sealed

sealed artifact commit:
88287409389111d3a3c69a396223a4f050e6fa12

canonical document commit:
c51db5bbe74ef7e8628c1dc46522d9d9cd34f7d2

canonical document tag:
final-pnp-proof-report-docs-hardened-8b45da4-c51db5b

validation:
1043 tests, 1043 pass, 0 fail, 0 cancelled
```

## Primary files for reviewers

```text
canonical_proof_report.pdf
canonical_proof_report.tex
REPRODUCE.md
REVIEWER_MAP.md

proof-artifacts/final-pnp-proof-report-hardened-8b45da4/release-seal.json
proof-artifacts/final-pnp-proof-report-hardened-8b45da4/SHA256SUMS
proof-artifacts/final-pnp-proof-report-hardened-8b45da4/SHA256SUMS.sha256

review/locked_nand_threshold_hostile_review_round1.md
review/residual_band_zeroslack_hostile_review_round1.md
```

## Minimal reproduction commands

```bash
git clone https://github.com/aisknab/pnp.git pnp-review
cd pnp-review
git fetch --tags --force

git checkout final-pnp-proof-report-artifacts-hardened-8b45da4-sealed
BUNDLE=proof-artifacts/final-pnp-proof-report-hardened-8b45da4
sha256sum -c "$BUNDLE/SHA256SUMS"
sha256sum -c "$BUNDLE/SHA256SUMS.sha256"

git checkout final-pnp-proof-report-hardened-8b45da4
npm ci
npm run validate
```

Expected validation summary:

```text
tests 1043
pass 1043
fail 0
cancelled 0
```

## Reviewer assignment

A hostile review should proceed in this order.

### 1. Locked NAND threshold

This round has already been made more explicit in the manuscript and GPack checker fields. Reviewers should still attack:

```text
DirectWireOutputLowerBound
MacroDistinct
TraceEquivalence
ZeroOutputConvention
FinalLockSeparation
```

The main question is whether the locked NAND word really satisfies:

```text
φ ∉ SAT  => μ(W^NAND_φ) = B^NAND_φ
φ ∈ SAT  => B^NAND_φ + 1 ≤ μ(W^NAND_φ) ≤ B^NAND_φ + 4
```

### 2. Residual-band minimization and ZeroSlack

This is the next highest-risk mathematical layer. Reviewers should attack whether the proof of polynomial residual-band exact minimization is actually complete:

```text
Λ(C0) ≤ O(log |C0|)
=> PCCMin_exp(C0) returns an exact minimum equivalent circuit in polynomial time.
```

The audit target is the route:

```text
NormalizeOrGain
=> PCCOracle
=> HResolve / BudgetResolve / selector search
=> ZeroSlack
=> residual-band minimization
```

### 3. Final package-to-public-theorem route

Reviewers should verify that the final route is conditional, accepted, and replayable:

```text
CheckPCCPackexp0
CheckAcceptRun0
ReplayAcceptRun0
EmitFinalVerdict0
CheckFinalPNPCertificate0
CheckFinalPNPReleaseGate0
CheckFinalPNPProofReport0
```

## What a reviewer should try to break

1. Find a positive residual-slack circuit that reaches `ZeroSlack` incorrectly.
2. Find a cheaper same-frontier replacement excluded by the finite selector universe.
3. Find a quotient-mode equality used constructively in full mode.
4. Find an uncharged materializer or duplicated charge owner.
5. Find a hidden exact-minimization oracle in executable position.
6. Find a stale proof-reference path where a theorem citation does not resolve to an accepted proof node.
7. Find a public theorem emission before accepted package/replay/certificate linkage.

## Expected communication format

A useful reviewer report should include:

```text
claim attacked:
file / theorem / checker:
minimal counterexample or missing obligation:
expected acceptance behavior:
actual acceptance behavior:
suggested patch:
```

For mathematical gaps, the best report is a concrete lemma that is missing, false, or insufficiently justified. For executable gaps, the best report is a minimal tamper fixture that should reject but accepts.
