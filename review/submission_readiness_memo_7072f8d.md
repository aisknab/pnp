# Submission Readiness Memo: 7072f8d Residual-Hardened PNP Release

Status: **external-review-ready release candidate**.

This memo separates what is frozen, what is ready to send to reviewers, what remains mathematically risky, and what must happen before this should be represented as a serious Clay-prize submission candidate.

## Public theorem boundary

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

The release is intentionally framed as a checker-gated theorem boundary. The public `P = NP` conclusion must not be represented as independent of the accepted generated-package, replay, final-certificate, release-gate, and proof-report chain.

## Frozen release identifiers

```text
source commit:
7072f8d0bda6d44d240f9bb3fad624fd357e1278

source tag:
final-pnp-proof-report-hardened-7072f8d

artifact JSON commit:
9526d5de8bdfc3f6f9d3d462044db18ba306cf2f

sealed artifact commit:
9d1de19f827e5cb6880741352eb2349cbbb45994

sealed artifact tag:
final-pnp-proof-report-artifacts-hardened-7072f8d-sealed

canonical document commit:
3ba356c79b545d2c734283bf10d85d0710de2b60

canonical document tag:
final-pnp-proof-report-docs-hardened-7072f8d-sealed

external review package commit:
02c265ab92c0e3d2b1244cffbde3715c8539e1b5

artifact bundle:
proof-artifacts/final-pnp-proof-report-hardened-7072f8d/

validation:
1121 tests, 1121 pass, 0 fail, 0 cancelled
```

## Frozen checksum anchors

```text
release-seal.json file checksum:
03a95ff0baeb5b251577780ecbce51e9b305fb611daddee4db9b05f2621d6bc7

SHA256SUMS detached checksum:
d1da103bbf2867b656e8026b734f81b33bc61deb79dbf3a2d48a16f83e8a2356

compact proof-report summary canonical digest:
6b67a24b4139041f67c4228482d097bfe2552943d782991c75288bd5135478c0

full proof-report check-record digest:
ef07f27dcb0bd5c0b115cc7ff22109522f916859a2319265ab552ee6a6243a43

CheckPCCPackexp0 record digest:
62f688bc16c26d9400f7c3c309f266beeb8836519572dd72b3b57f5446a3f1e0
```

## Files to send first

Send reviewers this minimal packet first:

```text
canonical_proof_report.pdf
REPRODUCE.md
REVIEWER_MAP.md
review/final_external_review_cover_7072f8d.md
review/hostile_review_checklist_7072f8d.md
review/external_review_handoff_7072f8d.md
review/locked_nand_threshold_hostile_review_round1.md
review/residual_band_zeroslack_hostile_review_round1.md
```

The repository and tags are part of the packet. The PDF alone is not enough.

## Minimal reviewer reproduction command

```bash
git clone https://github.com/aisknab/pnp.git pnp-review
cd pnp-review
git fetch --tags --force

git checkout final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
BUNDLE=proof-artifacts/final-pnp-proof-report-hardened-7072f8d
sha256sum -c "$BUNDLE/SHA256SUMS"
sha256sum -c "$BUNDLE/SHA256SUMS.sha256"

git checkout final-pnp-proof-report-hardened-7072f8d
npm ci
npm run validate
```

Expected validation summary:

```text
tests 1121
pass 1121
fail 0
cancelled 0
```

## What is frozen

The following are frozen for this review round:

1. The checker-gated theorem boundary.
2. The source tag and sealed artifact tag.
3. The canonical document tag.
4. The residual-band hardening pass through Terminal MuBridge, SaturatePositive, BCELReady, BN2, BN3, BN4, BN5/PkgC, BN6, Realizer/HB closure, and ZeroSlack final closure.
5. The locked NAND threshold review surface.
6. The hostile review checklist.

Do not change these during review unless a reviewer finds a concrete defect. If a defect is found, fix it on `main`, rerun validation, reseal with a new source tag, and update the documents.

## What is not frozen as mathematically settled

The following remain review-risk until independent mathematicians have attacked them:

1. The locked NAND threshold theorem.
2. The residual-band ZeroSlack contradiction.
3. The claim that every positive residual witness routes to BCELReady or an earlier named outcome.
4. The BN2 side-tight completion and no-overclaim discipline.
5. The BN3 joint finite request-envelope realizability.
6. The BN4 activation-exact cancellation equivalence.
7. The BN5/PkgC localization and singletonization route.
8. The BN6 packet collapse and selector completeness.
9. The Realizer/HB no-circular-negative closure.
10. The final theorem-boundary discipline and absence of hidden minimization.

## Review success criteria

A review round counts as useful only if reviewers try to break the proof, not merely read it.

A useful report identifies one of:

```text
a false lemma;
a missing proof obligation;
a counterexample circuit or support;
a selector packet not represented by K2/K3/Ksp;
a positive residual-slack case that still reaches ZeroSlack;
a quotient-mode equality used constructively in full mode;
a hidden minimization call;
a stale proof reference;
an accepted tamper fixture that should reject;
a public P = NP conclusion before the accepted package/replay/certificate boundary.
```

Reviewers should report issues in this format:

```text
claim attacked:
file / theorem / checker:
minimal counterexample or missing obligation:
expected acceptance behavior:
actual acceptance behavior:
suggested patch:
```

## Suggested reviewer roles

Use at least five independent review roles:

1. **Complexity theorist:** SAT reduction, final implication, theorem boundary.
2. **Circuit complexity / Boolean functions reviewer:** locked NAND threshold and macro truth signatures.
3. **Proof engineer / formal methods reviewer:** proof DAG, reflection, no-hidden-minimization, artifact replay.
4. **Combinatorics reviewer:** V53/V54, BN2-BN6, selector packet collapse.
5. **Adversarial software reviewer:** tamper fixtures, hash-as-index discipline, canonical bytes, checksum seal.

A stronger round would add:

6. **Category/rewriting systems reviewer:** direct-wire rewrite families, terminal bridge, saturation, full/quotient firewall.
7. **Independent reproducibility reviewer:** fresh clone, clean machine, tag verification, validation, artifact checksums.

## Immediate send order

Send in this order:

1. `review/final_external_review_cover_7072f8d.md`
2. `review/hostile_review_checklist_7072f8d.md`
3. `REPRODUCE.md`
4. `REVIEWER_MAP.md`
5. `canonical_proof_report.pdf`
6. Repository tags:
   - `final-pnp-proof-report-hardened-7072f8d`
   - `final-pnp-proof-report-artifacts-hardened-7072f8d-sealed`
   - `final-pnp-proof-report-docs-hardened-7072f8d-sealed`

## Triage policy

When a reviewer reports an issue:

1. Classify it as `counterexample`, `missing obligation`, `checker bug`, `documentation ambiguity`, or `reproduction issue`.
2. If it is a counterexample or missing obligation, do not argue from the release seal. Patch the math/checker or mark the proof invalid.
3. If it is a checker bug, add a failing tamper test first, then patch the checker.
4. If it is documentation ambiguity, patch the manuscript and reviewer map.
5. If it is a reproduction issue, patch `REPRODUCE.md` and rerun the consistency gate.

Any substantive patch invalidates the frozen review round and requires a new source tag, new artifacts, new document tag, and new cover note.

## Clay-prize readiness position

This release is **not yet something to call Clay-prize-ready** in public language. It is a serious external-review candidate. The next milestone is independent hostile mathematical review. Before any formal prize-oriented submission, check the current Clay Mathematics Institute rules and submission expectations directly, then prepare a public manuscript/repository package that reflects those requirements.

## One-sentence status

The 7072f8d release is sealed, validated, documented, and ready to send to hostile external reviewers; the main remaining risk is mathematical correctness under independent attack.

