# M231 plan: concrete CNFSAT NP-completeness

Status: integrated kernel-checked candidate; broad core validation and release gates pending. This work starts from the verified M230 core merge
`a5e6b44e1345b5b1ca124391a5e57f02f95742dd`, tree
`48938071581c3242c612573da1f0eb2f2e3f967e`.
The prepared M230 PNPLabs source pin remains unchanged while this core work proceeds. Do not bind the website to this development branch.

## Legacy anchor and dependency edge

The pinned manuscript's introduction uses SAT NP-completeness, and its
**Final SAT decision** / **Accepted package implies P=NP** dependency requires
that transport in the selected concrete model. The exact document authority is
the document tag recorded in
[the legacy archive manifest](../../archive/legacy-v0/ARCHIVE.json).
The manuscript is construction specification and provenance, not Lean proof authority.

M230 supplies a `PolynomialReduction language CNFSAT` for every concrete
`PolynomialTimeVerifier language`. Existing
`PNP.Concrete.FinalUniversalDesign.cnfSATInNP` supplies concrete NP membership.
The missing edge is the closed `NPComplete CNFSAT` proposition, whose hardness
field quantifies over every language in the concrete bounded-certificate NP class.

## Unbounded abstraction and exact theorem types

Add these theorems in `PNP.Concrete.CookLevin`:

```lean
theorem cnfSAT_np_hard (source : Language) (sourceInNP : InNP source) :
    ReducesTo source CNFSAT

theorem cnfSAT_np_complete : NPComplete CNFSAT
```

Eliminate the verifier witness from NP membership within the propositional
reduction-existence goal and reuse the exact M230 machine. Do not weaken the
quantifier to a finite language list, assume a reduction or correctness
certificate, replace the machine, or add an axiom.

## Producer and consumer plan

| Authority changed | Consumers to reconcile before broad validation | First rejecting check |
| --- | --- | --- |
| Two public theorems and canonical root import | Module audit, unbounded regressions, closed source/audit lists and inventory name producers | Incremental module/root build, exact axiom transcript and regressions |
| Compiled theorem types and earned publication row | Publication map, status derivation, inventory probe and hostile theorem/type/axiom contracts | Focused positive and weakened/supplied-data mutations |
| Concrete NP-completeness status field | Existing false-state expectations, global blockers and progress evidence, including still-open root transport | Structured changed-field comparison and targeted status/progress tests |
| Fixed checkpoint review | Canonical ledger, history, current core docs and report | Exact checkpoint arithmetic and source-bound generated-output checks |

Keep current and historical scope separate. A completed NP-completeness
transport does not imply a deterministic polynomial-time SAT algorithm.

## Verification and scoring gates

1. Reuse the verified exact-tree M230 dependency cache. Build the new leaf first,
   then rebuild the explicit root before importing it in the permanent axiom audit.
2. Require both closed theorem types, the exact expected two-name public interface,
   only approved Lean-standard axioms and no project-specific assumptions.
3. Update all affected producers and tests before inventory extraction or a broad suite.
   Derive fingerprints and counts from compiled evidence, never choose them in advance.
4. Review the fixed `reductions-concrete-np-hardness` checkpoint, worth two points,
   only after its complete obligation is compiled and audited. Do not mechanically
   award a second checkpoint merely because the same status field changed.
   The exact final SAT theorem, eligible root linkage and publication gate remain
   separate obligations.
5. Run required core validation, exact-source reproduction, normal PR checks and
   guarded manual merge. Only verified earning may change canonical progress.
6. If earned, publish M230 and M231 in one PNPLabs batch from the exact verified
   M231 core merge. Keep the prepared site source pin unchanged until that merge;
   never mix an unmerged core source into a public release.

Starting earned baseline (M230): risk-weighted proof estimate 38%, uncertainty
20% to 40%; formal artefact coverage 206 of 208; global gates closed 0 of 5.
Project-specific axioms remaining: 0. Eligible root `PNP.Main.p_eq_np`: absent.
Publication gate: false.

Residual terminal-input derivation, complete decreasing route coverage,
unconditional SaturatePositive, BCELReady and ZeroSlack, executable exact PCCMin
and its complete polynomial bounds, deterministic CNFSAT in P and the eligible
root theorem remain downstream.

## Integration review, 2026-09-11

The new leaf and explicit root build, both exact axiom audits and all four
unbounded regressions passed. The two theorem closures use only the existing
Lean standard axioms Classical.choice, Quot.sound and propext. Three initial
source-interface and hostile-mutation tests passed. This is not full milestone
release evidence, and canonical progress has not yet changed.

The exact M230 PDF still contains a cover statement that there is no complete
raw polynomial-time Cook-Levin builder, while its M230 body correctly records
that construction. Hold the standalone M230 website deployment. Correct the
mutable report template and enforce a current-summary regression in M231, then
publish the two related milestones in one source-bound website batch. Preserve
the M230 commit and its historical report bytes. The prepared site work is
retained; the stopped broad site audit is not a green release result.

## Canonical integration and verification evidence

Both compiled types now have reviewed publication fingerprints. The fixed
two-point hardness checkpoint is earned in the candidate ledger, moving the
risk-weighted estimate from 38% to 40%, with the uncertainty range unchanged
at 20% to 40%. Formal artefact coverage is 207 of 209 current scoped rows.
Global gates closed: 0 of 5. No project-specific axiom or root theorem is added.
The separate final complexity-transport checkpoint stays open, with its
evidence updated to the still-missing deterministic SAT and root linkage.

The six closed-package tests and all sixteen M230/M231 source, compiled-type,
progress, current-copy and hostile publication contracts passed. The canonical
progress validator and generated status/TeX byte check passed. The new PDF
built byte-identically twice, every page rendered, and its actual cover now
reports the complete builder and NP-completeness as true while deterministic
SAT and the root remain false. The earlier M230 report is not rewritten.

The release run uses the unique union of verifier and package lifecycle tests
once, followed by the conservative checker with unit tests disabled. This
avoids repeating npm pre/post wrappers and does not rebuild unchanged Lean
evidence. Normal PR and exact post-merge checks, one clean exact-source
reproduction, and source-bound website/deployment gates remain required.
If feature and verified merge trees are identical, reuse unchanged heavyweight
evidence under the verification ownership matrix; still prove clean checkout
identity, source binding and release artifacts at the merged coordinate.

## Broad-pass report-contract correction

The first 1,400-test pass completed with 1,399 passes and one failing report
test. Auditing all 123 literal expectations in that test found two assertions
for the removed cover chronology. The detailed module-scope checks remain;
the cover now checks its five facts against authoritative status, and the body
checks the completed M230 construction and M231 NP-completeness summary.
Run the entire affected report contract before the corrected broad pass.
The Lean source, compiled inventory, ledger, status, TeX and PDF are unchanged
by this test-only correction, so their successful evidence is reused. The
failed aggregate run is not a green release result.
