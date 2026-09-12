# M243: checked SAT hardness in the active final-report bridge

## Legacy anchor and dependency edge

Reconstruct the final complexity step in Section 18 of the canonical manuscript
pinned by `final-pnp-proof-report-docs-hardened-7072f8d-sealed`: Final SAT
decision, Accepted package implies P=NP, and Generated package sufficiency.
The source is `canonical_proof_report.tex`, specifically the theorem block
following the residual-band decision rule. Historical checker acceptance remains
specification/provenance, never kernel proof authority.

M231 already proves concrete CNFSAT NP-completeness. The active
`accepted_generated_package_implies_p_eq_np` and `final_report_bridge`
nevertheless require `CheckerTrustModel.satHard`. Close that actual dependency
edge by consuming the checked M231 theorem, not by reproving Cook-Levin or
creating an unused parallel bridge.

## Exact unbounded theorem boundary

Preserve `SAT := Concrete.CNFSAT` and all concrete complexity aliases. Add:

```lean
theorem sat_np_hard_checked : SATHard
theorem sat_np_complete_checked : NPComplete SAT
```

Both reuse the compiled all-input M231 construction. Strengthen the existing
active interfaces to:

```lean
theorem accepted_generated_package_implies_p_eq_np
    (loop : PCCMinLoopCertificate)
    (h : AcceptedGeneratedPackage loop) : PEqualsNP

theorem final_report_bridge :
    FinalReportAntecedent → FinalReportConsequent
```

Remove the now-unused `CheckerTrustModel` record. Keep the proof-bearing loop
certificate and its concrete residual-band polynomial decider explicit.
Do not infer existence from the accepted identifier, a string, a historic
acceptance record or an external supplied hardness proof.

This is a stronger conditional bridge, not an unconditional root theorem.
Update current bridge/root-status text to distinguish closed reduction,
reflection and hardness results from the remaining algorithmic obligations.

## Producer and consumer changes together

- SAT source imports and exact endpoints; Bridge theorem signatures and summary;
  Main blocker descriptions. Preserve package, loop and checker definitions.
- The three compatibility/reflection regression and source-contract families
  currently mention `CheckerTrustModel`. Replace those expectations and their
  hostile injections in the same edit; retain rejection of supplied reduction,
  reflection, missing-loop and string-authority shortcuts.
- Add exact argument-free hardness and conditional bridge type/axiom regressions.
  Assert that the eligible root is still absent and the loop-existence premise
  is not discharged.
- Update the inventory reviewed-name producer and required-name consumer,
  publication fingerprint keys, status fields and durable workflow together.
  Obtain fingerprints and counts only from compiled declarations.
- Reconcile package-script closure, current generated status/progress/report
  consumers and active bridge documentation before the relevant tests.
  Preserve pinned archives and module-specific historical milestone scope.

## Remaining obligations and progress

This does not construct the complete PCCMin loop certificate, its exact
polynomial residual-band decider, unconditional SaturatePositive, BCELReady or
ZeroSlack, runtime/output/certificate bounds, deterministic CNFSAT membership
in P, or `PNP.Main.p_eq_np`. Empty project-axiom inventory is not proof of
these missing existence statements.

The M231 hardness checkpoint is already credited. Do not award it twice or
close the final root transport checkpoint without the deterministic theorem
and eligible root linkage. Keep the fixed risk-weighted estimate unchanged;
formal artefact coverage is calculated separately from the publication ledger.

Publication decision: **defer PNPLabs**. The published M231 snapshot already
reports concrete NP-completeness. This removes an unnecessary internal bridge
premise but does not change that public bottom line or close a global gate.

## Verification and release

1. Record this plan before implementation. Use a separate checkout and an
   exact-source/toolchain-matched cache; do all processing on the remote builder.
2. Update source and affected tests together. Run the cheapest source-contract
   and bounded changed-module/type/axiom checks first.
3. Rebuild the changed dependency chain and explicit root; execute the exact
   edited workflow block and all affected Lean regressions. Freeze Lean source
   before inventory/source-closure sealing.
4. Generate canonical publication/status/progress and current documentation,
   run focused hostile checks, then one deduplicated standard test union.
   Run the canonical report command once with its built-in byte reproduction.
5. Reanchor to the actual verified M242 merge without changing the tested tree.
   Verify the exact head independently, normal PR checks, manual ready/merge,
   post-merge checks and one exact-merge identity/seal reproduction. Reuse
   unchanged heavyweight evidence across an identical tree where permitted.
6. Send meaningful verified-substep and completion notifications. Remove the
   named temporary checkouts, helpers, patches and logs after release evidence
   is recorded.
