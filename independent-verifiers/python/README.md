# Independent Python minimal-kernel verifier

This directory contains a clean-room Python verifier for the minimal proof-kernel coordinate. It is intentionally small and uses only the Python standard library.

The verifier does not import the JavaScript checker implementation. It consumes the repository's JSON audit artifacts as data and checks a subset of the same boundary invariants from an independent runtime.

## Scope

The verifier checks:

- `kernel/PNP_MINIMAL_KERNEL.json` has coordinate `PNP-MINIMAL-KERNEL-2026-06-27-01`.
- public theorem emission remains disabled.
- `finalTheoremReady` remains false.
- `activeFinalNodeIds` remains empty.
- remaining blockers remain exactly:
  - `Release.UnrestrictedFinalSoundness`
  - `ExternalReview.Acceptance`
- quarantined final node ids remain fixed.
- primitive kernel rule ids, Sigma theorem ids, proof-spine ids, and checker-surface ids match the expected minimal coordinate.
- every proof-spine checker id is declared in the checker surface.
- every proof-spine rule family is declared in the primitive rule table.
- every proof-spine package theorem id is either a required package theorem or a quarantined final node.
- every proof-spine report-binding id exists in `report-bindings/REPORT_THEOREM_BINDINGS.json`.
- referenced checker files exist in the checkout.
- no activation field claims public theorem emission.

The verifier also emits SHA256 digests for the minimal-kernel JSON and theorem-binding ledger bytes. These hashes are audit identities, not semantic proof obligations.

## Command

From the repository root:

```bash
python3 independent-verifiers/python/verify_minimal_kernel.py --json
```

Expected result:

```json
{
  "tag": "accept",
  "claimStatus": "minimal-kernel-independent-python-accepted",
  "publicTheoremEmissionAllowed": false,
  "finalTheoremReady": false,
  "activeFinalNodeIds": [],
  "remainingBlockers": [
    "Release.UnrestrictedFinalSoundness",
    "ExternalReview.Acceptance"
  ]
}
```

## Tests

```bash
python3 -m unittest discover independent-verifiers/python -p '*_test.py'
```

## Non-claims

This verifier is a redundancy layer for the minimal-kernel audit boundary. It does not prove the mathematical theorem, does not discharge `Release.UnrestrictedFinalSoundness`, and does not allow public theorem emission.
