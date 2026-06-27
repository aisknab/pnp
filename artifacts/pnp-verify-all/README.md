# PNP verify-all artifact

The one-command verifier writes its latest generated verdict here:

```text
artifacts/pnp-verify-all/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
npm run pnp:verify
```

The verifier currently checks:

1. `PNP_STATUS.json` boundary consistency.
2. Node syntax for the core verifier and public audit scripts.
3. The repository Node test suite.
4. The theorem-to-checker binding ledger audit.
5. The explicit trust-base audit and checksum ledger.
6. The trust-base audit tests.
7. The trust-base shrink-plan audit.
8. The trust-base shrink-plan audit tests.
9. The checker-totality seed audit.
10. The checker-totality audit tests.
11. The negative checker mutation seed audit.
12. The negative checker mutation audit tests.
13. The rule-family coverage ledger audit.
14. The rule-family coverage audit tests.
15. Cross-runtime minimal-kernel agreement.
16. Independent verifier no-shared-code policy.
17. Independent verifier audit tests.
18. Independent Python verifier tests.
19. Release-audit surface preservation.

The accepted verdict keeps the public-review boundary explicit:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

This command is the repository-level entrypoint for replaying the current self-verification stack. It does not mutate the historical sealed report and does not activate public theorem emission.
