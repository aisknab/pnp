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
15. The checker dependency graph generation.
16. The checker dependency graph tests.
17. The checker no-circular-authority audit.
18. The checker no-circular-authority audit tests.
19. The NAND direct-wire semantics audit.
20. The NAND direct-wire semantics tests.
21. The NAND direct-wire small-model audit.
22. The NAND direct-wire small-model tests.
23. The locked NAND SAT small-model audit.
24. The locked NAND SAT small-model tests.
25. The complexity implication ledger audit.
26. The complexity implication ledger tests.
27. The no-hidden-oracle audit.
28. The no-hidden-oracle audit tests.
29. The fresh-clone verifier script tests.
30. The container environment manifest and Dockerfile tests.
31. The multi-platform CI manifest and workflow tests.
32. The determinism audit harness tests.
33. Cross-runtime minimal-kernel agreement.
34. Independent verifier no-shared-code policy.
35. Independent verifier audit tests.
36. Independent Python verifier tests.
37. Release-audit surface preservation.

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
