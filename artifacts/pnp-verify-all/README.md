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
5. The proof obligation ledger audit.
6. The proof obligation ledger tests.
7. The explicit trust-base audit and checksum ledger.
8. The trust-base audit tests.
9. The trust-base shrink-plan audit.
10. The trust-base shrink-plan audit tests.
11. The checker-totality seed audit.
12. The checker-totality audit tests.
13. The negative checker mutation seed audit.
14. The negative checker mutation audit tests.
15. The rule-family coverage ledger audit.
16. The rule-family coverage audit tests.
17. The checker dependency graph generation.
18. The checker dependency graph tests.
19. The checker no-circular-authority audit.
20. The checker no-circular-authority audit tests.
21. The NAND direct-wire semantics audit.
22. The NAND direct-wire semantics tests.
23. The NAND direct-wire small-model audit.
24. The NAND direct-wire small-model tests.
25. The locked NAND SAT small-model audit.
26. The locked NAND SAT small-model tests.
27. The complexity implication ledger audit.
28. The complexity implication ledger tests.
29. The no-hidden-oracle audit.
30. The no-hidden-oracle audit tests.
31. The fresh-clone verifier script tests.
32. The container environment manifest and Dockerfile tests.
33. The multi-platform CI manifest and workflow tests.
34. The determinism audit harness tests.
35. The artifact regeneration ledger audit.
36. The artifact regeneration ledger tests.
37. The release ladder audit.
38. The release ladder tests.
39. Cross-runtime minimal-kernel agreement.
40. Independent verifier no-shared-code policy.
41. Independent verifier audit tests.
42. Independent Python verifier tests.
43. Release-audit surface preservation.

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
