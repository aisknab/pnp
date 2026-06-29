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
7. The gap ledger audit.
8. The gap ledger tests.
9. The explicit trust-base audit and checksum ledger.
10. The trust-base audit tests.
11. The trust-base shrink-plan audit.
12. The trust-base shrink-plan audit tests.
13. The checker-totality seed audit.
14. The checker-totality audit tests.
15. The negative checker mutation seed audit.
16. The negative checker mutation audit tests.
17. The rule-family coverage ledger audit.
18. The rule-family coverage audit tests.
19. The checker dependency graph generation.
20. The checker dependency graph tests.
21. The checker no-circular-authority audit.
22. The checker no-circular-authority audit tests.
23. The NAND direct-wire semantics audit.
24. The NAND direct-wire semantics tests.
25. The NAND direct-wire small-model audit.
26. The NAND direct-wire small-model tests.
27. The locked NAND SAT small-model audit.
28. The locked NAND SAT small-model tests.
29. The complexity implication ledger audit.
30. The complexity implication ledger tests.
31. The no-hidden-oracle audit.
32. The no-hidden-oracle audit tests.
33. The fresh-clone verifier script tests.
34. The container environment manifest and Dockerfile tests.
35. The multi-platform CI manifest and workflow tests.
36. The determinism audit harness tests.
37. The artifact regeneration ledger audit.
38. The artifact regeneration ledger tests.
39. The release ladder audit.
40. The release ladder tests.
41. Cross-runtime minimal-kernel agreement.
42. Independent verifier no-shared-code policy.
43. Independent verifier audit tests.
44. Independent Python verifier tests.
45. Release-audit surface preservation.

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
