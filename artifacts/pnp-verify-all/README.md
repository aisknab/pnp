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
5. The report theorem inventory audit.
6. The report theorem inventory tests.
7. The no-prose-only theorem policy audit.
8. The no-prose-only theorem policy tests.
9. The proof obligation ledger audit.
10. The proof obligation ledger tests.
11. The gap ledger audit.
12. The gap ledger tests.
13. The finite-to-unbounded family audit.
14. The finite-to-unbounded family audit tests.
15. The explicit trust-base audit and checksum ledger.
16. The trust-base audit tests.
17. The trust-base shrink-plan audit.
18. The trust-base shrink-plan audit tests.
19. The checker-totality seed audit.
20. The checker-totality audit tests.
21. The negative checker mutation seed audit.
22. The negative checker mutation audit tests.
23. The rule-family coverage ledger audit.
24. The rule-family coverage audit tests.
25. The checker dependency graph generation.
26. The checker dependency graph tests.
27. The checker no-circular-authority audit.
28. The checker no-circular-authority audit tests.
29. The NAND direct-wire semantics audit.
30. The NAND direct-wire semantics tests.
31. The NAND direct-wire small-model audit.
32. The NAND direct-wire small-model tests.
33. The locked NAND SAT small-model audit.
34. The locked NAND SAT small-model tests.
35. The complexity implication ledger audit.
36. The complexity implication ledger tests.
37. The no-hidden-oracle audit.
38. The no-hidden-oracle audit tests.
39. The fresh-clone verifier script tests.
40. The container environment manifest and Dockerfile tests.
41. The multi-platform CI manifest and workflow tests.
42. The determinism audit harness tests.
43. The artifact regeneration ledger audit.
44. The artifact regeneration ledger tests.
45. The release ladder audit.
46. The release ladder tests.
47. Cross-runtime minimal-kernel agreement.
48. Independent verifier no-shared-code policy.
49. Independent verifier audit tests.
50. Independent Python verifier tests.
51. Release-audit surface preservation.

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
