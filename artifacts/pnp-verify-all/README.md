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
7. The report theorem coverage matrix audit.
8. The report theorem coverage matrix tests.
9. The no-prose-only theorem policy audit.
10. The no-prose-only theorem policy tests.
11. The proof obligation ledger audit.
12. The proof obligation ledger tests.
13. The gap ledger audit.
14. The gap ledger tests.
15. The finite-to-unbounded family audit.
16. The finite-to-unbounded family audit tests.
17. The explicit trust-base audit and checksum ledger.
18. The trust-base audit tests.
19. The trust-base shrink-plan audit.
20. The trust-base shrink-plan audit tests.
21. The checker-totality seed audit.
22. The checker-totality audit tests.
23. The negative checker mutation seed audit.
24. The negative checker mutation audit tests.
25. The rule-family coverage ledger audit.
26. The rule-family coverage audit tests.
27. The checker dependency graph generation.
28. The checker dependency graph tests.
29. The checker no-circular-authority audit.
30. The checker no-circular-authority audit tests.
31. The NAND direct-wire semantics audit.
32. The NAND direct-wire semantics tests.
33. The NAND direct-wire small-model audit.
34. The NAND direct-wire small-model tests.
35. The locked NAND SAT small-model audit.
36. The locked NAND SAT small-model tests.
37. The complexity implication ledger audit.
38. The complexity implication ledger tests.
39. The no-hidden-oracle audit.
40. The no-hidden-oracle audit tests.
41. The fresh-clone verifier script tests.
42. The container environment manifest and Dockerfile tests.
43. The multi-platform CI manifest and workflow tests.
44. The determinism audit harness tests.
45. The artifact regeneration ledger audit.
46. The artifact regeneration ledger tests.
47. The release ladder audit.
48. The release ladder tests.
49. Cross-runtime minimal-kernel agreement.
50. Independent verifier no-shared-code policy.
51. Independent verifier audit tests.
52. Independent Python verifier tests.
53. Release-audit surface preservation.

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
