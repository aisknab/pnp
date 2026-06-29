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
9. The report theorem coverage closure plan audit.
10. The report theorem coverage closure plan tests.
11. The Base direct-binding seed audit.
12. The Base direct-binding seed tests.
13. The CHG direct-binding seed audit.
14. The CHG direct-binding seed tests.
15. The Mode direct-binding seed audit.
16. The Mode direct-binding seed tests.
17. The no-prose-only theorem policy audit.
18. The no-prose-only theorem policy tests.
19. The proof obligation ledger audit.
20. The proof obligation ledger tests.
21. The gap ledger audit.
22. The gap ledger tests.
23. The finite-to-unbounded family audit.
24. The finite-to-unbounded family audit tests.
25. The explicit trust-base audit and checksum ledger.
26. The trust-base audit tests.
27. The trust-base shrink-plan audit.
28. The trust-base shrink-plan audit tests.
29. The checker-totality seed audit.
30. The checker-totality audit tests.
31. The negative checker mutation seed audit.
32. The negative checker mutation audit tests.
33. The rule-family coverage ledger audit.
34. The rule-family coverage audit tests.
35. The checker dependency graph generation.
36. The checker dependency graph tests.
37. The checker no-circular-authority audit.
38. The checker no-circular-authority audit tests.
39. The NAND direct-wire semantics audit.
40. The NAND direct-wire semantics tests.
41. The NAND direct-wire small-model audit.
42. The NAND direct-wire small-model tests.
43. The locked NAND SAT small-model audit.
44. The locked NAND SAT small-model tests.
45. The complexity implication ledger audit.
46. The complexity implication ledger tests.
47. The no-hidden-oracle audit.
48. The no-hidden-oracle audit tests.
49. The fresh-clone verifier script tests.
50. The container environment manifest and Dockerfile tests.
51. The multi-platform CI manifest and workflow tests.
52. The determinism audit harness tests.
53. The artifact regeneration ledger audit.
54. The artifact regeneration ledger tests.
55. The release ladder audit.
56. The release ladder tests.
57. Cross-runtime minimal-kernel agreement.
58. Independent verifier no-shared-code policy.
59. Independent verifier audit tests.
60. Independent Python verifier tests.
61. Release-audit surface preservation.

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
