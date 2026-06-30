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
17. The E direct-binding seed audit.
18. The E direct-binding seed tests.
19. The no-prose-only theorem policy audit.
20. The no-prose-only theorem policy tests.
21. The proof obligation ledger audit.
22. The proof obligation ledger tests.
23. The gap ledger audit.
24. The gap ledger tests.
25. The finite-to-unbounded family audit.
26. The finite-to-unbounded family audit tests.
27. The explicit trust-base audit and checksum ledger.
28. The trust-base audit tests.
29. The trust-base shrink-plan audit.
30. The trust-base shrink-plan audit tests.
31. The checker-totality seed audit.
32. The checker-totality audit tests.
33. The negative checker mutation seed audit.
34. The negative checker mutation audit tests.
35. The rule-family coverage ledger audit.
36. The rule-family coverage audit tests.
37. The checker dependency graph generation.
38. The checker dependency graph tests.
39. The checker no-circular-authority audit.
40. The checker no-circular-authority audit tests.
41. The NAND direct-wire semantics audit.
42. The NAND direct-wire semantics tests.
43. The NAND direct-wire small-model audit.
44. The NAND direct-wire small-model tests.
45. The locked NAND SAT small-model audit.
46. The locked NAND SAT small-model tests.
47. The complexity implication ledger audit.
48. The complexity implication ledger tests.
49. The no-hidden-oracle audit.
50. The no-hidden-oracle audit tests.
51. The fresh-clone verifier script tests.
52. The container environment manifest and Dockerfile tests.
53. The multi-platform CI manifest and workflow tests.
54. The determinism audit harness tests.
55. The artifact regeneration ledger audit.
56. The artifact regeneration ledger tests.
57. The release ladder audit.
58. The release ladder tests.
59. Cross-runtime minimal-kernel agreement.
60. Independent verifier no-shared-code policy.
61. Independent verifier audit tests.
62. Independent Python verifier tests.
63. Release-audit surface preservation.

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
