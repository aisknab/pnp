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
15. The no-prose-only theorem policy audit.
16. The no-prose-only theorem policy tests.
17. The proof obligation ledger audit.
18. The proof obligation ledger tests.
19. The gap ledger audit.
20. The gap ledger tests.
21. The finite-to-unbounded family audit.
22. The finite-to-unbounded family audit tests.
23. The explicit trust-base audit and checksum ledger.
24. The trust-base audit tests.
25. The trust-base shrink-plan audit.
26. The trust-base shrink-plan audit tests.
27. The checker-totality seed audit.
28. The checker-totality audit tests.
29. The negative checker mutation seed audit.
30. The negative checker mutation audit tests.
31. The rule-family coverage ledger audit.
32. The rule-family coverage audit tests.
33. The checker dependency graph generation.
34. The checker dependency graph tests.
35. The checker no-circular-authority audit.
36. The checker no-circular-authority audit tests.
37. The NAND direct-wire semantics audit.
38. The NAND direct-wire semantics tests.
39. The NAND direct-wire small-model audit.
40. The NAND direct-wire small-model tests.
41. The locked NAND SAT small-model audit.
42. The locked NAND SAT small-model tests.
43. The complexity implication ledger audit.
44. The complexity implication ledger tests.
45. The no-hidden-oracle audit.
46. The no-hidden-oracle audit tests.
47. The fresh-clone verifier script tests.
48. The container environment manifest and Dockerfile tests.
49. The multi-platform CI manifest and workflow tests.
50. The determinism audit harness tests.
51. The artifact regeneration ledger audit.
52. The artifact regeneration ledger tests.
53. The release ladder audit.
54. The release ladder tests.
55. Cross-runtime minimal-kernel agreement.
56. Independent verifier no-shared-code policy.
57. Independent verifier audit tests.
58. Independent Python verifier tests.
59. Release-audit surface preservation.

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
