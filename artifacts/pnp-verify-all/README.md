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
13. The no-prose-only theorem policy audit.
14. The no-prose-only theorem policy tests.
15. The proof obligation ledger audit.
16. The proof obligation ledger tests.
17. The gap ledger audit.
18. The gap ledger tests.
19. The finite-to-unbounded family audit.
20. The finite-to-unbounded family audit tests.
21. The explicit trust-base audit and checksum ledger.
22. The trust-base audit tests.
23. The trust-base shrink-plan audit.
24. The trust-base shrink-plan audit tests.
25. The checker-totality seed audit.
26. The checker-totality audit tests.
27. The negative checker mutation seed audit.
28. The negative checker mutation audit tests.
29. The rule-family coverage ledger audit.
30. The rule-family coverage audit tests.
31. The checker dependency graph generation.
32. The checker dependency graph tests.
33. The checker no-circular-authority audit.
34. The checker no-circular-authority audit tests.
35. The NAND direct-wire semantics audit.
36. The NAND direct-wire semantics tests.
37. The NAND direct-wire small-model audit.
38. The NAND direct-wire small-model tests.
39. The locked NAND SAT small-model audit.
40. The locked NAND SAT small-model tests.
41. The complexity implication ledger audit.
42. The complexity implication ledger tests.
43. The no-hidden-oracle audit.
44. The no-hidden-oracle audit tests.
45. The fresh-clone verifier script tests.
46. The container environment manifest and Dockerfile tests.
47. The multi-platform CI manifest and workflow tests.
48. The determinism audit harness tests.
49. The artifact regeneration ledger audit.
50. The artifact regeneration ledger tests.
51. The release ladder audit.
52. The release ladder tests.
53. Cross-runtime minimal-kernel agreement.
54. Independent verifier no-shared-code policy.
55. Independent verifier audit tests.
56. Independent Python verifier tests.
57. Release-audit surface preservation.

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
