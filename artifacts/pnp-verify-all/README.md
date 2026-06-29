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
5. The no-prose-only theorem policy audit.
6. The no-prose-only theorem policy tests.
7. The proof obligation ledger audit.
8. The proof obligation ledger tests.
9. The gap ledger audit.
10. The gap ledger tests.
11. The finite-to-unbounded family audit.
12. The finite-to-unbounded family audit tests.
13. The explicit trust-base audit and checksum ledger.
14. The trust-base audit tests.
15. The trust-base shrink-plan audit.
16. The trust-base shrink-plan audit tests.
17. The checker-totality seed audit.
18. The checker-totality audit tests.
19. The negative checker mutation seed audit.
20. The negative checker mutation audit tests.
21. The rule-family coverage ledger audit.
22. The rule-family coverage audit tests.
23. The checker dependency graph generation.
24. The checker dependency graph tests.
25. The checker no-circular-authority audit.
26. The checker no-circular-authority audit tests.
27. The NAND direct-wire semantics audit.
28. The NAND direct-wire semantics tests.
29. The NAND direct-wire small-model audit.
30. The NAND direct-wire small-model tests.
31. The locked NAND SAT small-model audit.
32. The locked NAND SAT small-model tests.
33. The complexity implication ledger audit.
34. The complexity implication ledger tests.
35. The no-hidden-oracle audit.
36. The no-hidden-oracle audit tests.
37. The fresh-clone verifier script tests.
38. The container environment manifest and Dockerfile tests.
39. The multi-platform CI manifest and workflow tests.
40. The determinism audit harness tests.
41. The artifact regeneration ledger audit.
42. The artifact regeneration ledger tests.
43. The release ladder audit.
44. The release ladder tests.
45. Cross-runtime minimal-kernel agreement.
46. Independent verifier no-shared-code policy.
47. Independent verifier audit tests.
48. Independent Python verifier tests.
49. Release-audit surface preservation.

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
