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
9. The finite-to-unbounded family audit.
10. The finite-to-unbounded family audit tests.
11. The explicit trust-base audit and checksum ledger.
12. The trust-base audit tests.
13. The trust-base shrink-plan audit.
14. The trust-base shrink-plan audit tests.
15. The checker-totality seed audit.
16. The checker-totality audit tests.
17. The negative checker mutation seed audit.
18. The negative checker mutation audit tests.
19. The rule-family coverage ledger audit.
20. The rule-family coverage audit tests.
21. The checker dependency graph generation.
22. The checker dependency graph tests.
23. The checker no-circular-authority audit.
24. The checker no-circular-authority audit tests.
25. The NAND direct-wire semantics audit.
26. The NAND direct-wire semantics tests.
27. The NAND direct-wire small-model audit.
28. The NAND direct-wire small-model tests.
29. The locked NAND SAT small-model audit.
30. The locked NAND SAT small-model tests.
31. The complexity implication ledger audit.
32. The complexity implication ledger tests.
33. The no-hidden-oracle audit.
34. The no-hidden-oracle audit tests.
35. The fresh-clone verifier script tests.
36. The container environment manifest and Dockerfile tests.
37. The multi-platform CI manifest and workflow tests.
38. The determinism audit harness tests.
39. The artifact regeneration ledger audit.
40. The artifact regeneration ledger tests.
41. The release ladder audit.
42. The release ladder tests.
43. Cross-runtime minimal-kernel agreement.
44. Independent verifier no-shared-code policy.
45. Independent verifier audit tests.
46. Independent Python verifier tests.
47. Release-audit surface preservation.

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
