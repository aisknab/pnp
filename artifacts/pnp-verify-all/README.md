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

The verifier currently checks the repository status boundary, Node syntax, the repository Node test suite, the theorem/report ledgers, direct-binding seed audits, proof/gap/trust ledgers, checker-hardening ledgers, semantics ledgers, reproducibility ledgers, release ladder, independent verifier surfaces, Python verifier tests, and release-audit preservation.

The current direct-binding seed audits included in the verifier are:

```text
Base -> pcc-direct-bind-base-semantics0.mjs
CHG  -> pcc-direct-bind-charge-ledger0.mjs
Mode -> pcc-direct-bind-mode-firewall0.mjs
E    -> pcc-direct-bind-verifydw-soundness0.mjs
N    -> pcc-direct-bind-normalization0.mjs
FT   -> pcc-direct-bind-finite-table0.mjs
```

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
