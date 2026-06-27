# Trust-base shrink-plan artifacts

The trust-base shrink-plan checker writes its latest generated verdict here:

```text
artifacts/trust-base/shrink-plan/latest-verdict.json
```

The generated verdict is not committed as a stable source artifact. It is replayed from the current checkout.

Run it with:

```bash
node pcc-trust-base-shrink-plan0.mjs --json
```

The checker validates `trust-base/SHRINK_PLAN.json`, checks that it links to `PNP-TRUST-BASE-2026-06-27-01`, verifies every required trust-base assumption is targeted by at least one shrink task, rejects premature completion states, validates task dependencies, and preserves the public-review boundary.

The plan is deliberately non-activating:

```text
shrinkPlanReady = true
shrinksTrustBaseNow = false
```

This artifact does not claim the trust base has shrunk yet. It records the reduction queue that later PRs must discharge one task at a time.
