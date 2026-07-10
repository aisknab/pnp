# Withdrawn activated PNP status artifacts

This directory documents a historical assertion-checker verdict. The activated status is withdrawn as
proof authority and must not be treated as the current public status. The current authority is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](../../status/FORMAL_RECONSTRUCTION_STATUS.json).

The legacy checker wrote its generated verdict here:

```text
artifacts/activated-pnp-status/latest-verdict.json
```

The historical replay commands were:

```bash
npm run proof:activated-pnp-status -- --historical-replay
```

or directly with:

```bash
node pcc-activated-pnp-status0.mjs --json --historical-replay
```

This artifact surface checked that the old activated-status payload and its public mirror matched the
same recorded assertion state. That replay did not establish the mathematical propositions named in
the payload. The activated payload, `PNP_STATUS.json`, and the older public-review checks are legacy
surfaces subordinate to the formal reconstruction status.
