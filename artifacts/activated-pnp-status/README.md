# Legacy activated-status compatibility artifacts

The historical command remains available for compatibility:

```bash
npm run proof:activated-pnp-status
```

It now delegates to the formal reconstruction status checker and must report:

```text
publicTheoremEmissionAllowed = false
activationSuperseded = true
formalReleaseGatePassed = false
```

The compatibility output is not theorem evidence. The canonical current artifact is `artifacts/formal-reconstruction-status/latest-verdict.json`.
