# Container environment artifacts

The container environment workflow does not commit generated runtime artifacts. It validates the source manifest and builds the repository Dockerfile at replay time.

The source coordinate is:

```text
PNP-CONTAINER-ENVIRONMENT-2026-06-27-01
```

Build and run the full verifier in the container with:

```bash
docker build -t pnp-verify:local .
docker run pnp-verify:local npm run pnp:verify
```

The CI smoke path builds the same Dockerfile and runs:

```bash
docker run pnp-container-environment-smoke node --check pcc-core.mjs
```

The container environment is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
