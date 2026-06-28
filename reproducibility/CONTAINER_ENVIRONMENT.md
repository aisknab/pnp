# Containerized verification environment

This directory records the current container-environment coordinate:

```text
PNP-CONTAINER-ENVIRONMENT-2026-06-27-01
```

The machine-readable manifest is:

```text
reproducibility/CONTAINER_ENVIRONMENT.json
```

The container files are:

```text
Dockerfile
.dockerignore
docker-compose.yml
.devcontainer/devcontainer.json
.github/workflows/container-environment.yml
```

Build and run the default verifier path with:

```bash
docker build -t pnp-verify:local .
docker run pnp-verify:local npm run pnp:verify
```

The Dockerfile uses `node:20-bookworm-slim`, installs dependencies with `npm ci`, copies the repository, and defaults to:

```bash
npm run pnp:verify
```

## CI smoke mode

The container workflow builds the same Dockerfile, then runs a fast smoke command:

```bash
docker run pnp-container-environment-smoke node --check pcc-core.mjs
```

That checks container build and execution mechanics without recursively running the full one-command verifier inside every container workflow run. Independent reviewers can run the full default command above.

## Boundary

The container environment is non-activating:

```text
publicTheoremEmissionAllowed = false
finalTheoremReady = false
activeFinalNodeIds = []
remainingBlockers = [
  "Release.UnrestrictedFinalSoundness",
  "ExternalReview.Acceptance"
]
```

The base image is pinned by Node major version and Debian distribution, but not yet by immutable image digest. Digest pinning remains a future reproducibility hardening step.
