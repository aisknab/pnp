import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

async function text0(pathname) {
  return readFile(new URL(`../${pathname}`, import.meta.url), 'utf8');
}

async function json0(pathname) {
  return JSON.parse(await text0(pathname));
}

test('container environment manifest preserves non-activating boundary', async () => {
  const manifest = await json0('reproducibility/CONTAINER_ENVIRONMENT.json');

  assert.equal(manifest.kind, 'PNPContainerEnvironment0');
  assert.equal(manifest.coordinate, 'PNP-CONTAINER-ENVIRONMENT-2026-06-27-01');
  assert.equal(manifest.containerEnvironmentReady, true);
  assert.equal(manifest.fullEnvironmentReproducibilityProved, false);
  assert.equal(manifest.publicTheoremEmissionAllowedByEnvironment, false);
  assert.equal(manifest.baseImage.image, 'node:20-bookworm-slim');
  assert.equal(manifest.baseImage.nodeMajor, 20);
  assert.equal(manifest.claimBoundary.publicTheoremEmissionAllowed, false);
  assert.equal(manifest.claimBoundary.finalTheoremReady, false);
  assert.deepEqual(manifest.claimBoundary.activeFinalNodeIds, []);
  assert.deepEqual(manifest.claimBoundary.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('Dockerfile installs from lockfile and defaults to pnp verify', async () => {
  const dockerfile = await text0('Dockerfile');

  assert.match(dockerfile, /^FROM node:20-bookworm-slim/m);
  assert.match(dockerfile, /^WORKDIR \/workspace\/pnp/m);
  assert.match(dockerfile, /^COPY package\.json package-lock\.json \.[/]?$/m);
  assert.match(dockerfile, /^RUN npm ci$/m);
  assert.match(dockerfile, /^COPY \. \.$/m);
  assert.match(dockerfile, /^CMD \["npm", "run", "pnp:verify"\]$/m);
});

test('docker compose exposes the verifier service', async () => {
  const compose = await text0('docker-compose.yml');

  assert.match(compose, /^services:/m);
  assert.match(compose, /pnp-verify:/);
  assert.match(compose, /dockerfile: Dockerfile/);
  assert.match(compose, /image: pnp-verify:local/);
  assert.match(compose, /command: \["npm", "run", "pnp:verify"\]/);
});

test('devcontainer builds from the repository Dockerfile', async () => {
  const devcontainer = await json0('.devcontainer/devcontainer.json');

  assert.equal(devcontainer.name, 'PNP verifier');
  assert.equal(devcontainer.build.dockerfile, '../Dockerfile');
  assert.equal(devcontainer.build.context, '..');
  assert.equal(devcontainer.workspaceFolder, '/workspace/pnp');
  assert.equal(devcontainer.postCreateCommand, 'npm ci');
});

test('dockerignore excludes generated and local-only directories', async () => {
  const dockerignore = await text0('.dockerignore');

  assert.match(dockerignore, /^\.git$/m);
  assert.match(dockerignore, /^node_modules$/m);
  assert.match(dockerignore, /^artifacts\/\*\*\/latest-verdict\.json$/m);
});
