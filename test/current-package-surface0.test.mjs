import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import * as currentApi from '../index.mjs';
import {
  CURRENT_PACKAGE_EXPORTS0,
  CURRENT_PACKAGE_SCRIPTS0,
  CURRENT_PUBLIC_EXPORTS0,
} from '../pcc-formal-public-surface0.mjs';

test('root entry point exports only current status and archive verification APIs', () => {
  assert.deepEqual(Object.keys(currentApi).sort(), [...CURRENT_PUBLIC_EXPORTS0].sort());
  for (const legacy of [
    'RunAll0',
    'CheckRunAll0',
    'CheckReleaseAudit0',
    'CheckPCCPackexp0',
    'GeneratePCCPack0',
    'CheckFinalPNPProofReport0',
  ]) {
    assert.equal(Object.hasOwn(currentApi, legacy), false, legacy);
  }
});

test('package exports, scripts, and bins are a closed current-authority surface', async () => {
  const pkg = JSON.parse(await readFile(new URL('../package.json', import.meta.url), 'utf8'));
  assert.deepEqual(pkg.exports, CURRENT_PACKAGE_EXPORTS0);
  assert.deepEqual(pkg.scripts, CURRENT_PACKAGE_SCRIPTS0);
  assert.equal(Object.hasOwn(pkg, 'bin'), false);
  assert.equal(pkg.private, true);
  assert.deepEqual(Object.keys(pkg.scripts).filter((key) => key.startsWith('legacy:')), [
    'legacy:v0:check',
    'legacy:v0:replay',
  ]);
});

test('legacy-v0 subpath exposes archive verification, not checker execution', async () => {
  const archiveApi = await import('@aisknab/pnp/legacy-v0-archive');
  assert.deepEqual(Object.keys(archiveApi).sort(), [
    'CheckLegacyV0Archive0',
    'LEGACY_V0_ARCHIVE_PINS0',
  ]);
});

test('historical replay is manual-only and automatic CI never executes it', async () => {
  const historical = await readFile(new URL('../.github/workflows/legacy-v0-replay.yml', import.meta.url), 'utf8');
  const ci = await readFile(new URL('../.github/workflows/ci.yml', import.meta.url), 'utf8');

  assert.match(historical, /on:\n  workflow_dispatch:/u);
  assert.doesNotMatch(historical, /\n  (?:push|pull_request):/u);
  assert.match(historical, /permissions:\n  contents: read/u);
  assert.match(historical, /replay-transcript\.json/u);
  assert.doesNotMatch(historical, /\bgit (?:commit|push|tag)\b/u);

  assert.doesNotMatch(ci, /replay-legacy-v0|legacy:v0:replay|--historical-replay/u);
  assert.match(ci, /npm run pnp:verify -- --no-write/u);
});
