import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckFormalPublicSurface0,
  FORMAL_GATED_ENTRYPOINTS0,
} from '../pcc-formal-public-surface0.mjs';

async function packageJson0() {
  return JSON.parse(await readFile(new URL('../package.json', import.meta.url), 'utf8'));
}

test('formal public surface accepts the reconstruction boundary', async () => {
  const out = await CheckFormalPublicSurface0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PUBLIC-SURFACE-BASELINE-2026-07-10-FORMAL-RECONSTRUCTION-01');
  assert.equal(out.mathematicalTheoremEstablished, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.publicTheoremStatement, null);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(out.legacyCliHistoricalReplayRequiresExplicitOptIn, true);
  assert.equal(out.legacyProgrammaticCheckerExportsAreCurrentAuthority, false);
  assert.deepEqual(out.gatedEntrypoints, FORMAL_GATED_ENTRYPOINTS0);
});

test('formal public surface rejects an implicit package opt-in', async () => {
  const pkg = await packageJson0();
  pkg.scripts['proof:public-theorem-activation'] += ' --historical-replay';
  const out = await CheckFormalPublicSurface0({ writeOutput: false, packageJsonOverride: pkg });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalPublicSurface.ImplicitHistoricalReplay');
  assert.deepEqual(out.path, ['package.json', 'scripts', 'proof:public-theorem-activation']);
});

test('formal public surface rejects a missing CLI gate', async () => {
  const entrypoint = 'bin/runall0.mjs';
  const out = await CheckFormalPublicSurface0({
    writeOutput: false,
    sourceOverrides: { [entrypoint]: '#!/usr/bin/env node\n' },
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalPublicSurface.MissingCliGate');
  assert.deepEqual(out.path, [entrypoint]);
});

test('formal public surface rejects an unused CLI gate import', async () => {
  const entrypoint = 'bin/runall0.mjs';
  const out = await CheckFormalPublicSurface0({
    writeOutput: false,
    sourceOverrides: {
      [entrypoint]: "import { EnforceHistoricalReplayCli0 } from '../pcc-legacy-replay-gate0.mjs';\n",
    },
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalPublicSurface.MissingCliGate');
  assert.deepEqual(out.path, [entrypoint]);
});
