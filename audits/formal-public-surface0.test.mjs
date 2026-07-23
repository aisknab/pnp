import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckFormalPublicSurface0,
  CURRENT_PACKAGE_EXPORTS0,
  CURRENT_PACKAGE_SCRIPTS0,
} from '../pcc-formal-public-surface0.mjs';

async function packageJson0() {
  return JSON.parse(await readFile(new URL('../package.json', import.meta.url), 'utf8'));
}

test('formal public surface accepts the archive-only legacy boundary', async () => {
  const out = await CheckFormalPublicSurface0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PUBLIC-SURFACE-BASELINE-2026-07-23-COOK-LEVIN-BUILDER-SECOND-CONSTRAINT-SECOND-PADDING-OR-UNARY-OPPORTUNITY-STEP-77');
  assert.equal(out.currentStatusAuthority, true);
  assert.equal(out.mathematicalTheoremEstablished, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.leanConcreteCNFVerifierCorrectnessFormalized, true);
  assert.equal(out.leanConcreteCNFVerifierNoTimeoutFormalized, true);
  assert.equal(out.leanConcreteCNFSATMembershipFormalized, true);
  assert.equal(out.leanConcreteCNFSATMembershipTheorem,
    'PNP.Concrete.FinalUniversalDesign.cnfSATInNP');
  assert.equal(out.leanConcreteCNFSATInPFormalized, false);
  assert.equal(out.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(out.publicTheoremStatement, null);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(out.legacyV0CheckerExportedAsCurrentAuthority, false);
  assert.equal(out.legacyV0ReplayRequiresDesignatedCommand, true);
  assert.deepEqual(out.packageExports, CURRENT_PACKAGE_EXPORTS0);
  assert.deepEqual(out.packageScripts, CURRENT_PACKAGE_SCRIPTS0);
  assert.deepEqual(out.packageBinKeys, []);
});

test('formal public surface rejects a legacy theorem-checker package export', async () => {
  const pkg = await packageJson0();
  pkg.exports['./runall0'] = './pcc-runall-public0.mjs';
  const out = await CheckFormalPublicSurface0({ writeOutput: false, packageJsonOverride: pkg });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalPublicSurface.PackageExports');
  assert.deepEqual(out.path, ['package.json', 'exports']);
});

test('formal public surface rejects a reintroduced executable bin', async () => {
  const pkg = await packageJson0();
  pkg.bin = { 'pnp-runall0': './bin/runall0.mjs' };
  const out = await CheckFormalPublicSurface0({ writeOutput: false, packageJsonOverride: pkg });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalPublicSurface.PackageBin');
  assert.deepEqual(out.path, ['package.json', 'bin']);
});

test('formal public surface rejects extra or drifting scripts', async () => {
  const pkg = await packageJson0();
  pkg.scripts.runall = 'node ./bin/runall0.mjs --historical-replay';
  const out = await CheckFormalPublicSurface0({ writeOutput: false, packageJsonOverride: pkg });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalPublicSurface.PackageScripts');
  assert.deepEqual(out.path, ['package.json', 'scripts']);
});

test('formal public surface rejects a legacy route in the root entry point', async () => {
  const index = await readFile(new URL('../index.mjs', import.meta.url), 'utf8');
  const out = await CheckFormalPublicSurface0({
    writeOutput: false,
    indexSourceOverride: `${index}\nexport { RunAll0 } from './pcc-runall0.mjs';\n`,
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalPublicSurface.LegacyExport');
  assert.deepEqual(out.path, ['index.mjs']);
});

test('formal public surface rejects an extra non-legacy root export', async () => {
  const index = await readFile(new URL('../index.mjs', import.meta.url), 'utf8');
  const out = await CheckFormalPublicSurface0({
    writeOutput: false,
    indexSourceOverride: `${index}\nexport const UnexpectedCurrentAuthority0 = true;\n`,
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalPublicSurface.IndexExports');
  assert.deepEqual(out.path, ['index.mjs', 'exports']);
  assert.equal(out.witness.unparsedExportSyntax, true);
});
