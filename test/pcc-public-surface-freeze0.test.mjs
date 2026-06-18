import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import { test } from 'node:test';

import * as publicEntry0 from '../index.mjs';

import {
  CheckPublicEntryReleaseSurface0,
  PUBLIC_ENTRY_EXPORT_KEYS0,
  PUBLIC_PACKAGE_BIN0,
  PUBLIC_PACKAGE_EXPORTS0,
  PUBLIC_PACKAGE_SCRIPT_KEYS0,
  PUBLIC_PACKAGE_SCRIPT_TARGETS0,
} from '../pcc-public-surface-freeze0.mjs';

test('CheckPublicEntryReleaseSurface0 accepts the current public release surface', async () => {
  const out = await CheckPublicEntryReleaseSurface0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckPublicEntryReleaseSurface0');
  assert.equal(out.NF.kind, 'PublicEntryReleaseSurface0NF');
  assert.equal(out.NF.surfaceFrozen, true);
  assert.deepEqual(out.NF.publicEntryExportKeys, PUBLIC_ENTRY_EXPORT_KEYS0);
  assert.deepEqual(out.NF.packageExportKeys, Object.keys(PUBLIC_PACKAGE_EXPORTS0).sort());
  assert.deepEqual(out.NF.packageBinKeys, Object.keys(PUBLIC_PACKAGE_BIN0).sort());
  assert.deepEqual(out.NF.packageScriptKeys, PUBLIC_PACKAGE_SCRIPT_KEYS0);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('public entry export keys match the frozen key list', () => {
  assert.deepEqual(Object.keys(publicEntry0).sort(), PUBLIC_ENTRY_EXPORT_KEYS0);
});

test('CheckPublicEntryReleaseSurface0 rejects a missing public entry export', async () => {
  const entryOverride = Object.fromEntries(Object.entries(publicEntry0));

  delete entryOverride.RunAll0;

  const out = await CheckPublicEntryReleaseSurface0({
    publicEntryOverride: entryOverride,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPublicEntryReleaseSurface0');
  assert.equal(out.Coord, 'CheckPublicEntryReleaseSurface0.publicEntryExports');
  assert.deepEqual(out.Path, ['index.mjs', 'exports']);
  assert.equal(out.Witness.reason, 'public release surface keys changed');
  assert.deepEqual(out.Witness.detail.missingKeys, ['RunAll0']);
});

test('CheckPublicEntryReleaseSurface0 rejects an extra public entry export', async () => {
  const entryOverride = {
    ...Object.fromEntries(Object.entries(publicEntry0)),
    UnexpectedPublicExport0: true,
  };

  const out = await CheckPublicEntryReleaseSurface0({
    publicEntryOverride: entryOverride,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPublicEntryReleaseSurface0');
  assert.equal(out.Coord, 'CheckPublicEntryReleaseSurface0.publicEntryExports');
  assert.deepEqual(out.Path, ['index.mjs', 'exports']);
  assert.equal(out.Witness.reason, 'public release surface keys changed');
  assert.deepEqual(out.Witness.detail.extraKeys, ['UnexpectedPublicExport0']);
});

test('CheckPublicEntryReleaseSurface0 rejects a changed package export target', async () => {
  const pkg = await readPackageJson0();

  pkg.exports = {
    ...pkg.exports,
    './runall0': './wrong-runall0.mjs',
  };

  const out = await CheckPublicEntryReleaseSurface0({
    packageJsonOverride: pkg,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPublicEntryReleaseSurface0');
  assert.equal(out.Coord, 'CheckPublicEntryReleaseSurface0.packageExports');
  assert.deepEqual(out.Path, ['package.json', 'exports', './runall0']);
  assert.equal(out.Witness.reason, 'public release surface mapping value changed');
});

test('CheckPublicEntryReleaseSurface0 rejects a changed package bin target', async () => {
  const pkg = await readPackageJson0();

  pkg.bin = {
    ...pkg.bin,
    'pnp-runall0': './bin/not-runall0.mjs',
  };

  const out = await CheckPublicEntryReleaseSurface0({
    packageJsonOverride: pkg,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPublicEntryReleaseSurface0');
  assert.equal(out.Coord, 'CheckPublicEntryReleaseSurface0.packageBin');
  assert.deepEqual(out.Path, ['package.json', 'bin', 'pnp-runall0']);
  assert.equal(out.Witness.reason, 'public release surface mapping value changed');
});

test('CheckPublicEntryReleaseSurface0 rejects a missing package script', async () => {
  const pkg = await readPackageJson0();

  delete pkg.scripts['materialized:public-status-roundtrip'];

  const out = await CheckPublicEntryReleaseSurface0({
    packageJsonOverride: pkg,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPublicEntryReleaseSurface0');
  assert.equal(out.Coord, 'CheckPublicEntryReleaseSurface0.packageScripts');
  assert.deepEqual(out.Path, ['package.json', 'scripts']);
  assert.equal(out.Witness.reason, 'public release surface keys changed');
  assert.deepEqual(out.Witness.detail.missingKeys, ['materialized:public-status-roundtrip']);
});

test('CheckPublicEntryReleaseSurface0 rejects a changed package script command', async () => {
  const pkg = await readPackageJson0();

  pkg.scripts = {
    ...pkg.scripts,
    'materialized:public-status-roundtrip': 'node ./bin/wrong.mjs',
  };

  const out = await CheckPublicEntryReleaseSurface0({
    packageJsonOverride: pkg,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPublicEntryReleaseSurface0');
  assert.equal(out.Coord, 'CheckPublicEntryReleaseSurface0.packageScripts');
  assert.deepEqual(out.Path, ['package.json', 'scripts', 'materialized:public-status-roundtrip']);
  assert.equal(out.Witness.reason, 'public release surface mapping value changed');
});

test('frozen package script key list matches frozen package script target map', () => {
  assert.deepEqual(Object.keys(PUBLIC_PACKAGE_SCRIPT_TARGETS0).sort(), PUBLIC_PACKAGE_SCRIPT_KEYS0);
});

test('README documents public entry release surface freeze', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Public entry release surface freeze'), true);
  assert.equal(readme.includes('CheckPublicEntryReleaseSurface0'), true);
  assert.equal(readme.includes('index.mjs export names'), true);
  assert.equal(readme.includes('package.json exports keys and values'), true);
  assert.equal(readme.includes('package.json bin keys and values'), true);
  assert.equal(readme.includes('package.json script keys and values'), true);
});

async function readPackageJson0() {
  return JSON.parse(await fs.readFile(new URL('../package.json', import.meta.url), 'utf8'));
}