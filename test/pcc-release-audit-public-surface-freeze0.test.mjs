import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
} from '../pcc-release-audit0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function makePublicSurfaceAcceptRecord0(overrides = {}) {
  const nf = {
    kind: 'PublicEntryReleaseSurface0NF',
    checker: 'CheckPublicEntryReleaseSurface0',
    version: 0,
    publicEntryExportCount: 20,
    publicEntryExportKeys: [
      'RunAll0',
    ],
    packageExportCount: 5,
    packageExportKeys: [
      '.',
    ],
    packageBinCount: 2,
    packageBinKeys: [
      'pnp-runall0',
    ],
    packageScriptCount: 32,
    packageScriptKeys: [
      'validate',
    ],
    packageMain: './index.mjs',
    packageType: 'module',
    surfaceFrozen: true,
    ...overrides,
  };

  return {
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckPublicEntryReleaseSurface0',
    version: 0,
    NF: nf,
    Digest: digestCanonical0(nf),
    Ledger: [],
    nf,
    digest: digestCanonical0(nf),
    ledger: [],
  };
}

async function runReleaseAuditWithPublicSurfaceRecord0(record, overrides = {}) {
  return CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: true,
    publicSurfaceFreezeRunner: async () => record,
    runMaterializedPublicStatusGate: false,
    ...overrides,
  }));
}

test('CheckReleaseAudit0 executes the public surface freeze phase', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: true,
    runMaterializedPublicStatusGate: false,
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');

  const phase = out.Ledger.find((entry) => entry.phase === 'publicSurfaceFreeze');

  assert.equal(phase.status, 'pass');
  assert.match(phase.digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckReleaseAudit0 can skip public surface freeze by explicit internal config', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
  }));

  assert.equal(out.tag, 'accept');

  const phase = out.Ledger.find((entry) => entry.phase === 'publicSurfaceFreeze');

  assert.equal(phase.status, 'pass');
});

test('CheckReleaseAudit0 rejects when public surface freeze checker rejects', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0({
    tag: 'reject',
    kind: 'reject',
    checker: 'CheckPublicEntryReleaseSurface0',
    Coord: 'CheckPublicEntryReleaseSurface0.packageScripts',
    Path: [
      'package.json',
      'scripts',
    ],
    Witness: {
      reason: 'public release surface keys changed',
    },
    Digest: digestCanonical0({
      kind: 'BadPublicSurfaceFreezeRejectNF',
    }),
    Ledger: [],
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckPublicEntryReleaseSurface0.packageScripts');
});

test('CheckReleaseAudit0 rejects public surface freeze accept record with wrong NF kind', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0({
    kind: 'WrongPublicSurfaceNF',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF', 'kind']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker emitted the wrong NF kind');
});

test('CheckReleaseAudit0 rejects public surface freeze accept record without surfaceFrozen=true', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0({
    surfaceFrozen: false,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF', 'surfaceFrozen']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker must certify surfaceFrozen=true');
});

test('CheckReleaseAudit0 rejects public surface freeze accept record without export count', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0({
    publicEntryExportCount: 0,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF', 'publicEntryExportCount']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker must count public entry exports');
});

test('CheckReleaseAudit0 validates public surface freeze config shape', async () => {
  const out = await CheckReleaseAudit0({
    ...makeReleaseAuditConfig0(),
    runPublicSurfaceFreeze: 'yes',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.input');
  assert.deepEqual(out.Path, ['runPublicSurfaceFreeze']);
  assert.equal(out.Witness.reason, 'ReleaseAuditConfig0 runPublicSurfaceFreeze must be boolean');
});

test('README documents release audit public surface freeze phase', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Release audit public surface freeze phase'), true);
  assert.equal(readme.includes('publicSurfaceFreeze'), true);
  assert.equal(readme.includes('index.mjs public export names'), true);
  assert.equal(readme.includes('package.json exports map'), true);
  assert.equal(readme.includes('package.json bin map'), true);
  assert.equal(readme.includes('package.json script map'), true);
});