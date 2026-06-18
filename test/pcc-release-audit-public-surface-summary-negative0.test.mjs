import assert from 'node:assert/strict';
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
      './runall0',
      './integrated-pipeline0',
      './accept-run0',
      './release-audit0',
    ],
    packageBinCount: 2,
    packageBinKeys: [
      'pnp-release-audit0',
      'pnp-runall0',
    ],
    packageScriptCount: 30,
    packageScriptKeys: [
      'validate',
    ],
    packageMain: './index.mjs',
    packageType: 'module',
    surfaceFrozen: true,
    ...overrides,
  };

  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckPublicEntryReleaseSurface0',
    version: 0,
    NF: nf,
    Digest: digest,
    Ledger: [],
    nf,
    digest,
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

test('CheckReleaseAudit0 rejects public surface freeze accept record without an NF object', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0({
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckPublicEntryReleaseSurface0',
    version: 0,
    Digest: digestCanonical0({
      kind: 'MissingNF',
    }),
    Ledger: [],
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker must emit an NF object');
});

test('CheckReleaseAudit0 rejects public surface freeze accept record with wrong NF kind', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0({
    kind: 'WrongPublicSurfaceFreezeNF',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF', 'kind']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker emitted the wrong NF kind');
});

test('CheckReleaseAudit0 rejects public surface freeze accept record with surfaceFrozen=false', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0({
    surfaceFrozen: false,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF', 'surfaceFrozen']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker must certify surfaceFrozen=true');
});

test('CheckReleaseAudit0 rejects public surface freeze accept record with zero public entry export count', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0({
    publicEntryExportCount: 0,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF', 'publicEntryExportCount']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker must count public entry exports');
});

test('CheckReleaseAudit0 rejects public surface freeze accept record with zero package export count', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0({
    packageExportCount: 0,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF', 'packageExportCount']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker must count package exports');
});

test('CheckReleaseAudit0 rejects public surface freeze accept record with zero package bin count', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0({
    packageBinCount: 0,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF', 'packageBinCount']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker must count package bin entries');
});

test('CheckReleaseAudit0 rejects public surface freeze accept record with zero package script count', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0({
    packageScriptCount: 0,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.publicSurfaceFreeze');
  assert.deepEqual(out.Path, ['publicSurfaceFreeze', 'NF', 'packageScriptCount']);
  assert.equal(out.Witness.reason, 'public release surface freeze checker must count package scripts');
});

test('CheckReleaseAudit0 rejects public surface freeze runner reject record at publicSurfaceFreeze phase', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0({
    tag: 'reject',
    kind: 'reject',
    checker: 'CheckPublicEntryReleaseSurface0',
    version: 0,
    Coord: 'CheckPublicEntryReleaseSurface0.packageScripts',
    Path: [
      'package.json',
      'scripts',
    ],
    Witness: {
      reason: 'public release surface keys changed',
    },
    Digest: digestCanonical0({
      kind: 'SyntheticPublicSurfaceRejectNF',
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

test('CheckReleaseAudit0 accepts valid synthetic public surface freeze proof and exposes summary', async () => {
  const out = await runReleaseAuditWithPublicSurfaceRecord0(makePublicSurfaceAcceptRecord0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.NF.publicSurfaceFreeze, true);
  assert.equal(out.NF.publicSurfaceFreezeSummary.surfaceFrozen, true);
  assert.equal(out.NF.publicSurfaceFreezePublicEntryExportCount, 20);
  assert.equal(out.NF.publicSurfaceFreezePackageExportCount, 5);
  assert.equal(out.NF.publicSurfaceFreezePackageBinCount, 2);
  assert.equal(out.NF.publicSurfaceFreezePackageScriptCount, 30);
});

test('README documents public surface freeze negative coverage', async () => {
  const readme = await import('node:fs/promises').then((fs) => (
    fs.readFile(new URL('../README.md', import.meta.url), 'utf8')
  ));

  assert.equal(readme.includes('Release audit public surface freeze negative coverage'), true);
  assert.equal(readme.includes('wrong normal-form kind'), true);
  assert.equal(readme.includes('surfaceFrozen = false'), true);
  assert.equal(readme.includes('zero public entry export count'), true);
  assert.equal(readme.includes('zero package script count'), true);
  assert.equal(readme.includes('CheckReleaseAudit0.publicSurfaceFreeze'), true);
});