import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedNoHiddenMin0,
  CheckMaterializedNoHiddenMinFile0,
  MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0,
  makeMaterializedNoHiddenMinShell0,
} from '../pcc-materialized-no-hidden-min0.mjs';

import {
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedNoHiddenMin0 accepts expanded no-hidden-min scans', async () => {
  const out = await CheckMaterializedNoHiddenMin0(makeMaterializedNoHiddenMinShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedNoHiddenMin0');
  assert.equal(out.NF.kind, 'MaterializedNoHiddenMin0NF');
  assert.deepEqual(out.NF.forbiddenSymbols, MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0);
  assert.equal(out.NF.occurrenceCount > 0, true);
  assert.equal(out.PackObject.GPack.noMinScan.importsScanned, true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedNoHiddenMinFile0 accepts a no-hidden-min shell file', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedNoHiddenMinShell0());

  const out = await CheckMaterializedNoHiddenMinFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedNoHiddenMinFile0');
  assert.equal(out.NF.kind, 'MaterializedNoHiddenMinFile0NF');
  assert.equal(out.NF.occurrenceCount > 0, true);
});

test('CheckMaterializedNoHiddenMin0 rejects missing noMinPolicy', async () => {
  const shell = makeMaterializedNoHiddenMinShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.Manifest.noMinPolicy;

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedNoHiddenMin0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedNoHiddenMin0');
  assert.equal(out.Coord, 'CheckMaterializedNoHiddenMin0.noMinPolicy');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'noMinPolicy']);
  assert.equal(out.Witness.reason, 'Pack.Manifest noMinPolicy must be an object');
});

test('CheckMaterializedNoHiddenMin0 rejects noMinPolicy missing expansion stage', async () => {
  const shell = makeMaterializedNoHiddenMinShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.noMinPolicy = {
    ...pack.Manifest.noMinPolicy,
    expansionStages: pack.Manifest.noMinPolicy.expansionStages.filter((entry) => entry !== 'imports'),
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedNoHiddenMin0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedNoHiddenMin0');
  assert.equal(out.Coord, 'CheckMaterializedNoHiddenMin0.noMinPolicy');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'noMinPolicy', 'expansionStages']);
  assert.equal(out.Witness.reason, 'noMinPolicy must include every expansion stage');
});

test('CheckMaterializedNoHiddenMin0 rejects missing artefact noMinScan', async () => {
  const shell = makeMaterializedNoHiddenMinShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.GPack.noMinScan;

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedNoHiddenMin0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedNoHiddenMin0');
  assert.equal(out.Coord, 'CheckMaterializedNoHiddenMin0.artefactNoMinScans');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'noMinScan']);
  assert.equal(out.Witness.reason, 'materialized artefact must declare noMinScan');
});

test('CheckMaterializedNoHiddenMin0 rejects executable minimumEquivalent occurrence', async () => {
  const shell = makeMaterializedNoHiddenMinShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.noMinScans.GPack = {
    ...pack.Manifest.noMinScans.GPack,
    occurrences: [
      ...pack.Manifest.noMinScans.GPack.occurrences,
      {
        identifier: 'minimumEquivalent',
        expandedIdentifier: 'µ*',
        occurrenceClass: 'ExecCall',
        source: 'bad executable call',
      },
    ],
  };

  pack.GPack = {
    ...pack.GPack,
    noMinScan: pack.Manifest.noMinScans.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedNoHiddenMin0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedNoHiddenMin0');
  assert.equal(out.Coord, 'CheckMaterializedNoHiddenMin0.occurrences');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'noMinScans', 'GPack', 'occurrences', pack.Manifest.noMinScans.GPack.occurrences.length - 1, 'identifier']);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckMaterializedNoHiddenMin0 rejects hidden executable symbol in artefact body', async () => {
  const shell = makeMaterializedNoHiddenMinShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack = {
    ...pack.GPack,
    body: [
      'minimumEquivalent',
    ],
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedNoHiddenMin0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedNoHiddenMin0');
  assert.equal(out.Coord, 'CheckMaterializedNoHiddenMin0.executableScan');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckMaterializedNoHiddenMin0 rejects noMinScan mismatch with manifest', async () => {
  const shell = makeMaterializedNoHiddenMinShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack.noMinScan = {
    ...pack.GPack.noMinScan,
    importsScanned: false,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedNoHiddenMin0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedNoHiddenMin0');
  assert.equal(out.Coord, 'CheckMaterializedNoHiddenMin0.artefactNoMinScans');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'noMinScan', 'importsScanned']);
  assert.equal(out.Witness.reason, 'materialized no-min scan must certify importsScanned');
});

test('CheckMaterializedNoHiddenMin0 rejects noMinScan digest mismatch', async () => {
  const shell = makeMaterializedNoHiddenMinShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.noMinScans.GPack = {
    ...pack.Manifest.noMinScans.GPack,
    digest: {
      alg: 'SHA256',
      bytes: 'utf8',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  pack.GPack = {
    ...pack.GPack,
    noMinScan: pack.Manifest.noMinScans.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedNoHiddenMin0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedNoHiddenMin0');
  assert.equal(out.Coord, 'CheckMaterializedNoHiddenMin0.scanDigests');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'noMinScans', 'GPack', 'digest']);
  assert.equal(out.Witness.reason, 'manifest no-min scan digest mismatch');
});

async function writeTempShellFile0(t, shell) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-no-hidden-min-'));
  const filePath = path.join(dir, 'MaterializedPCCPack0.json');

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  await fs.writeFile(filePath, JSON.stringify(shell, null, 2), 'utf8');

  return filePath;
}

function resealShellPack0(shell, pack) {
  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);
}