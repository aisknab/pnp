import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  ACCEPT_RUN_PHASES0,
} from '../pcc-accept-run0.mjs';

import {
  PCCPACK_REQUIRED_FIELDS0,
} from '../pcc-pack-sufficiency0.mjs';

import {
  CheckMaterializedPhaseManifest0,
  CheckMaterializedPhaseManifestFile0,
  MATERIALIZED_PHASE_MANIFEST_KIND0,
  makeMaterializedPhaseManifestShell0,
} from '../pcc-materialized-phase-manifest0.mjs';

import {
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedPhaseManifest0 accepts a shell with a concrete phase manifest inside PackBytes', async () => {
  const out = await CheckMaterializedPhaseManifest0(makeMaterializedPhaseManifestShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPhaseManifest0');
  assert.equal(out.NF.kind, 'MaterializedPhaseManifest0NF');
  assert.equal(out.Manifest.kind, MATERIALIZED_PHASE_MANIFEST_KIND0);
  assert.equal(out.NF.phaseCount, ACCEPT_RUN_PHASES0.length);
  assert.equal(out.NF.artefactCount, PCCPACK_REQUIRED_FIELDS0.length);
  assert.equal(out.NF.publicClaimBoundary.consequent, 'P = NP');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedPhaseManifestFile0 accepts a phase manifest shell file', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedPhaseManifestShell0());

  const out = await CheckMaterializedPhaseManifestFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPhaseManifestFile0');
  assert.equal(out.NF.kind, 'MaterializedPhaseManifestFile0NF');
  assert.equal(out.NF.phaseCount, ACCEPT_RUN_PHASES0.length);
});

test('CheckMaterializedPhaseManifest0 rejects a missing Pack.Manifest', async () => {
  const shell = makeMaterializedPhaseManifestShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.Manifest;

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedPhaseManifest0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPhaseManifest0');
  assert.equal(out.Coord, 'CheckMaterializedPhaseManifest0.manifest');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest']);
  assert.equal(out.Witness.reason, 'Pack.Manifest must be an object');
});

test('CheckMaterializedPhaseManifest0 rejects phase order mismatch', async () => {
  const shell = makeMaterializedPhaseManifestShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest = {
    ...pack.Manifest,
    phaseOrder: [...pack.Manifest.phaseOrder],
  };

  pack.Manifest.phaseOrder[0] = 'BadPhase';

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedPhaseManifest0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPhaseManifest0');
  assert.equal(out.Coord, 'CheckMaterializedPhaseManifest0.phaseOrder');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'phaseOrder', 0]);
  assert.equal(out.Witness.reason, 'Pack.Manifest phaseOrder mismatch');
});

test('CheckMaterializedPhaseManifest0 rejects missing required artefact', async () => {
  const shell = makeMaterializedPhaseManifestShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest = {
    ...pack.Manifest,
    requiredArtefacts: pack.Manifest.requiredArtefacts.filter((entry) => entry !== 'GPack'),
  };

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedPhaseManifest0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPhaseManifest0');
  assert.equal(out.Coord, 'CheckMaterializedPhaseManifest0.requiredArtefacts');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'requiredArtefacts', 'GPack']);
  assert.equal(out.Witness.reason, 'Pack.Manifest is missing a required package artefact');
});

test('CheckMaterializedPhaseManifest0 rejects manifest coreDigest mismatch', async () => {
  const shell = makeMaterializedPhaseManifestShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest = {
    ...pack.Manifest,
    coreDigest: {
      ...pack.Manifest.coreDigest,
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedPhaseManifest0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPhaseManifest0');
  assert.equal(out.Coord, 'CheckMaterializedPhaseManifest0.digestLinks');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'coreDigest']);
  assert.equal(out.Witness.reason, 'Pack.Manifest coreDigest must match envelope CoreDigest');
});

test('CheckMaterializedPhaseManifest0 rejects manifest core boundary false', async () => {
  const shell = makeMaterializedPhaseManifestShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest = {
    ...pack.Manifest,
    coreExcludesAcceptRun: false,
  };

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedPhaseManifest0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPhaseManifest0');
  assert.equal(out.Coord, 'CheckMaterializedPhaseManifest0.coreBoundary');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'coreExcludesAcceptRun']);
  assert.equal(out.Witness.reason, 'Pack.Manifest must certify that Core excludes AcceptRun');
});

test('CheckMaterializedPhaseManifest0 rejects digest-only equality policy', async () => {
  const shell = makeMaterializedPhaseManifestShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest = {
    ...pack.Manifest,
    canonicalBytePolicy: {
      ...pack.Manifest.canonicalBytePolicy,
      digestEqualityIsNotObjectEquality: false,
    },
  };

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedPhaseManifest0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPhaseManifest0');
  assert.equal(out.Coord, 'CheckMaterializedPhaseManifest0.canonicalBytePolicy');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'canonicalBytePolicy', 'digestEqualityIsNotObjectEquality']);
  assert.equal(out.Witness.reason, 'Pack.Manifest canonicalBytePolicy must certify digestEqualityIsNotObjectEquality');
});

test('CheckMaterializedPhaseManifest0 rejects non-conditional public claim boundary', async () => {
  const shell = makeMaterializedPhaseManifestShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest = {
    ...pack.Manifest,
    publicClaimBoundary: {
      ...pack.Manifest.publicClaimBoundary,
      conditional: false,
    },
  };

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedPhaseManifest0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPhaseManifest0');
  assert.equal(out.Coord, 'CheckMaterializedPhaseManifest0.publicClaimBoundary');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'publicClaimBoundary', 'conditional']);
  assert.equal(out.Witness.reason, 'Pack.Manifest public claim boundary must be conditional');
});

async function writeTempShellFile0(t, shell) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-phase-manifest-'));
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