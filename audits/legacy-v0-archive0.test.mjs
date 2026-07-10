import assert from 'node:assert/strict';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckLegacyV0Archive0,
  LEGACY_V0_ARCHIVE_PINS0,
} from '../pcc-legacy-v0-archive0.mjs';

const ARCHIVE_URL = new URL('../archive/legacy-v0/ARCHIVE.json', import.meta.url);

async function archive0() {
  return JSON.parse(await readFile(ARCHIVE_URL, 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

async function checkMutatedManifest0(manifest) {
  const root = await mkdtemp(path.join(os.tmpdir(), 'pnp-legacy-v0-manifest-'));
  try {
    await mkdir(path.join(root, 'archive', 'legacy-v0'), { recursive: true });
    await writeFile(
      path.join(root, 'archive', 'legacy-v0', 'ARCHIVE.json'),
      `${JSON.stringify(manifest, null, 2)}\n`,
      'utf8',
    );
    return await CheckLegacyV0Archive0({ root });
  } finally {
    await rm(root, { recursive: true, force: true });
  }
}

test('legacy-v0 archive pins and verifies all three annotated releases', async () => {
  const out = await CheckLegacyV0Archive0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-LEGACY-V0-ARCHIVE-2026-07-10-01');
  assert.equal(out.archiveManifestAccepted, true);
  assert.equal(out.tagObjectIdentityVerified, true);
  assert.equal(out.archivedFileDigestsVerified, true);
  assert.equal(out.artifactChecksumLedgerVerified, true);
  assert.equal(out.verifiedTagCount, 3);
  assert.equal(out.verifiedFileCount, 10);
  assert.equal(out.tagsAnnotated, true);
  assert.equal(out.tagsSigned, false);
  assert.equal(out.signedProvenanceEstablished, false);
});

test('legacy-v0 archive accepted verdict cannot establish current theorem authority', async () => {
  const out = await CheckLegacyV0Archive0();

  assert.equal(out.historicalReplay, true);
  assert.equal(out.currentStatusAuthority, false);
  assert.equal(out.mathematicalTheoremEstablished, false);
  assert.equal(out.checkerReplayIsMathematicalProof, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(out.historicalValidationRecorded, true);
  assert.equal(out.historicalValidationReexecuted, false);
});

test('legacy-v0 exported pins preserve exact tag object, commit, and tree identities', () => {
  assert.deepEqual(
    {
      source: LEGACY_V0_ARCHIVE_PINS0.source.tag,
      artifacts: LEGACY_V0_ARCHIVE_PINS0.artifacts.tag,
      documents: LEGACY_V0_ARCHIVE_PINS0.documents.tag,
    },
    {
      source: {
        name: 'final-pnp-proof-report-hardened-7072f8d',
        object: '9b69c4f8d8d6d62eb359af759288e5794d1c81c2',
        commit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
        tree: '2b673c397c8438a0631952c2d0325456e96c5341',
        annotated: true,
        signed: false,
      },
      artifacts: {
        name: 'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
        object: 'e7ea459c907ed9e334af8c0bd5f3bb117348992d',
        commit: '9d1de19f827e5cb6880741352eb2349cbbb45994',
        tree: 'fa34921ab6279b2258436b325326d32bfb40fd36',
        annotated: true,
        signed: false,
      },
      documents: {
        name: 'final-pnp-proof-report-docs-hardened-7072f8d-sealed',
        object: '9eeb4b85af1c04c43e6f086debcd3ac37d5d27d1',
        commit: '3ba356c79b545d2c734283bf10d85d0710de2b60',
        tree: '4f0c3b5d93da1783be1c24560dac3bf4023370f8',
        annotated: true,
        signed: false,
      },
    },
  );
});

test('legacy-v0 archive rejects a mutated manifest tag-object pin', async () => {
  const manifest = clone0(await archive0());
  manifest.source.tag.object = '0'.repeat(40);

  const out = await checkMutatedManifest0(manifest);
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LegacyV0Archive.ManifestField');
  assert.deepEqual(out.path, ['source', 'tag', 'object']);
});

test('legacy-v0 archive rejects a false signed-provenance claim', async () => {
  const manifest = clone0(await archive0());
  manifest.artifacts.tag.signed = true;

  const out = await checkMutatedManifest0(manifest);
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LegacyV0Archive.ManifestField');
  assert.deepEqual(out.path, ['artifacts', 'tag', 'signed']);
});

test('legacy-v0 archive rejects a mutated sealed-file digest', async () => {
  const manifest = clone0(await archive0());
  manifest.artifacts.files[4].sha256 = 'f'.repeat(64);

  const out = await checkMutatedManifest0(manifest);
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LegacyV0Archive.ManifestField');
  assert.deepEqual(out.path, ['artifacts', 'files', 4, 'sha256']);
});

test('legacy-v0 production checker rejects injected Git tag identities', async () => {
  const sourceTag = clone0(LEGACY_V0_ARCHIVE_PINS0.source.tag);
  sourceTag.tree = '0'.repeat(40);

  const out = await CheckLegacyV0Archive0({
    tagIdentityOverrides: {
      [sourceTag.name]: sourceTag,
    },
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LegacyV0Archive.TestOverrideForbidden');
  assert.deepEqual(out.path, ['tagIdentityOverrides']);
  assert.equal(out.tagObjectIdentityVerified, undefined);
});

test('legacy-v0 production checker rejects injected archived bytes', async () => {
  const file = LEGACY_V0_ARCHIVE_PINS0.documents.files[0];
  const key = `${LEGACY_V0_ARCHIVE_PINS0.documents.tag.commit}:${file.path}`;
  const out = await CheckLegacyV0Archive0({
    fileBytesOverrides: {
      [key]: Buffer.from('not the pinned PDF', 'utf8'),
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LegacyV0Archive.TestOverrideForbidden');
  assert.deepEqual(out.path, ['fileBytesOverrides']);
  assert.equal(out.archivedFileDigestsVerified, undefined);
});

test('legacy-v0 archive rejects any attempt to activate current authority', async () => {
  const manifest = clone0(await archive0());
  manifest.claimBoundary.currentStatusAuthority = true;

  const out = await checkMutatedManifest0(manifest);
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LegacyV0Archive.ManifestField');
  assert.deepEqual(out.path, ['claimBoundary', 'currentStatusAuthority']);
  assert.equal(out.currentStatusAuthority, false);
  assert.equal(out.mathematicalTheoremEstablished, false);
});

test('legacy-v0 archive cannot accept fully injected evidence outside Git', async () => {
  const out = await CheckLegacyV0Archive0({
    root: '/definitely/not/a/git/repo',
    manifestOverride: await archive0(),
    tagIdentityOverrides: {},
    fileBytesOverrides: {},
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'LegacyV0Archive.TestOverrideForbidden');
  assert.deepEqual(out.path, [
    'manifestOverride',
    'tagIdentityOverrides',
    'fileBytesOverrides',
  ]);
  assert.equal(out.currentStatusAuthority, false);
  assert.equal(out.mathematicalTheoremEstablished, false);
});

test('legacy-v0 archive fails closed when its manifest is unavailable', async () => {
  const root = await mkdtemp(path.join(os.tmpdir(), 'pnp-legacy-v0-missing-'));
  try {
    const out = await CheckLegacyV0Archive0({ root });
    assert.equal(out.tag, 'reject');
    assert.equal(out.coord, 'LegacyV0Archive.ReadOrParse');
    assert.deepEqual(out.path, ['archive/legacy-v0/ARCHIVE.json']);
    assert.equal(out.currentStatusAuthority, false);
    assert.equal(out.publicTheoremEmissionAllowed, false);
  } finally {
    await rm(root, { recursive: true, force: true });
  }
});
