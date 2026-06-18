import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedAggregate0,
  CheckMaterializedAggregateFile0,
  MATERIALIZED_AGGREGATE_PHASES0,
  makeMaterializedAggregateShell0,
} from '../pcc-materialized-aggregate0.mjs';

import {
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedAggregate0 accepts the complete materialized shell skeleton', async () => {
  const out = await CheckMaterializedAggregate0(makeMaterializedAggregateShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.NF.kind, 'MaterializedAggregate0NF');
  assert.deepEqual(out.NF.phaseOrder, MATERIALIZED_AGGREGATE_PHASES0);
  assert.equal(out.NF.phaseCount, MATERIALIZED_AGGREGATE_PHASES0.length);
  assert.equal(out.NF.phaseDigests.length, MATERIALIZED_AGGREGATE_PHASES0.length);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkPCCPackStatus, 'pending');
  assert.equal(out.NF.checkPCCPackAccepted, false);
  assert.equal(out.NF.checkPCCPackStrict, false);  
});

test('CheckMaterializedAggregateFile0 accepts an aggregate shell file', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedAggregateShell0());

  const out = await CheckMaterializedAggregateFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAggregateFile0');
  assert.equal(out.NF.kind, 'MaterializedAggregateFile0NF');
  assert.equal(out.NF.phaseCount, MATERIALIZED_AGGREGATE_PHASES0.length);
});

test('CheckMaterializedAggregate0 rejects shell validation failure first', async () => {
  const shell = makeMaterializedAggregateShell0();

  shell.CoreDigest = {
    ...shell.CoreDigest,
    hex: '0000000000000000000000000000000000000000000000000000000000000000',
  };

  const out = await CheckMaterializedAggregate0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.Coord, 'CheckMaterializedAggregate0.CheckMaterializedPCCPackShell0');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.reason, 'CheckMaterializedPCCPackShell0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedPCCPackShell0.canonicalBytes');
});

test('CheckMaterializedAggregate0 rejects core extraction failure at the core phase', async () => {
  const shell = makeMaterializedAggregateShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Core = {
    ...pack.Core,
    packageId: 'DifferentConcreteCore0',
  };

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedAggregate0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.Coord, 'CheckMaterializedAggregate0.ExtractMaterializedCore0');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.reason, 'ExtractMaterializedCore0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'ExtractMaterializedCore0.packCoreLink');
});

test('CheckMaterializedAggregate0 rejects phase manifest failure at the manifest phase', async () => {
  const shell = makeMaterializedAggregateShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest = {
    ...pack.Manifest,
    phaseOrder: [
      ...pack.Manifest.phaseOrder,
    ],
  };

  pack.Manifest.phaseOrder[0] = 'BadPhase';

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedAggregate0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.Coord, 'CheckMaterializedAggregate0.CheckMaterializedPhaseManifest0');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedPhaseManifest0.phaseOrder');
});

test('CheckMaterializedAggregate0 rejects artefact inventory failure at the inventory phase', async () => {
  const shell = makeMaterializedAggregateShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.GPack;

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedAggregate0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.Coord, 'CheckMaterializedAggregate0.CheckMaterializedArtefactInventory0');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedArtefactInventory0.artefactInventory');
});

test('CheckMaterializedAggregate0 rejects dependency failure at the dependency phase', async () => {
  const shell = makeMaterializedAggregateShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactDependencies.GPack = [
    'GlobalFirewalls',
    'FinalTheorem',
  ];

  pack.GPack = {
    ...pack.GPack,
    dependencies: pack.Manifest.artefactDependencies.GPack,
    imports: pack.Manifest.artefactDependencies.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedAggregate0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.Coord, 'CheckMaterializedAggregate0.CheckMaterializedArtefactDeps0');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedArtefactDeps0.dependencyEdges');
});

test('CheckMaterializedAggregate0 rejects proof ref failure at the proof-ref phase', async () => {
  const shell = makeMaterializedAggregateShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack.proofRefs = [
    ...pack.GPack.proofRefs,
    {
      kind: 'ProofRef0',
      version: 0,
      refKind: 'EarlierArtefactProof',
      id: 'bad.forward.target',
      artefactName: 'FinalTheorem',
    },
  ];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedAggregate0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.Coord, 'CheckMaterializedAggregate0.CheckMaterializedProofRefs0');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedProofRefs0.proofRefs');
});

test('CheckMaterializedAggregate0 rejects bounds failure at the bounds phase', async () => {
  const shell = makeMaterializedAggregateShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactBounds.GPack = {
    ...pack.Manifest.artefactBounds.GPack,
    exponent: 0,
  };

  pack.GPack = {
    ...pack.GPack,
    bounds: pack.Manifest.artefactBounds.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedAggregate0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.Coord, 'CheckMaterializedAggregate0.CheckMaterializedBounds0');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedBounds0.manifestArtefactBounds');
});

test('CheckMaterializedAggregate0 rejects no-hidden-min failure at the no-min phase', async () => {
  const shell = makeMaterializedAggregateShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack = {
    ...pack.GPack,
    body: [
      'minimumEquivalent',
    ],
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedAggregate0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.Coord, 'CheckMaterializedAggregate0.CheckMaterializedNoHiddenMin0');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedNoHiddenMin0.executableScan');
});

test('CheckMaterializedAggregate0 rejects import failure at the import phase', async () => {
  const shell = makeMaterializedAggregateShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.packageImportEdges = [
    {
      from: 'O',
      to: 'G',
    },
  ];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedAggregate0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregate0');
  assert.equal(out.Coord, 'CheckMaterializedAggregate0.CheckMaterializedImports0');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedImports0.packageImportEdges');
});

async function writeTempShellFile0(t, shell) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-aggregate-'));
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