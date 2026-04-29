import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedArtefactDeps0,
  CheckMaterializedArtefactDepsFile0,
  MATERIALIZED_ARTEFACT_ORDER0,
  makeMaterializedArtefactDependencyShell0,
} from '../pcc-materialized-artefact-deps0.mjs';

import {
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedArtefactDeps0 accepts backward-only artefact dependencies', async () => {
  const out = await CheckMaterializedArtefactDeps0(makeMaterializedArtefactDependencyShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedArtefactDeps0');
  assert.equal(out.NF.kind, 'MaterializedArtefactDeps0NF');
  assert.deepEqual(out.NF.artefactOrder, MATERIALIZED_ARTEFACT_ORDER0);
  assert.equal(out.NF.artefactCount, MATERIALIZED_ARTEFACT_ORDER0.length);
  assert.equal(out.Manifest.artefactDependencies.GPack.includes('GlobalFirewalls'), true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedArtefactDepsFile0 accepts a dependency shell file', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedArtefactDependencyShell0());

  const out = await CheckMaterializedArtefactDepsFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedArtefactDepsFile0');
  assert.equal(out.NF.kind, 'MaterializedArtefactDepsFile0NF');
  assert.equal(out.NF.artefactCount, MATERIALIZED_ARTEFACT_ORDER0.length);
});

test('CheckMaterializedArtefactDeps0 rejects a missing dependency entry', async () => {
  const shell = makeMaterializedArtefactDependencyShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.Manifest.artefactDependencies.GPack;

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedArtefactDeps0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactDeps0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactDeps0.dependencyShape');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactDependencies', 'GPack']);
  assert.equal(out.Witness.reason, 'artefactDependencies is missing a required artefact key');
});

test('CheckMaterializedArtefactDeps0 rejects dependency on unknown artefact', async () => {
  const shell = makeMaterializedArtefactDependencyShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactDependencies.GPack = [
    'GlobalFirewalls',
    'UnknownArtefact0',
  ];

  pack.GPack = {
    ...pack.GPack,
    dependencies: pack.Manifest.artefactDependencies.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedArtefactDeps0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactDeps0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactDeps0.dependencyEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactDependencies', 'GPack', 1]);
  assert.equal(out.Witness.reason, 'artefact dependency points to an unknown artefact');
});

test('CheckMaterializedArtefactDeps0 rejects dependency on AcceptRun', async () => {
  const shell = makeMaterializedArtefactDependencyShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactDependencies.FinalTheorem = [
    'FinalIntegration',
    'AcceptRun',
  ];

  pack.FinalTheorem = {
    ...pack.FinalTheorem,
    dependencies: pack.Manifest.artefactDependencies.FinalTheorem,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedArtefactDeps0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactDeps0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactDeps0.dependencyEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactDependencies', 'FinalTheorem', 1]);
  assert.equal(out.Witness.reason, 'artefact dependency must not point to AcceptRun');
});

test('CheckMaterializedArtefactDeps0 rejects forward dependency', async () => {
  const shell = makeMaterializedArtefactDependencyShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactDependencies.GPack = [
    'GlobalFirewalls',
    'FinalTheorem',
  ];

  pack.GPack = {
    ...pack.GPack,
    dependencies: pack.Manifest.artefactDependencies.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedArtefactDeps0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactDeps0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactDeps0.dependencyEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactDependencies', 'GPack', 1]);
  assert.equal(out.Witness.reason, 'artefact dependency must point to an earlier artefact');
});

test('CheckMaterializedArtefactDeps0 rejects self dependency', async () => {
  const shell = makeMaterializedArtefactDependencyShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactDependencies.GPack = [
    'GlobalFirewalls',
    'GPack',
  ];

  pack.GPack = {
    ...pack.GPack,
    dependencies: pack.Manifest.artefactDependencies.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedArtefactDeps0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactDeps0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactDeps0.dependencyEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactDependencies', 'GPack', 1]);
  assert.equal(out.Witness.reason, 'artefact dependency must not be self-referential');
});

test('CheckMaterializedArtefactDeps0 rejects duplicate artefact order entries', async () => {
  const shell = makeMaterializedArtefactDependencyShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactOrder = [
    ...pack.Manifest.artefactOrder,
  ];

  pack.Manifest.artefactOrder[1] = pack.Manifest.artefactOrder[0];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedArtefactDeps0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactDeps0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactDeps0.artefactOrder');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactOrder', 1]);
  assert.equal(out.Witness.reason, 'artefactOrder entries must be unique');
});

test('CheckMaterializedArtefactDeps0 rejects artefact dependency declaration mismatch', async () => {
  const shell = makeMaterializedArtefactDependencyShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack = {
    ...pack.GPack,
    dependencies: [],
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedArtefactDeps0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactDeps0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactDeps0.declaredArtefactDependencies');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'dependencies']);
  assert.equal(out.Witness.reason, 'materialized artefact dependency list must match Pack.Manifest');
});

async function writeTempShellFile0(t, shell) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-artefact-deps-'));
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