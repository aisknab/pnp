import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedImports0,
  CheckMaterializedImportsFile0,
  MATERIALIZED_IMPORT_FORBIDDEN_EDGES0,
  makeMaterializedImportShell0,
} from '../pcc-materialized-imports0.mjs';

import {
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedImports0 accepts acyclic dependency-aligned artefact imports', async () => {
  const out = await CheckMaterializedImports0(makeMaterializedImportShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.NF.kind, 'MaterializedImports0NF');
  assert.deepEqual(out.NF.forbiddenEdges, MATERIALIZED_IMPORT_FORBIDDEN_EDGES0);
  assert.equal(out.Manifest.artefactImports.GPack.includes('GlobalFirewalls'), true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedImportsFile0 accepts an import skeleton shell file', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedImportShell0());

  const out = await CheckMaterializedImportsFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedImportsFile0');
  assert.equal(out.NF.kind, 'MaterializedImportsFile0NF');
  assert.equal(out.NF.artefactImportCount > 0, true);
});

test('CheckMaterializedImports0 rejects missing import policy', async () => {
  const shell = makeMaterializedImportShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.Manifest.importPolicy;

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedImports0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.Coord, 'CheckMaterializedImports0.importPolicy');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'importPolicy']);
  assert.equal(out.Witness.reason, 'Pack.Manifest importPolicy must be an object');
});

test('CheckMaterializedImports0 rejects missing artefact import list', async () => {
  const shell = makeMaterializedImportShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.Manifest.artefactImports.GPack;

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedImports0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.Coord, 'CheckMaterializedImports0.artefactImports');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactImports', 'GPack']);
  assert.equal(out.Witness.reason, 'Pack.Manifest artefactImports is missing an artefact key');
});

test('CheckMaterializedImports0 rejects forward artefact imports', async () => {
  const shell = makeMaterializedImportShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactImports.GPack = [
    'GlobalFirewalls',
    'FinalTheorem',
  ];

  pack.GPack = {
    ...pack.GPack,
    imports: pack.Manifest.artefactImports.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedImports0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.Coord, 'CheckMaterializedImports0.artefactImportEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactImports', 'GPack', 1]);
  assert.equal(out.Witness.reason, 'artefact import must point to an earlier artefact');
});

test('CheckMaterializedImports0 rejects artefact import to AcceptRun', async () => {
  const shell = makeMaterializedImportShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactImports.FinalTheorem = [
    'FinalIntegration',
    'AcceptRun',
  ];

  pack.FinalTheorem = {
    ...pack.FinalTheorem,
    imports: pack.Manifest.artefactImports.FinalTheorem,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedImports0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.Coord, 'CheckMaterializedImports0.artefactImportEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactImports', 'FinalTheorem', 1]);
  assert.equal(out.Witness.reason, 'artefact import must not target AcceptRun');
});

test('CheckMaterializedImports0 rejects artefact imports that do not match dependencies', async () => {
  const shell = makeMaterializedImportShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactImports.GPack = [];

  pack.GPack = {
    ...pack.GPack,
    imports: [],
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedImports0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.Coord, 'CheckMaterializedImports0.artefactImportEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactImports', 'GPack']);
  assert.equal(out.Witness.reason, 'artefact imports must match artefactDependencies');
});

test('CheckMaterializedImports0 rejects artefact declared imports mismatch', async () => {
  const shell = makeMaterializedImportShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack = {
    ...pack.GPack,
    imports: [],
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedImports0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.Coord, 'CheckMaterializedImports0.declaredArtefactImports');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'imports']);
  assert.equal(out.Witness.reason, 'materialized artefact imports must match Pack.Manifest artefactImports');
});

test('CheckMaterializedImports0 rejects manifest importEdges not declared in artefactImports', async () => {
  const shell = makeMaterializedImportShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.importEdges = [
    ...pack.Manifest.importEdges,
    {
      from: 'GPack',
      to: 'FinalTheorem',
    },
  ];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedImports0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.Coord, 'CheckMaterializedImports0.manifestImportEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'importEdges', pack.Manifest.importEdges.length - 1]);
  assert.equal(out.Witness.reason, 'Pack.Manifest importEdges contains an edge not declared in artefactImports');
});

test('CheckMaterializedImports0 rejects forbidden package edge O to G', async () => {
  const shell = makeMaterializedImportShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.packageImportEdges = [
    {
      from: 'O',
      to: 'G',
    },
  ];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedImports0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.Coord, 'CheckMaterializedImports0.packageImportEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'packageImportEdges', 0]);
  assert.equal(out.Witness.reason, 'package import uses a forbidden edge');
});

test('CheckMaterializedImports0 rejects package import cycles', async () => {
  const shell = makeMaterializedImportShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.packageImportEdges = [
    {
      from: 'A',
      to: 'B',
    },
    {
      from: 'B',
      to: 'A',
    },
  ];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedImports0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedImports0');
  assert.equal(out.Coord, 'CheckMaterializedImports0.packageImportEdges');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'packageImportEdges']);
  assert.equal(out.Witness.reason, 'package import graph contains a cycle');
});

async function writeTempShellFile0(t, shell) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-imports-'));
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