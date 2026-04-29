import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedProofRefs0,
  CheckMaterializedProofRefsFile0,
  MATERIALIZED_PROOF_REF_KINDS0,
  makeMaterializedProofRefShell0,
} from '../pcc-materialized-proof-refs0.mjs';

import {
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedProofRefs0 accepts proof refs for every materialized artefact', async () => {
  const out = await CheckMaterializedProofRefs0(makeMaterializedProofRefShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.NF.kind, 'MaterializedProofRefs0NF');
  assert.deepEqual(out.NF.allowedRefKinds, MATERIALIZED_PROOF_REF_KINDS0);
  assert.equal(out.NF.proofRefCount > 0, true);
  assert.equal(out.PackObject.GPack.proofRefs.some((ref) => ref.refKind === 'EarlierArtefactProof'), true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedProofRefsFile0 accepts a proof-ref shell file', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedProofRefShell0());

  const out = await CheckMaterializedProofRefsFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedProofRefsFile0');
  assert.equal(out.NF.kind, 'MaterializedProofRefsFile0NF');
  assert.equal(out.NF.proofRefCount > 0, true);
});

test('CheckMaterializedProofRefs0 rejects missing proofRefs list', async () => {
  const shell = makeMaterializedProofRefShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.GPack.proofRefs;

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedProofRefs0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.Coord, 'CheckMaterializedProofRefs0.proofRefLists');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'proofRefs']);
  assert.equal(out.Witness.reason, 'materialized artefact must declare proofRefs');
});

test('CheckMaterializedProofRefs0 rejects unknown proof ref kind', async () => {
  const shell = makeMaterializedProofRefShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack.proofRefs = [
    ...pack.GPack.proofRefs,
    {
      kind: 'ProofRef0',
      version: 0,
      refKind: 'UnknownProofKind',
      id: 'bad.unknown',
    },
  ];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedProofRefs0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.Coord, 'CheckMaterializedProofRefs0.proofRefs');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'proofRefs', pack.GPack.proofRefs.length - 1, 'refKind']);
  assert.equal(out.Witness.reason, 'proofRef refKind is not allowed');
});

test('CheckMaterializedProofRefs0 rejects EarlierArtefactProof target to unknown artefact', async () => {
  const shell = makeMaterializedProofRefShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack.proofRefs = [
    ...pack.GPack.proofRefs,
    {
      kind: 'ProofRef0',
      version: 0,
      refKind: 'EarlierArtefactProof',
      id: 'bad.unknown.target',
      artefactName: 'NoSuchArtefact',
    },
  ];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedProofRefs0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.Coord, 'CheckMaterializedProofRefs0.proofRefs');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'proofRefs', pack.GPack.proofRefs.length - 1, 'artefactName']);
  assert.equal(out.Witness.reason, 'EarlierArtefactProof target is unknown');
});

test('CheckMaterializedProofRefs0 rejects forward EarlierArtefactProof target', async () => {
  const shell = makeMaterializedProofRefShell0();
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

  const out = await CheckMaterializedProofRefs0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.Coord, 'CheckMaterializedProofRefs0.proofRefs');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'proofRefs', pack.GPack.proofRefs.length - 1, 'artefactName']);
  assert.equal(out.Witness.reason, 'EarlierArtefactProof target must be an earlier artefact');
});

test('CheckMaterializedProofRefs0 rejects EarlierArtefactProof target to AcceptRun', async () => {
  const shell = makeMaterializedProofRefShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack.proofRefs = [
    ...pack.GPack.proofRefs,
    {
      kind: 'ProofRef0',
      version: 0,
      refKind: 'EarlierArtefactProof',
      id: 'bad.accept.run.target',
      artefactName: 'AcceptRun',
    },
  ];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedProofRefs0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.Coord, 'CheckMaterializedProofRefs0.proofRefs');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'proofRefs', pack.GPack.proofRefs.length - 1, 'artefactName']);
  assert.equal(out.Witness.reason, 'EarlierArtefactProof must not target AcceptRun');
});

test('CheckMaterializedProofRefs0 rejects dependency without EarlierArtefactProof coverage', async () => {
  const shell = makeMaterializedProofRefShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack.proofRefs = pack.GPack.proofRefs.filter((ref) => (
    !(ref.refKind === 'EarlierArtefactProof' && ref.artefactName === 'GlobalFirewalls')
  ));

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedProofRefs0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.Coord, 'CheckMaterializedProofRefs0.dependencyProofCoverage');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'proofRefs']);
  assert.equal(out.Witness.reason, 'materialized artefact proofRefs must cover every declared dependency');
});

test('CheckMaterializedProofRefs0 rejects duplicate proof ref ids', async () => {
  const shell = makeMaterializedProofRefShell0();
  const pack = JSON.parse(shell.PackBytes);
  const duplicate = pack.GPack.proofRefs[0];

  pack.FinalTheorem.proofRefs = [
    ...pack.FinalTheorem.proofRefs,
    {
      ...duplicate,
    },
  ];

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedProofRefs0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.Coord, 'CheckMaterializedProofRefs0.proofRefs');
  assert.deepEqual(out.Path, ['PackBytes', 'FinalTheorem', 'proofRefs', pack.FinalTheorem.proofRefs.length - 1, 'id']);
  assert.equal(out.Witness.reason, 'proofRef ids must be globally unique');
});

test('CheckMaterializedProofRefs0 rejects opaque proof material inside proof refs', async () => {
  const shell = makeMaterializedProofRefShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack.proofRefs[0] = {
    ...pack.GPack.proofRefs[0],
    proofBlob: {
      bytes: 'not allowed',
    },
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedProofRefs0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.Coord, 'CheckMaterializedProofRefs0.opaqueProof');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'proofRefs', 0, 'proofBlob']);
  assert.equal(out.Witness.reason, 'materialized proof references reject opaque proof material');
});

test('CheckMaterializedProofRefs0 rejects proof ref policy missing a kind', async () => {
  const shell = makeMaterializedProofRefShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.proofRefPolicy = {
    ...pack.Manifest.proofRefPolicy,
    allowedRefKinds: pack.Manifest.proofRefPolicy.allowedRefKinds.filter((kind) => kind !== 'SigmaInstance'),
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedProofRefs0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedProofRefs0');
  assert.equal(out.Coord, 'CheckMaterializedProofRefs0.proofRefPolicy');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'proofRefPolicy', 'allowedRefKinds', 'SigmaInstance']);
  assert.equal(out.Witness.reason, 'proofRefPolicy is missing an allowed proof ref kind');
});

async function writeTempShellFile0(t, shell) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-proof-refs-'));
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