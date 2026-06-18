import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedGlobalProofDAG0,
  makeMaterializedGlobalProofDAG0,
  writeMaterializedGlobalProofDAGFiles0,
} from '../pcc-global-proof-dag-materialized0.mjs';

import {
  CheckGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

test('CheckMaterializedGlobalProofDAG0 accepts a JSON-materialized global proof DAG', async () => {
  const envelope = await makeMaterializedGlobalProofDAG0();
  const out = await CheckMaterializedGlobalProofDAG0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedGlobalProofDAG0');
  assert.equal(out.NF.kind, 'MaterializedGlobalProofDAG0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.nodeCount, envelope.GlobalProofDAG.Nodes.length);
  assert.ok(out.NF.nodeCount > 0);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner GlobalProofDAG0 checker accepts the materialized DAG core', async () => {
  const envelope = await makeMaterializedGlobalProofDAG0();
  const out = await CheckGlobalProofDAG0(envelope.GlobalProofDAG);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.NF.kind, 'GlobalProofDAG0NF');
  assert.equal(out.NF.nodeCount, envelope.GlobalProofDAG.Nodes.length);
});

test('CheckMaterializedGlobalProofDAG0 rejects an IfaceHash linkage mismatch', async () => {
  const envelope = await makeMaterializedGlobalProofDAG0();

  envelope.GlobalProofDAG = {
    ...envelope.GlobalProofDAG,
    IfaceHash: {
      ...envelope.GlobalProofDAG.IfaceHash,
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    globalProofDAGDigest: undefined,
  };

  const out = await CheckMaterializedGlobalProofDAG0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckMaterializedGlobalProofDAG0.linkage');
  assert.deepEqual(out.Path, ['GlobalProofDAG', 'IfaceHash']);
});

test('CheckMaterializedGlobalProofDAG0 rejects fixture marker text in the DAG core', async () => {
  const envelope = await makeMaterializedGlobalProofDAG0();

  envelope.GlobalProofDAG = {
    ...envelope.GlobalProofDAG,
    PiGlobalDAG: {
      ...envelope.GlobalProofDAG.PiGlobalDAG,
      note: 'synthetic marker must reject',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    globalProofDAGDigest: undefined,
  };

  const out = await CheckMaterializedGlobalProofDAG0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckMaterializedGlobalProofDAG0.fixtureMarkers');
});

test('writeMaterializedGlobalProofDAGFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-global-dag-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeMaterializedGlobalProofDAGFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.dagPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});
