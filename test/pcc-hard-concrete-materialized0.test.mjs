import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedHard0,
  makeConcreteHardCoverage0,
  makeConcreteMaterializedHard0,
  writeConcreteMaterializedHardFiles0,
} from '../pcc-hard-concrete-materialized0.mjs';

import {
  CheckMaterializedHard0,
} from '../pcc-hard-materialized0.mjs';

import {
  HARD_CHECKER_FIELDS0,
} from '../pcc-hard0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function refreshEnvelope0(envelope) {
  envelope.HardCheck = envelope.MaterializedHardEnvelope.HardCheck;
  envelope.Coverage = makeConcreteHardCoverage0(envelope.MaterializedHardEnvelope);

  envelope.Linkage = {
    ...envelope.Linkage,
    materializedHardDigest: digestCanonical0(envelope.MaterializedHardEnvelope),
    hardCheckDigest: digestCanonical0(envelope.HardCheck),
    coverageDigest: digestCanonical0(envelope.Coverage),
    checkerCount: envelope.Coverage.checkerCount,
    rowKeyFieldCount: envelope.Coverage.rowKeyFieldCount,
    forbiddenSymbolCount: envelope.Coverage.forbiddenSymbolCount,
    forbiddenImportEdgeCount: envelope.Coverage.forbiddenImportEdgeCount,
  };

  return envelope;
}

test('CheckConcreteMaterializedHard0 accepts concrete hard-checker coverage', async () => {
  const envelope = makeConcreteMaterializedHard0();
  const out = await CheckConcreteMaterializedHard0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedHard0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedHardCheck0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.checkerCoverageComplete, true);
  assert.equal(out.NF.rowKeyCoverageComplete, true);
  assert.equal(out.NF.routePriorityComplete, true);
  assert.equal(out.NF.proofRefPolicyComplete, true);
  assert.equal(out.NF.hashDisciplineComplete, true);
  assert.equal(out.NF.noMinCoverageComplete, true);
  assert.equal(out.NF.importPolicyComplete, true);
  assert.equal(out.NF.reflectionPolicyComplete, true);
  assert.equal(out.NF.boundsPolicyComplete, true);
  assert.equal(out.NF.diagnosticsPolicyComplete, true);
  assert.equal(out.NF.checkerCount, HARD_CHECKER_FIELDS0.length);

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner materialized HardCheck checker accepts the concrete hard core', async () => {
  const envelope = makeConcreteMaterializedHard0();
  const out = await CheckMaterializedHard0(envelope.MaterializedHardEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedHard0');
  assert.equal(out.NF.kind, 'MaterializedHardCheck0NF');
});

test('CheckConcreteMaterializedHard0 rejects stale coverage', async () => {
  const envelope = makeConcreteMaterializedHard0();

  envelope.MaterializedHardEnvelope = {
    ...envelope.MaterializedHardEnvelope,
    HardCheck: {
      ...envelope.MaterializedHardEnvelope.HardCheck,
      RowKeyCheck: {
        ...envelope.MaterializedHardEnvelope.HardCheck.RowKeyCheck,
        rowKeyFields: envelope.MaterializedHardEnvelope.HardCheck.RowKeyCheck.rowKeyFields.slice(1),
      },
    },
  };

  envelope.HardCheck = envelope.MaterializedHardEnvelope.HardCheck;
  envelope.Linkage = {
    ...envelope.Linkage,
    materializedHardDigest: undefined,
    hardCheckDigest: undefined,
  };

  const out = await CheckConcreteMaterializedHard0(envelope, {
    checkMaterializedHard: false,
    checkHard: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedHard0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedHard0.coverage');
  assert.deepEqual(out.Path, ['Coverage']);
});

test('CheckConcreteMaterializedHard0 rejects incomplete no-hidden-minimization coverage', async () => {
  const envelope = makeConcreteMaterializedHard0();

  envelope.MaterializedHardEnvelope = {
    ...envelope.MaterializedHardEnvelope,
    HardCheck: {
      ...envelope.MaterializedHardEnvelope.HardCheck,
      NoMinCheck: {
        ...envelope.MaterializedHardEnvelope.HardCheck.NoMinCheck,
        forbiddenSymbols: envelope.MaterializedHardEnvelope.HardCheck.NoMinCheck.forbiddenSymbols.filter((symbol) => symbol !== 'minimumEquivalent'),
      },
    },
  };

  refreshEnvelope0(envelope);

  const out = await CheckConcreteMaterializedHard0(envelope, {
    checkMaterializedHard: false,
    checkHard: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedHard0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedHard0.coverage');
  assert.deepEqual(out.Path, ['Coverage', 'noMinCoverageComplete']);
});

test('CheckConcreteMaterializedHard0 rejects incomplete import policy coverage', async () => {
  const envelope = makeConcreteMaterializedHard0();

  envelope.MaterializedHardEnvelope = {
    ...envelope.MaterializedHardEnvelope,
    HardCheck: {
      ...envelope.MaterializedHardEnvelope.HardCheck,
      ImportCheck: {
        ...envelope.MaterializedHardEnvelope.HardCheck.ImportCheck,
        forbiddenEdges: envelope.MaterializedHardEnvelope.HardCheck.ImportCheck.forbiddenEdges.slice(1),
      },
    },
  };

  refreshEnvelope0(envelope);

  const out = await CheckConcreteMaterializedHard0(envelope, {
    checkMaterializedHard: false,
    checkHard: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedHard0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedHard0.coverage');
  assert.deepEqual(out.Path, ['Coverage', 'importPolicyComplete']);
});

test('CheckConcreteMaterializedHard0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = makeConcreteMaterializedHard0({
    overrides: {
      GateNote: 'synthetic marker must reject in strict marker mode',
    },
  });

  const out = await CheckConcreteMaterializedHard0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedHard0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedHard0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteMaterializedHardFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-hard-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedHardFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.materializedHardPath,
    result.files.hardCheckPath,
    result.files.coveragePath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});
