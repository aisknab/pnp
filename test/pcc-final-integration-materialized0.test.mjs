import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedFinalIntegration0,
  makeMaterializedFinalIntegrationEnvelope0,
  writeMaterializedFinalIntegrationFiles0,
} from '../pcc-final-integration-materialized0.mjs';

import {
  CheckGPack0,
  CheckRowFamG0,
} from '../pcc-gpack0.mjs';

import {
  CheckFinalFrameworkMatch0,
  CheckFinalIntegration0,
  CheckSATBounds0,
  CheckSATDecision0,
  FINAL_INTEGRATION_PHASES0,
} from '../pcc-final-framework0.mjs';

import {
  CheckFinal0,
  CheckRowFamFinal0,
} from '../pcc-final0.mjs';

test('CheckMaterializedFinalIntegration0 accepts a materialized locked NAND and final integration envelope', async () => {
  const envelope = makeMaterializedFinalIntegrationEnvelope0();
  const out = await CheckMaterializedFinalIntegration0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalIntegration0');
  assert.equal(out.NF.kind, 'MaterializedFinalIntegration0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.deepEqual(out.NF.phases, FINAL_INTEGRATION_PHASES0);
  assert.equal(out.NF.residualSlackBound, 4);
  assert.equal(out.NF.exportedStatement.consequent, 'P = NP');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner locked NAND and final checkers accept the materialized cores', async () => {
  const envelope = makeMaterializedFinalIntegrationEnvelope0();

  const gpack = await CheckGPack0(envelope.GPack);
  const rowFamG = await CheckRowFamG0(envelope.RowFamG);
  const finalMatch = await CheckFinalFrameworkMatch0(envelope.FinalIntegration.FinalMatch);
  const satDecision = await CheckSATDecision0(envelope.FinalIntegration.SATDecision);
  const satBounds = await CheckSATBounds0(envelope.FinalIntegration.SATBounds);
  const finalIntegration = await CheckFinalIntegration0(envelope.FinalIntegration);
  const finalTheorem = await CheckFinal0(envelope.FinalTheorem);
  const rowFamFinal = await CheckRowFamFinal0(envelope.RowFamFinal);

  assert.equal(gpack.tag, 'accept');
  assert.equal(rowFamG.tag, 'accept');
  assert.equal(finalMatch.tag, 'accept');
  assert.equal(satDecision.tag, 'accept');
  assert.equal(satBounds.tag, 'accept');
  assert.equal(finalIntegration.tag, 'accept');
  assert.equal(finalTheorem.tag, 'accept');
  assert.equal(rowFamFinal.tag, 'accept');
});

test('CheckMaterializedFinalIntegration0 exposes locked NAND checker failures', async () => {
  const envelope = makeMaterializedFinalIntegrationEnvelope0();

  envelope.GPack = {
    ...envelope.GPack,
    ThresholdCert: {
      ...envelope.GPack.ThresholdCert,
      residualSlackMax: 5,
    },
  };

  const out = await CheckMaterializedFinalIntegration0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalIntegration0');
  assert.equal(out.Coord, 'CheckMaterializedFinalIntegration0.GPack');
  assert.equal(out.Witness.detail.inner.coord, 'CheckGPack0.threshold');
});

test('CheckMaterializedFinalIntegration0 rejects RowFamG linkage mismatch', async () => {
  const envelope = makeMaterializedFinalIntegrationEnvelope0();

  envelope.RowFamG = {
    ...envelope.RowFamG,
    GPack: {
      ...envelope.RowFamG.GPack,
      IfaceHash: {
        ...envelope.RowFamG.GPack.IfaceHash,
        hex: '0000000000000000000000000000000000000000000000000000000000000000',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    rowFamGDigest: undefined,
  };

  const out = await CheckMaterializedFinalIntegration0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalIntegration0');
  assert.equal(out.Coord, 'CheckMaterializedFinalIntegration0.linkage');
  assert.deepEqual(out.Path, ['RowFamG', 'GPack']);
});

test('CheckMaterializedFinalIntegration0 rejects forbidden fixture marker text', async () => {
  const envelope = makeMaterializedFinalIntegrationEnvelope0();

  envelope.FinalTheorem = {
    ...envelope.FinalTheorem,
    PiFinal: {
      ...envelope.FinalTheorem.PiFinal,
      note: 'synthetic marker must reject',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    finalTheoremDigest: undefined,
  };

  const out = await CheckMaterializedFinalIntegration0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalIntegration0');
  assert.equal(out.Coord, 'CheckMaterializedFinalIntegration0.fixtureMarkers');
});

test('CheckMaterializedFinalIntegration0 rejects stale linkage digest', async () => {
  const envelope = makeMaterializedFinalIntegrationEnvelope0();

  envelope.Linkage = {
    ...envelope.Linkage,
    finalIntegrationDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckMaterializedFinalIntegration0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalIntegration0');
  assert.equal(out.Coord, 'CheckMaterializedFinalIntegration0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'finalIntegrationDigest']);
});

test('writeMaterializedFinalIntegrationFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-final-integration-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeMaterializedFinalIntegrationFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.gpackPath,
    result.files.rowFamGPath,
    result.files.finalIntegrationPath,
    result.files.finalMatchPath,
    result.files.satDecisionPath,
    result.files.satBoundsPath,
    result.files.finalTheoremPath,
    result.files.rowFamFinalPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});
