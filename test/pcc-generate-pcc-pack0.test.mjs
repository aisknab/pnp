
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckGeneratedPCCPackexp0,
  GeneratePCCPack0,
  makeGeneratedPCCPackexp0,
  makeGeneratePCCPackConfig0,
  writeGeneratedPCCPackexpFiles0,
} from '../pcc-generate-pcc-pack0.mjs';

test('GeneratePCCPack0 emits deterministic concrete materialized package bytes', async () => {
  const first = await GeneratePCCPack0();
  const second = await GeneratePCCPack0();

  assert.equal(JSON.stringify(first), JSON.stringify(second));
  assert.equal(first.kind, 'ConcreteMaterializedPCCPack0');
  assert.equal(first.MaterializedPCCPackEnvelope.kind, 'MaterializedPCCPack0');
  assert.equal(first.PCCPack.kind, 'PCCPack0');
});

test('CheckGeneratedPCCPackexp0 accepts generated package with accepted CheckPCCPackexp0 record', async () => {
  const envelope = await makeGeneratedPCCPackexp0();
  const out = await CheckGeneratedPCCPackexp0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.NF.kind, 'GeneratedPCCPackexp0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.generator, 'GeneratePCCPack0');
  assert.equal(out.NF.deterministicGenerator, true);
  assert.equal(out.NF.generatedPackageMatchesGenerator, true);
  assert.equal(out.NF.generatedPackageCoreOnly, true);
  assert.equal(out.NF.generatorCoreExcludesAcceptRun, true);

  assert.equal(out.NF.generatedPackageBoot0, true);
  assert.equal(out.NF.boot0Accepted, true);
  assert.equal(out.NF.boot0Kind, 'Boot0');
  assert.match(out.NF.boot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.boot0CheckDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.boot0CanonicalByteDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.boot0RowCount > 0, true);
  assert.equal(out.NF.boot0KernelRuleCount > 0, true);
  assert.equal(out.NF.boot0JsonMaterialized, true);
  assert.equal(out.NF.boot0NoFixtureMarkers, true);
  assert.match(out.NF.boot0BootBatchDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.boot0BootAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.boot0LinkedToPCCPack, true);
  assert.equal(out.NF.boot0LinkedToCoreDigestMap, true);

  assert.equal(out.NF.checkPCCPackexp, true);
  assert.equal(out.NF.checkPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.checkPCCPackexpRecordChecker, 'CheckPCCPackexp0');
  assert.equal(out.NF.checkPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.checkPCCPackexpRecordMatchesFresh, true);

  assert.equal(out.NF.publicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.equal(out.NF.publicConclusion.conditional, true);

  assert.equal(out.NF.concretePCCPack, true);
  assert.equal(out.NF.concreteKBundle, true);
  assert.equal(out.NF.concreteHardCheck, true);
  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteGlobalProofDAG, true);
  assert.equal(out.NF.concreteFinalIntegration, true);

  assert.match(out.NF.generatedPackageDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.checkPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('makeGeneratePCCPackConfig0 fills default validation switches', () => {
  const config = makeGeneratePCCPackConfig0({
    checkJsonMaterialized: false,
  });

  assert.equal(config.kind, 'GeneratePCCPackConfig0');
  assert.equal(config.checkDeterministicGenerator, true);
  assert.equal(config.checkGeneratedPackageCoreBoundary, true);
  assert.equal(config.checkMaterializedBoot0, true);
  assert.equal(config.checkJsonMaterialized, false);
  assert.equal(typeof config.checkPCCPackexpConfig, 'object');
});

test('CheckGeneratedPCCPackexp0 rejects generated package core with embedded AcceptRun', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    AcceptRun: {
      kind: 'ForbiddenEmbeddedAcceptRun0',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedPackageDigest: undefined,
  };

  const out = await CheckGeneratedPCCPackexp0(envelope, {
    checkDeterministicGenerator: false,
    checkCheckPCCPackexpRecord: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.coreBoundary');
  assert.deepEqual(out.Path, ['GeneratedPCCPack', 'AcceptRun']);
});

test('CheckGeneratedPCCPackexp0 rejects stale materialized CheckPCCPackexp0 record', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.CheckPCCPackexpRecord = {
    ...envelope.CheckPCCPackexpRecord,
    NF: {
      ...envelope.CheckPCCPackexpRecord.NF,
      concreteHardCheck: false,
    },
    nf: {
      ...envelope.CheckPCCPackexpRecord.nf,
      concreteHardCheck: false,
    },
  };

  const out = await CheckGeneratedPCCPackexp0(envelope, {
    checkDeterministicGenerator: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.CheckPCCPackexpRecord');
  assert.deepEqual(out.Path, ['CheckPCCPackexpRecord', 'Digest']);
});

test('writeGeneratedPCCPackexpFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-generated-pcc-pack-exp-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeGeneratedPCCPackexpFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.generatedPackagePath,
    result.files.checkPCCPackexpRecordPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('CheckGeneratedPCCPackexp0 rejects generated package whose Boot0 core digest is stale', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      PCCPack: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.PCCPack,
        Core: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.PCCPack.Core,
          artefactDigests: {
            ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.PCCPack.Core.artefactDigests,
            Boot0: {
              alg: 'SHA256',
              bytes: 'canonical-json-v0',
              hex: '0000000000000000000000000000000000000000000000000000000000000000',
            },
          },
        },
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedPackageDigest: undefined,
  };

  const out = await CheckGeneratedPCCPackexp0(envelope, {
    checkDeterministicGenerator: false,
    checkCheckPCCPackexpRecord: false,
    checkPublicClaimBoundary: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.Boot0');
  assert.deepEqual(out.Path, ['GeneratedPCCPack', 'PCCPack', 'Core', 'artefactDigests', 'Boot0']);
});
