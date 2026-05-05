
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
  assert.equal(out.NF.boot0B0Accepted, true);
  assert.match(out.NF.boot0B0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.boot0B0CoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.boot0B0FamilyCount, 12);
  assert.equal(out.NF.boot0B0RequiredFamilyCount, 12);
  assert.deepEqual(out.NF.boot0B0Families, [
    'BIface',
    'BSched',
    'BNF',
    'BTruthEval',
    'BRel',
    'BCharge',
    'BObl',
    'BArith',
    'BMode',
    'BRoute',
    'BHash',
    'BImport',
  ]);
  assert.equal(out.NF.boot0B0AllRequiredFamiliesPresent, true);
  assert.equal(out.NF.boot0B0CoversIface, true);
  assert.equal(out.NF.boot0B0CoversSched, true);
  assert.equal(out.NF.boot0B0CoversNF, true);
  assert.equal(out.NF.boot0B0CoversTruthEval, true);
  assert.equal(out.NF.boot0B0CoversRel, true);
  assert.equal(out.NF.boot0B0CoversCharge, true);
  assert.equal(out.NF.boot0B0CoversObl, true);
  assert.equal(out.NF.boot0B0CoversArith, true);
  assert.equal(out.NF.boot0B0CoversMode, true);
  assert.equal(out.NF.boot0B0CoversRoute, true);
  assert.equal(out.NF.boot0B0CoversHash, true);
  assert.equal(out.NF.boot0B0CoversImport, true);

  assert.equal(out.NF.boot0LinkedToPCCPack, true);
  assert.equal(out.NF.boot0LinkedToCoreDigestMap, true);

  assert.equal(out.NF.generatedPackageKernelSeed0, true);
  assert.equal(out.NF.kernelSeed0Accepted, true);
  assert.equal(out.NF.kernelSeed0Kind, 'KernelSeed0');
  assert.match(out.NF.kernelSeed0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.kernelSeed0RuleCount, 16);
  assert.equal(out.NF.kernelSeed0RequiredRuleCount, 16);
  assert.deepEqual(out.NF.kernelSeed0Rules, [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
    'OblTopoInd',
    'TraceInd',
    'FiniteExhaust',
    'DPInd',
    'Hall',
    'RankInd',
    'MinCounterexample',
    'IntArith',
    'Transport',
    'TruthVec',
    'FiniteRel',
  ]);
  assert.equal(out.NF.kernelSeed0AllRequiredRulesPresent, true);
  assert.equal(out.NF.kernelSeed0HasEq, true);
  assert.equal(out.NF.kernelSeed0HasSubst, true);
  assert.equal(out.NF.kernelSeed0HasRecord, true);
  assert.equal(out.NF.kernelSeed0HasDAGInd, true);
  assert.equal(out.NF.kernelSeed0HasLedgerInd, true);
  assert.equal(out.NF.kernelSeed0HasOblTopoInd, true);
  assert.equal(out.NF.kernelSeed0HasTraceInd, true);
  assert.equal(out.NF.kernelSeed0HasFiniteExhaust, true);
  assert.equal(out.NF.kernelSeed0HasDPInd, true);
  assert.equal(out.NF.kernelSeed0HasHall, true);
  assert.equal(out.NF.kernelSeed0HasRankInd, true);
  assert.equal(out.NF.kernelSeed0HasMinCounterexample, true);
  assert.equal(out.NF.kernelSeed0HasIntArith, true);
  assert.equal(out.NF.kernelSeed0HasTransport, true);
  assert.equal(out.NF.kernelSeed0HasTruthVec, true);
  assert.equal(out.NF.kernelSeed0HasFiniteRel, true);
  assert.equal(out.NF.kernelSeed0ProofNodeKindCount, 5);
  assert.deepEqual(out.NF.kernelSeed0ProofNodeKinds, [
    'PrimitiveRule',
    'SigmaInstance',
    'ReflectionInstance',
    'RowProof',
    'PackageTheorem',
  ]);
  assert.equal(out.NF.kernelSeed0AllRequiredProofNodeKindsPresent, true);
  assert.equal(out.NF.kernelSeed0ProofRefsRejectOpaque, true);
  assert.equal(out.NF.kernelSeed0ProofRefsTypedAcyclic, true);
  assert.equal(out.NF.kernelSeed0ProofRefsHashIndependent, true);
  assert.equal(out.NF.kernelSeed0PiBootDigestMatches, true);
  assert.equal(out.NF.generatedPackageCodec0, true);
  assert.equal(out.NF.codec0Accepted, true);
  assert.equal(out.NF.codec0Kind, 'Codec0');
  assert.match(out.NF.codec0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.codec0Canonical, true);
  assert.equal(out.NF.codec0NaturalEncoding, 'u32be-length-shortest-big-endian-magnitude');
  assert.equal(out.NF.codec0IntegerEncoding, 'sign-byte-plus-canonical-natural-no-negative-zero');
  assert.equal(out.NF.codec0StringEncoding, 'utf8-nfc-length-prefixed');
  assert.equal(out.NF.codec0TopLevelConsumesAllBytes, true);
  assert.equal(out.NF.codec0NormalFormSerialization, 'canonical-json-v0');
  assert.equal(out.NF.codec0PiBootDigestMatches, true);

  assert.equal(out.NF.generatedPackageDigest0, true);
  assert.equal(out.NF.digest0Accepted, true);
  assert.equal(out.NF.digest0Kind, 'Digest0');
  assert.match(out.NF.digest0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.digest0Alg, 'SHA256');
  assert.equal(out.NF.digest0Bytes, 'canonical-json-v0');
  assert.equal(out.NF.digest0EqualityNotObjectEquality, true);
  assert.equal(out.NF.digest0FullKeyComparisonAfterHashLookup, true);
  assert.equal(out.NF.digest0PiBootDigestMatches, true);
  assert.equal(out.NF.generatedPackageIfaceDict0, true);
  assert.equal(out.NF.ifaceDict0Accepted, true);
  assert.equal(out.NF.ifaceDict0Kind, 'IfaceDict0');
  assert.match(out.NF.ifaceDict0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.ifaceDict0ForbiddenSymbolCount >= 11, true);
  assert.equal(out.NF.ifaceDict0RequiredForbiddenSymbolsPresent, true);
  assert.equal(out.NF.ifaceDict0NoExecutableMinSymbols, true);
  assert.equal(out.NF.ifaceDict0PublicConstructorsPresent, true);
  assert.equal(out.NF.ifaceDict0CriticalKindsPresent, true);
  assert.equal(out.NF.ifaceDict0RouteTokensPresent, true);
  assert.equal(out.NF.ifaceDict0PiBootDigestMatches, true);

  assert.equal(out.NF.generatedPackageSched0, true);
  assert.equal(out.NF.sched0Accepted, true);
  assert.equal(out.NF.sched0Kind, 'Sched0');
  assert.match(out.NF.sched0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.sched0CoreMatchesExpected, true);
  assert.equal(out.NF.sched0CoreB0, 64);
  assert.equal(out.NF.sched0CoreK0, 512);
  assert.equal(out.NF.sched0CoreR0, 64);
  assert.equal(out.NF.sched0CoreH0, 128);
  assert.equal(out.NF.sched0CoreO0, 64);
  assert.equal(out.NF.sched0CoreRel0, 16);
  assert.equal(out.NF.sched0ScaleFactorsPresent, true);
  assert.equal(out.NF.sched0SelectorBoundsPresent, true);
  assert.equal(out.NF.sched0SelectorBoundBH, 8);
  assert.equal(out.NF.sched0SelectorBoundBTheta, 12);
  assert.equal(out.NF.sched0PolynomialExponent, 36);
  assert.equal(out.NF.sched0PiBootDigestMatches, true);
  assert.equal(out.NF.generatedPackageByteLang0, true);
  assert.equal(out.NF.byteLang0Accepted, true);
  assert.equal(out.NF.byteLang0Kind, 'ByteLang0');
  assert.match(out.NF.byteLang0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.byteLang0TagCount >= 12, true);
  assert.equal(out.NF.byteLang0TagsUnique, true);
  assert.equal(out.NF.byteLang0RequiredTagsPresent, true);
  assert.equal(out.NF.byteLang0SortCount >= 8, true);
  assert.equal(out.NF.byteLang0RequiredSortsPresent, true);
  assert.equal(out.NF.byteLang0ConstructorCount >= 7, true);
  assert.equal(out.NF.byteLang0RequiredConstructorsPresent, true);
  assert.equal(out.NF.byteLang0RecordCount >= 9, true);
  assert.equal(out.NF.byteLang0RequiredRecordAritiesPresent, true);
  assert.equal(out.NF.byteLang0PiBootDigestMatches, true);

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
  assert.equal(config.checkKernelSeed0, true);
  assert.equal(config.checkCodecDigest0, true);
  assert.equal(config.checkIfaceSched0, true);
  assert.equal(config.checkByteLang0, true);
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

test('CheckGeneratedPCCPackexp0 rejects generated package missing a B0 row family', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      MaterializedBoot0: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0,
        B0: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.B0,
          rows: envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.B0.rows.filter((row) => (
            row.PackageID !== 'BTruthEval'
          )),
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
  assert.deepEqual(out.Path, ['GeneratedPCCPack', 'Boot0', 'B0']);
});

test('CheckGeneratedPCCPackexp0 rejects generated package missing a KernelSeed0 primitive rule', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      MaterializedBoot0: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0,
        KernelSeed0: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.KernelSeed0,
          rules: envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.KernelSeed0.rules.filter((rule) => (
            rule !== 'Hall'
          )),
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
    checkMaterializedBoot0: false,
    checkCheckPCCPackexpRecord: false,
    checkPublicClaimBoundary: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.KernelSeed0');
  assert.deepEqual(out.Path, ['GeneratedPCCPack', 'Boot0', 'KernelSeed0', 'rules']);
});

test('CheckGeneratedPCCPackexp0 rejects KernelSeed0 opaque proof references', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      MaterializedBoot0: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0,
        KernelSeed0: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.KernelSeed0,
          proofReferencePolicy: {
            ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.KernelSeed0.proofReferencePolicy,
            rejectsOpaqueProofBlobs: false,
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
    checkMaterializedBoot0: false,
    checkCheckPCCPackexpRecord: false,
    checkPublicClaimBoundary: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.KernelSeed0');
  assert.deepEqual(out.Path, [
    'GeneratedPCCPack',
    'Boot0',
    'KernelSeed0',
    'proofReferencePolicy',
    'rejectsOpaqueProofBlobs',
  ]);
});

test('CheckGeneratedPCCPackexp0 rejects noncanonical Codec0 natural encoding', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      MaterializedBoot0: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0,
        Codec0: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.Codec0,
          naturalEncoding: 'noncanonical-natural-encoding',
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
    checkMaterializedBoot0: false,
    checkKernelSeed0: false,
    checkCheckPCCPackexpRecord: false,
    checkPublicClaimBoundary: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.CodecDigest0');
  assert.deepEqual(out.Path, ['GeneratedPCCPack', 'Boot0', 'Codec0', 'naturalEncoding']);
});

test('CheckGeneratedPCCPackexp0 rejects Digest0 object-equality misuse', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      MaterializedBoot0: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0,
        Digest0: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.Digest0,
          digestEqualityIsNotObjectEquality: false,
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
    checkMaterializedBoot0: false,
    checkKernelSeed0: false,
    checkCheckPCCPackexpRecord: false,
    checkPublicClaimBoundary: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.CodecDigest0');
  assert.deepEqual(out.Path, [
    'GeneratedPCCPack',
    'Boot0',
    'Digest0',
    'digestEqualityIsNotObjectEquality',
  ]);
});

test('CheckGeneratedPCCPackexp0 rejects IfaceDict0 missing hidden-minimization forbidden symbols', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      MaterializedBoot0: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0,
        IfaceDict0: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.IfaceDict0,
          forbiddenSymbols: envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.IfaceDict0.forbiddenSymbols.filter((symbol) => (
            symbol !== 'minimumEquivalent'
          )),
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
    checkMaterializedBoot0: false,
    checkKernelSeed0: false,
    checkCodecDigest0: false,
    checkCheckPCCPackexpRecord: false,
    checkPublicClaimBoundary: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.IfaceSched0');
  assert.deepEqual(out.Path, ['GeneratedPCCPack', 'Boot0', 'IfaceDict0', 'forbiddenSymbols']);
});

test('CheckGeneratedPCCPackexp0 rejects Sched0 core drift', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      MaterializedBoot0: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0,
        Sched0: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.Sched0,
          core: {
            ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.Sched0.core,
            B0: 63,
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
    checkMaterializedBoot0: false,
    checkKernelSeed0: false,
    checkCodecDigest0: false,
    checkCheckPCCPackexpRecord: false,
    checkPublicClaimBoundary: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.IfaceSched0');
  assert.deepEqual(out.Path, ['GeneratedPCCPack', 'Boot0', 'Sched0', 'core', 'B0']);
});

test('CheckGeneratedPCCPackexp0 rejects duplicate ByteLang0 tag values', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      MaterializedBoot0: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0,
        ByteLang0: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.ByteLang0,
          tags: {
            ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.ByteLang0.tags,
            Row0: envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.ByteLang0.tags.Boot0,
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
    checkMaterializedBoot0: false,
    checkKernelSeed0: false,
    checkCodecDigest0: false,
    checkIfaceSched0: false,
    checkCheckPCCPackexpRecord: false,
    checkPublicClaimBoundary: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.ByteLang0');
  assert.deepEqual(out.Path, ['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'tags']);
});

test('CheckGeneratedPCCPackexp0 rejects stale ByteLang0 record arity', async () => {
  const envelope = await makeGeneratedPCCPackexp0();

  envelope.GeneratedPCCPack = {
    ...envelope.GeneratedPCCPack,
    MaterializedPCCPackEnvelope: {
      ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope,
      MaterializedBoot0: {
        ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0,
        ByteLang0: {
          ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.ByteLang0,
          records: {
            ...envelope.GeneratedPCCPack.MaterializedPCCPackEnvelope.MaterializedBoot0.ByteLang0.records,
            Boot0: 8,
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
    checkMaterializedBoot0: false,
    checkKernelSeed0: false,
    checkCodecDigest0: false,
    checkIfaceSched0: false,
    checkCheckPCCPackexpRecord: false,
    checkPublicClaimBoundary: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckGeneratedPCCPackexp0');
  assert.equal(out.Coord, 'CheckGeneratedPCCPackexp0.ByteLang0');
  assert.deepEqual(out.Path, ['GeneratedPCCPack', 'Boot0', 'ByteLang0', 'records', 'Boot0']);
});
