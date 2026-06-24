import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalFinalPrefixSemantic0,
  GLOBAL_FINAL_PREFIX_NODE_IDS0,
  GLOBAL_FINAL_REMAINING_NODE_IDS0,
  makeGlobalFinalPrefixPCCPack0,
  makeGlobalFinalPrefixSemanticSuite0,
} from '../pcc-global-final-prefix-semantic0.mjs';

import {
  makeFinalPrefixSemanticInput0,
  withoutFinalPrefixDigest0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

test('final-prefix checker refines two prefix nodes without activating public conclusions', async () => {
  const out = await CheckGlobalFinalPrefixSemantic0(
    makeFinalPrefixSemanticInput0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalFinalPrefixSemantic0');
  assert.equal(out.NF.globalFinalPrefixSemanticReady, true);
  assert.equal(out.NF.globalFinalPrefixRefinementsReady, true);
  assert.equal(out.NF.globalPackageSoundnessNodeRefinementReady, true);
  assert.equal(out.NF.globalGeneratedPackageSufficiencyNodeRefinementReady, true);
  assert.deepEqual(out.NF.globalFinalPrefixNodeIds, GLOBAL_FINAL_PREFIX_NODE_IDS0);
  assert.deepEqual(out.NF.globalFinalRemainingNodeIds, GLOBAL_FINAL_REMAINING_NODE_IDS0);
  assert.equal(out.NF.globalFinalPrefixRefinementCount, 2);
  assert.equal(out.NF.packSufficiencyAccepted, true);
  assert.equal(out.NF.globalPackageDerivationsReady, true);
  assert.equal(out.NF.boundedExecutableFinalPrefixRefinementsOnly, true);
  assert.equal(out.NF.unrestrictedFinalPrefixTheoremSoundnessNotClaimed, true);
  assert.equal(out.NF.packAcceptanceDoesNotActivatePublicConclusion, true);
  assert.equal(out.NF.globalFinalSATReductionDerivationReady, false);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);

  const packageSoundness = out.NF.finalPrefixRefinements[0];
  assert.equal(packageSoundness.nodeId, 'Final.PackageSoundness');
  assert.equal(
    packageSoundness.negativeCoord,
    'CheckPackSufficiency0.PackSufficiencyTheorem',
  );
  assert.deepEqual(packageSoundness.negativePath, [
    'PackSufficiencyTheorem',
    'packageSufficiency',
    'acceptedPackageValid',
  ]);

  const generated = out.NF.finalPrefixRefinements[1];
  assert.equal(generated.nodeId, 'Final.GeneratedPackageSufficiency');
  assert.deepEqual(generated.negativePath, [
    'PackSufficiencyTheorem',
    'generatedPackageSufficiency',
    'canonicalByteEquality',
  ]);
});

test('final-prefix refinement digests bind every node and pack boundary', async () => {
  const out = await CheckGlobalFinalPrefixSemantic0(
    makeFinalPrefixSemanticInput0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.finalPrefixRefinementDigests.length, 2);
  for (const entry of out.NF.finalPrefixRefinementDigests) {
    assert.equal(entry.digest.alg, 'SHA256');
    assert.equal(entry.globalNodeDigest.alg, 'SHA256');
    assert.equal(entry.dependencyNodeDigest.alg, 'SHA256');
    assert.equal(entry.sourceRecordDigest.alg, 'SHA256');
    assert.equal(entry.positiveRecordDigest.alg, 'SHA256');
    assert.equal(entry.negativeRecordDigest.alg, 'SHA256');
    assert.equal(entry.checkerContractDigest.alg, 'SHA256');
    assert.equal(entry.conclusionDigest.alg, 'SHA256');
  }
});

test('final-prefix checker rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeFinalPrefixSemanticInput0(),
    globalFinalPrefixRefinementsReady: true,
  };
  const out = await CheckGlobalFinalPrefixSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalPrefixSemantic0.input');
  assert.deepEqual(out.Path, ['globalFinalPrefixRefinementsReady']);
  assert.equal(
    out.Witness.reason,
    'global final-prefix semantic checker rejects caller-supplied readiness or truth assertions',
  );
});

test('final-prefix checker rejects a stale semantic binding digest', async () => {
  const base = makeFinalPrefixSemanticInput0();
  const input = {
    ...base,
    SemanticFinalPrefix: {
      ...base.SemanticFinalPrefix,
      refinements: base.SemanticFinalPrefix.refinements.map((entry) => (
        entry.nodeId === 'Final.PackageSoundness'
          ? {
              ...entry,
              sourceRecordDigest: {
                alg: 'SHA256',
                hex: '0'.repeat(64),
              },
            }
          : entry
      )),
    },
  };
  const out = await CheckGlobalFinalPrefixSemantic0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalPrefixSemantic0.semanticFinalPrefixSuite');
  assert.equal(
    out.Witness.reason,
    'global final-prefix semantic suite must exactly match the computed final-node, dependency, pack, and checker bindings',
  );
});

test('final-prefix checker rejects a caller truth payload on Final.PackageSoundness', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === 'Final.PackageSoundness'
      ? withoutFinalPrefixDigest0(node, { payload: { sound: true } })
      : node
  ));
  const out = await CheckGlobalFinalPrefixSemantic0(
    makeFinalPrefixSemanticInput0({ LegacyGlobalProofDAG: dag }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalFinalPrefixSemantic0.finalPrefix.Final.PackageSoundness',
  );
  assert.equal(
    out.Witness.reason,
    'final-prefix global node must retain empty imports/payload, Full mode, and null route/rank',
  );
});

test('final-prefix checker propagates a false package-validity source field', async () => {
  const input = makeFinalPrefixSemanticInput0();
  const pack = {
    ...input.PCCPack,
    PackSufficiencyTheorem: {
      ...input.PCCPack.PackSufficiencyTheorem,
      packageSufficiency: {
        ...input.PCCPack.PackSufficiencyTheorem.packageSufficiency,
        acceptedPackageValid: false,
      },
    },
  };
  const out = await CheckGlobalFinalPrefixSemantic0({
    ...input,
    PCCPack: pack,
    SemanticFinalPrefix: makeGlobalFinalPrefixSemanticSuite0({
      LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
      PCCPack: pack,
    }),
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalPrefixSemantic0.packSufficiency');
  assert.equal(
    out.Witness.reason,
    'final-prefix refinements require an accepted version-zero pack-sufficiency record',
  );
});

test('final-prefix checker propagates a false canonical-byte source field', async () => {
  const input = makeFinalPrefixSemanticInput0();
  const pack = {
    ...input.PCCPack,
    PackSufficiencyTheorem: {
      ...input.PCCPack.PackSufficiencyTheorem,
      generatedPackageSufficiency: {
        ...input.PCCPack.PackSufficiencyTheorem.generatedPackageSufficiency,
        canonicalByteEquality: false,
      },
    },
  };
  const out = await CheckGlobalFinalPrefixSemantic0({
    ...input,
    PCCPack: pack,
    SemanticFinalPrefix: makeGlobalFinalPrefixSemanticSuite0({
      LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
      PCCPack: pack,
    }),
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalPrefixSemantic0.packSufficiency');
});

test('final-prefix checker rejects a pack aligned to a different accepted global DAG', async () => {
  const input = makeFinalPrefixSemanticInput0();
  const differentDAG = makeSyntheticGlobalProofDAG0();
  differentDAG.PiGlobalDAG = {
    ...differentDAG.PiGlobalDAG,
    note: 'different accepted global DAG witness',
  };
  const pack = makeGlobalFinalPrefixPCCPack0({
    LegacyGlobalProofDAG: differentDAG,
    RowPack: input.RowPack,
    RowFamG: input.RowFamG,
    LocalPackages: input.LocalPackages,
  });
  const out = await CheckGlobalFinalPrefixSemantic0({
    ...input,
    PCCPack: pack,
    SemanticFinalPrefix: makeGlobalFinalPrefixSemanticSuite0({
      LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
      PCCPack: pack,
    }),
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalFinalPrefixSemantic0.packSurfaceAlignment');
  assert.deepEqual(out.Path, ['PCCPack', 'GlobalProofDAG']);
});
