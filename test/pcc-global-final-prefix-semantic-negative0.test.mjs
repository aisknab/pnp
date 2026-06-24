import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  CheckGlobalFinalPrefixSemantic0,
  makeGlobalFinalPrefixPCCPack0,
  makeGlobalFinalPrefixSemanticSuite0,
} from '../pcc-global-final-prefix-semantic0.mjs';

import {
  makeFinalPrefixSemanticInput0,
  withoutFinalPrefixDigest0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

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
