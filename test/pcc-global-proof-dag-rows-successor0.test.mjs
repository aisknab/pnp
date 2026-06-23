import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleSigmaSuccessor0,
} from '../pcc-kbundle-sigma-successor0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from '../pcc-kbundle-reflection-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

import {
  GLOBAL_INFRASTRUCTURE_NODE_IDS0,
  makeGlobalInfrastructureSemanticSuite0,
} from '../pcc-global-infrastructure-semantic0.mjs';

import {
  GLOBAL_ROW_SEMANTIC_NODE_IDS0,
  makeGlobalRowsSemanticSuite0,
} from '../pcc-global-rows-semantic0.mjs';

import {
  CheckGlobalProofDAGRowsFinalTheoremReadiness0,
  CheckGlobalProofDAGRowsSuccessor0,
  makeGlobalProofDAGRowsSuccessor0,
} from '../pcc-global-proof-dag-rows-successor0.mjs';

import {
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticFiniteRelJudgment0,
  makeSemanticFiniteRelClaim0,
  makeSemanticFiniteRelDomain0,
  makeSemanticFiniteRelNode0,
  makeSemanticFiniteRelProgram0,
  makeSemanticFiniteRelSpec0,
  makeSemanticFiniteRelTuple0,
} from '../pcc-kernel-finiterel-semantic0.mjs';

const finalNodeIds = [
  'Final.PackageSoundness',
  'Final.GeneratedPackageSufficiency',
  'Final.AcceptedPackageImpliesSATinP',
  'Final.AcceptedPackageImpliesPEqualsNP',
];

function makeFiniteRelProof0() {
  const domain = makeSemanticFiniteRelDomain0({
    index: 0,
    id: 'D',
    elements: ['a', 'b'],
  });
  const literal = makeSemanticFiniteRelNode0({
    index: 0,
    id: 'R',
    op: 'literal',
    domainIds: ['D', 'D'],
    tuples: [makeSemanticFiniteRelTuple0({ index: 0, values: ['a', 'b'] })],
  });
  const closure = makeSemanticFiniteRelNode0({
    index: 1,
    id: 'R.rtc',
    op: 'reflexive-transitive-closure',
    domainIds: ['D', 'D'],
    inputIds: ['R'],
  });
  const program = makeSemanticFiniteRelProgram0({
    programId: 'global.rows.successor.program',
    domains: [domain],
    nodes: [literal, closure],
    claims: [
      makeSemanticFiniteRelClaim0({
        index: 0,
        id: 'claim.R.in.rtc',
        claimKind: 'included',
        leftId: 'R',
        rightId: 'R.rtc',
      }),
      makeSemanticFiniteRelClaim0({
        index: 1,
        id: 'claim.rtc.closed',
        claimKind: 'reflexive-transitive-closed',
        leftId: 'R.rtc',
      }),
    ],
  });
  const spec = makeSemanticFiniteRelSpec0({
    evaluationId: 'global.rows.successor.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global.rows.successor',
      RuleName: 'FiniteRel',
      Conclusion: deriveSemanticFiniteRelJudgment0({ spec }),
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({
  Purpose = 'development',
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
} = {}) {
  const KBundle = makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalProofDAGRowsSuccessor0({
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations:
      makeGlobalInfrastructureSemanticSuite0({ LegacyGlobalProofDAG }),
    RowSemanticDerivations:
      makeGlobalRowsSemanticSuite0({ LegacyGlobalProofDAG }),
    Purpose,
  });
}

function withoutDigest0(node, changes) {
  const out = { ...node, ...changes };
  delete out.Digest;
  delete out.digest;
  return out;
}

test('global rows successor activates every row coordinate contract but keeps theorem/package/final gates closed', async () => {
  const out = await CheckGlobalProofDAGRowsSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGRowsSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalInfrastructureReady, true);
  assert.equal(out.NF.predecessorGlobalRowCoordinateDerivationsReady, false);
  assert.equal(out.NF.semanticKBundleFinalReady, true);
  assert.equal(out.NF.globalInfrastructureSemanticReady, true);
  assert.equal(out.NF.globalRowCoordinateDerivationsReady, true);
  assert.equal(out.NF.globalGenericRowFamilyCoordinateDerivationsReady, true);
  assert.equal(out.NF.globalLockedNANDRowCoordinateDerivationsReady, true);
  assert.equal(out.NF.globalRowCoordinateCount, GLOBAL_ROW_SEMANTIC_NODE_IDS0.length);
  assert.equal(out.NF.boundedGlobalRowCoordinateContractsOnly, true);
  assert.equal(out.NF.unrestrictedRowTheoremSoundnessNotClaimed, true);
  assert.equal(out.NF.globalRowTheoremDerivationsReady, false);

  assert.deepEqual(
    out.NF.semanticOverlay.semanticInfrastructureNodeIds,
    GLOBAL_INFRASTRUCTURE_NODE_IDS0,
  );
  assert.deepEqual(
    out.NF.semanticOverlay.semanticRowNodeIds,
    GLOBAL_ROW_SEMANTIC_NODE_IDS0,
  );
  assert.deepEqual(out.NF.semanticOverlay.blockedRowNodeIds, []);
  assert.equal(
    out.NF.semanticOverlay.semanticRowBindings.length,
    GLOBAL_ROW_SEMANTIC_NODE_IDS0.length,
  );
  assert.equal(out.NF.semanticOverlay.globalRowCoordinateDerivationsReady, true);
  assert.equal(out.NF.semanticOverlay.globalRowTheoremDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.globalPackageDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.globalFinalDerivationsReady, false);
  for (const coordinate of GLOBAL_ROW_SEMANTIC_NODE_IDS0) {
    assert.equal(out.NF.semanticOverlay.semanticNodeIds.includes(coordinate), true);
    assert.equal(out.NF.semanticOverlay.structuralOnlyNodeIds.includes(coordinate), false);
  }

  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'GlobalDAG.RowTheoremDerivations',
    'GlobalDAG.PackageDerivations',
    'GlobalDAG.FinalDerivations',
  ]);
  assert.equal(out.NF.legacyFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, finalNodeIds);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('global rows successor rejects final purpose while row theorem, package, and final derivations remain blocked', async () => {
  const out = await CheckGlobalProofDAGRowsSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowsSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic global rows successor is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 3);
  assert.equal(out.Witness.unrestrictedRowTheoremSoundnessNotClaimed, true);
});

test('explicit global rows final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGRowsFinalTheoremReadiness0(makeInput0());

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGRowsFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('global rows successor rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.globalRowCoordinateDerivationsReady = true;

  const out = await CheckGlobalProofDAGRowsSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowsSuccessor0.input');
  assert.deepEqual(out.Path, ['globalRowCoordinateDerivationsReady']);
  assert.equal(
    out.Witness.reason,
    'semantic global rows successor rejects caller-supplied readiness assertions',
  );
});

test('global rows successor rejects a final-purpose child KBundle', async () => {
  const input = makeInput0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGRowsSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowsSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('global rows successor rejects a stale Sigma-only KBundle at the predecessor boundary', async () => {
  const input = makeGlobalProofDAGRowsSuccessor0({
    KBundle: makeKBundleSigmaSuccessor0(),
  });

  const out = await CheckGlobalProofDAGRowsSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowsSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'global infrastructure predecessor rejected before row-coordinate upgrade',
  );
});

test('global rows successor rejects a generic row theorem assertion', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  const coordinate = GLOBAL_ROW_SEMANTIC_NODE_IDS0.find(
    (entry) => entry.startsWith('Row.'),
  );
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === coordinate
      ? withoutDigest0(node, { payload: { sound: true } })
      : node
  ));
  const out = await CheckGlobalProofDAGRowsSuccessor0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowsSuccessor0.semanticRows');
  assert.equal(out.Witness.reason, 'bounded global row-coordinate checker rejected');
  assert.equal(
    out.Witness.inner.witness.reason,
    'generic row-family coordinate rejects caller-supplied theorem or readiness payload fields',
  );
});

test('global rows successor rejects a stale row binding digest', async () => {
  const input = makeInput0();
  input.RowSemanticDerivations = {
    ...input.RowSemanticDerivations,
    bindings: input.RowSemanticDerivations.bindings.map((entry, index) => (
      index === 0
        ? {
            ...entry,
            nodeDigest: {
              alg: 'SHA256',
              hex: '0'.repeat(64),
            },
          }
        : entry
    )),
  };

  const out = await CheckGlobalProofDAGRowsSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowsSuccessor0.semanticRows');
  assert.equal(out.Witness.reason, 'bounded global row-coordinate checker rejected');
});

test('global rows overlay binds every row node to its checked coordinate derivation digest', async () => {
  const out = await CheckGlobalProofDAGRowsSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const derivationByCoordinate = new Map(
    out.NF.globalRowDerivationDigests.map((entry) => [
      entry.coordinate,
      entry,
    ]),
  );
  for (const binding of out.NF.semanticOverlay.semanticRowBindings) {
    const derivation = derivationByCoordinate.get(binding.coordinate);
    assert.equal(binding.derivationDigest.hex, derivation.digest.hex);
    assert.equal(binding.nodeDigest.hex, derivation.nodeDigest.hex);
    assert.equal(binding.premiseDigest.hex, derivation.premiseDigest.hex);
    assert.equal(binding.conclusionDigest.hex, derivation.conclusionDigest.hex);
    assert.equal(binding.payloadDigest.hex, derivation.payloadDigest.hex);
    assert.equal(binding.boundsDigest.hex, derivation.boundsDigest.hex);
    assert.equal(
      binding.checkerContractDigest.hex,
      derivation.checkerContractDigest.hex,
    );
  }
  const rowContractGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.GlobalDAG.RowCoordinateContracts',
  );
  assert.equal(rowContractGate.ready, true);
  const rowTheoremGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.GlobalDAG.RowTheoremDerivations',
  );
  assert.equal(rowTheoremGate.ready, false);
});
