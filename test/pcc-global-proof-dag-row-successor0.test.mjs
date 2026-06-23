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
  makeGlobalInfrastructureSemanticSuite0,
} from '../pcc-global-infrastructure-semantic0.mjs';

import {
  makeSyntheticRowPack0,
} from '../pcc-rows0.mjs';

import {
  makeSyntheticRowFamG0,
} from '../pcc-gpack0.mjs';

import {
  makeGlobalRowSemanticSuite0,
} from '../pcc-global-row-semantic0.mjs';

import {
  CheckGlobalProofDAGRowFinalTheoremReadiness0,
  CheckGlobalProofDAGRowSuccessor0,
  makeGlobalProofDAGRowSuccessor0,
} from '../pcc-global-proof-dag-row-successor0.mjs';

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
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
} = {}) {
  const KBundle = makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalProofDAGRowSuccessor0({
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations:
      makeGlobalInfrastructureSemanticSuite0({ LegacyGlobalProofDAG }),
    RowPack,
    RowFamG,
    RowSemanticDerivations: makeGlobalRowSemanticSuite0({
      LegacyGlobalProofDAG,
      RowPack,
      RowFamG,
    }),
    Purpose,
  });
}

function withoutDigest0(node, changes) {
  const out = { ...node, ...changes };
  delete out.Digest;
  delete out.digest;
  return out;
}

test('global row successor activates every required row node and keeps package/final nodes quarantined', async () => {
  const out = await CheckGlobalProofDAGRowSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGRowSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalInfrastructureReady, true);
  assert.equal(out.NF.predecessorGlobalRowReady, false);
  assert.equal(out.NF.semanticKBundleDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKBundleFinalProbeAccepted, true);
  assert.equal(out.NF.kBundleFinalReady, true);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.equal(out.NF.semanticReflectionReady, true);
  assert.equal(out.NF.globalInfrastructureSemanticReady, true);
  assert.equal(out.NF.globalRowSemanticReady, true);
  assert.equal(out.NF.globalRowDerivationsReady, true);
  assert.equal(out.NF.globalRowFamilyCount, 39);
  assert.equal(out.NF.globalLockedNANDProofRowCount, 3);
  assert.equal(out.NF.globalRowNodeIds.length, 42);

  assert.equal(out.NF.semanticOverlay.globalInfrastructureSemanticReady, true);
  assert.equal(out.NF.semanticOverlay.globalRowDerivationsReady, true);
  assert.equal(out.NF.semanticOverlay.globalPackageDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.globalFinalDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.globalSemanticNodeDerivationsReady, false);
  assert.equal(out.NF.semanticOverlay.semanticRowNodeIds.length, 42);
  assert.deepEqual(out.NF.semanticOverlay.blockedRowNodeIds, []);
  assert.equal(out.NF.semanticOverlay.semanticRowBindings.length, 42);
  assert.equal(out.NF.semanticOverlay.blockedPackageNodeIds.length > 0, true);
  assert.deepEqual(out.NF.semanticOverlay.blockedFinalNodeIds, finalNodeIds);
  assert.equal(
    out.NF.semanticOverlay.semanticRowNodeIds.includes('Row.BIface'),
    true,
  );
  assert.equal(
    out.NF.semanticOverlay.semanticRowNodeIds.includes('G.ThresholdCert.proof'),
    true,
  );

  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'GlobalDAG.PackageDerivations',
    'GlobalDAG.FinalDerivations',
  ]);
  assert.equal(out.NF.rowSchemaAndRouteRefinementOnly, true);
  assert.equal(out.NF.mathematicalGovernedUniverseCompletenessNotClaimed, true);
  assert.equal(out.NF.primitiveProofRuleSoundnessNotClaimedHere, true);
  assert.equal(out.NF.legacyFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, finalNodeIds);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('global row successor rejects final purpose while package and final derivations remain blocked', async () => {
  const out = await CheckGlobalProofDAGRowSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGRowSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic global row successor is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit global row final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGRowFinalTheoremReadiness0(makeInput0());

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGRowFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('global row successor rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.globalRowDerivationsReady = true;

  const out = await CheckGlobalProofDAGRowSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowSuccessor0.input');
  assert.deepEqual(out.Path, ['globalRowDerivationsReady']);
  assert.equal(
    out.Witness.reason,
    'semantic global row successor rejects caller-supplied readiness assertions',
  );
});

test('global row successor rejects a final-purpose child KBundle', async () => {
  const input = makeInput0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGRowSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('global row successor rejects a stale Sigma-only KBundle', async () => {
  const input = makeGlobalProofDAGRowSuccessor0({
    KBundle: makeKBundleSigmaSuccessor0(),
  });

  const out = await CheckGlobalProofDAGRowSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'semantic infrastructure predecessor global gate rejected before row upgrade',
  );
});

test('global row successor rejects a malformed global row premise at the row semantic checker', async () => {
  const dag = makeSyntheticGlobalProofDAG0();
  dag.Nodes = dag.Nodes.map((node) => (
    node.id === 'Row.RW'
      ? withoutDigest0(node, { premises: ['K.Record'] })
      : node
  ));
  const out = await CheckGlobalProofDAGRowSuccessor0(makeInput0({
    LegacyGlobalProofDAG: dag,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowSuccessor0.semanticRows');
  assert.equal(out.Witness.reason, 'semantic global row checker rejected');
  assert.equal(
    out.Witness.inner.witness.reason,
    'global row-family node must retain the exact Record and Transport prerequisites',
  );
});

test('global row successor rejects a stale row semantic binding digest', async () => {
  const input = makeInput0();
  input.RowSemanticDerivations = {
    ...input.RowSemanticDerivations,
    lockedNANDBindings: input.RowSemanticDerivations.lockedNANDBindings.map(
      (entry) => (
        entry.rowKind === 'TraceCert'
          ? {
              ...entry,
              certificateDigest: {
                alg: 'SHA256',
                hex: '0'.repeat(64),
              },
            }
          : entry
      ),
    ),
  };

  const out = await CheckGlobalProofDAGRowSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGRowSuccessor0.semanticRows');
  assert.equal(out.Witness.reason, 'semantic global row checker rejected');
});

test('global row overlay binds every active row node to its computed derivation digest', async () => {
  const out = await CheckGlobalProofDAGRowSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const derivationByNodeId = new Map(
    out.NF.globalRowDerivationDigests.map((entry) => [entry.nodeId, entry]),
  );
  for (const binding of out.NF.semanticOverlay.semanticRowBindings) {
    const derivation = derivationByNodeId.get(binding.nodeId);
    assert.equal(binding.derivationDigest.hex, derivation.digest.hex);
    assert.equal(binding.globalNodeDigest.hex, derivation.globalNodeDigest.hex);
    assert.equal(
      binding.checkerContractDigest.hex,
      derivation.checkerContractDigest.hex,
    );
    assert.equal(binding.conclusionDigest.hex, derivation.conclusionDigest.hex);
  }
  const rowGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.GlobalDAG.RowDerivations',
  );
  assert.equal(rowGate.ready, true);
  const finalGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.FinalTheorem.Readiness',
  );
  assert.equal(finalGate.ready, false);
});
