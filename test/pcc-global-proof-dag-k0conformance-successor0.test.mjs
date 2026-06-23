import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleFiniteRelSuccessor0,
} from '../pcc-kbundle-finiterel-successor0.mjs';

import {
  makeKBundleK0ConformanceSuccessor0,
} from '../pcc-kbundle-k0conformance-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

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

import {
  CheckGlobalProofDAGK0ConformanceFinalTheoremReadiness0,
  CheckGlobalProofDAGK0ConformanceSuccessor0,
  makeGlobalProofDAGK0ConformanceSuccessor0,
} from '../pcc-global-proof-dag-k0conformance-successor0.mjs';

const completeNodeIds = [
  'K.Eq',
  'K.Subst',
  'K.Record',
  'K.DAGInd',
  'K.LedgerInd',
  'K.OblTopoInd',
  'K.TraceInd',
  'K.FiniteExhaust',
  'K.DPInd',
  'K.Hall',
  'K.RankInd',
  'K.MinCounterexample',
  'K.IntArith',
  'K.Transport',
  'K.TruthVec',
  'K.FiniteRel',
];

const completeRules = completeNodeIds.map((id) => id.slice(2));

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
    programId: 'global.k0conformance.program',
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
    evaluationId: 'global.k0conformance.eval',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.k0conformance.global',
      RuleName: 'FiniteRel',
      Conclusion: conclusion,
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({ Purpose = 'development' } = {}) {
  const KBundle = makeKBundleK0ConformanceSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalProofDAGK0ConformanceSuccessor0({ KBundle, Purpose });
}

test('semantic K0 conformance global gate records K0 readiness and keeps finals quarantined', async () => {
  const out = await CheckGlobalProofDAGK0ConformanceSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGK0ConformanceSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.predecessorGlobalFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.predecessorGlobalSemanticKernelNodeIds, completeNodeIds);
  assert.equal(out.NF.semanticKBundleDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKBundleDevelopmentOnly, true);
  assert.deepEqual(out.NF.semanticKBundleSupportedRules, completeRules);
  assert.deepEqual(out.NF.semanticKBundleMissingRules, []);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticKImplFinalReady, true);
  assert.equal(out.NF.semanticKBundleFinalProbeAccepted, false);
  assert.equal(out.NF.kBundleFinalReady, false);
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, completeNodeIds);
  assert.deepEqual(out.NF.semanticOverlay.blockedKernelNodeIds, []);
  assert.equal(out.NF.semanticOverlay.primitiveSemanticRuleCoverageComplete, true);
  assert.equal(out.NF.semanticOverlay.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticOverlay.semanticSigmaReady, false);
  assert.equal(out.NF.semanticOverlay.semanticReflectionReady, false);
  assert.equal(out.NF.semanticOverlay.globalSemanticNodeDerivationsReady, false);
  assert.equal(out.NF.legacyFinalNodesStructurallyAccepted, true);
  assert.equal(out.NF.legacyFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, [
    'Final.PackageSoundness',
    'Final.GeneratedPackageSufficiency',
    'Final.AcceptedPackageImpliesSATinP',
    'Final.AcceptedPackageImpliesPEqualsNP',
  ]);
  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'KBundle.K0ConformanceFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('semantic K0 conformance global gate rejects final purpose while Sigma/reflection/global derivations are blocked', async () => {
  const out = await CheckGlobalProofDAGK0ConformanceSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGK0ConformanceSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit semantic K0 conformance global final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGK0ConformanceFinalTheoremReadiness0(
    makeInput0(),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGK0ConformanceFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('semantic K0 conformance global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGK0ConformanceSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance global-DAG rejects caller-supplied readiness assertions',
  );
});

test('semantic K0 conformance global gate rejects a final-purpose child KBundle', async () => {
  const input = makeInput0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGK0ConformanceSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('semantic K0 conformance global gate rejects a stale FiniteRel KBundle', async () => {
  const input = makeGlobalProofDAGK0ConformanceSuccessor0({
    KBundle: makeKBundleFiniteRelSuccessor0(),
  });

  const out = await CheckGlobalProofDAGK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGK0ConformanceSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance development KBundle rejected',
  );
});

test('semantic K0 conformance global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeInput0();
  input.Policy.predecessorGlobalGateCannotImplyK0ConformanceReadiness = false;

  const out = await CheckGlobalProofDAGK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGK0ConformanceSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance global-DAG release policy must match the fail-closed policy',
  );
});

test('semantic K0 conformance global gate propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGK0ConformanceSuccessor0({
    KBundle: makeKBundleK0ConformanceSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
    }),
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGK0ConformanceSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'FiniteRel predecessor global gate rejected the complete primitive semantic base',
  );
});

test('computed semantic K0 conformance global gate binds the expanded KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGK0ConformanceSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(
    out.NF.computedGlobalGate.semanticKBundleComputedReadinessDigest.hex,
    out.NF.semanticKBundleComputedReadinessDigest.hex,
  );
  const finalGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.FinalTheorem.Readiness',
  );
  assert.equal(finalGate.ready, false);
  assert.deepEqual(finalGate.premises, [
    'Gate.KBundle.K0ConformanceFinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.semanticOverlay.semanticK0ConformanceReady, true);
});
