import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleTruthVecSuccessor0,
} from '../pcc-kbundle-truthvec-successor0.mjs';

import {
  makeKBundleFiniteRelSuccessor0,
} from '../pcc-kbundle-finiterel-successor0.mjs';

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
  CheckGlobalProofDAGFiniteRelFinalTheoremReadiness0,
  CheckGlobalProofDAGFiniteRelSuccessor0,
  makeGlobalProofDAGFiniteRelSuccessor0,
} from '../pcc-global-proof-dag-finiterel-successor0.mjs';

const predecessorNodeIds = [
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
];

const finiteRelRules = [
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
    tuples: [
      makeSemanticFiniteRelTuple0({ index: 0, values: ['a', 'b'] }),
    ],
  });
  const closure = makeSemanticFiniteRelNode0({
    index: 1,
    id: 'R.rtc',
    op: 'reflexive-transitive-closure',
    domainIds: ['D', 'D'],
    inputIds: ['R'],
  });
  const program = makeSemanticFiniteRelProgram0({
    programId: 'global.finiterel.program',
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
    evaluationId: 'global.finiterel.eval',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global',
      RuleName: 'FiniteRel',
      Conclusion: conclusion,
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({ Purpose = 'development' } = {}) {
  const KBundle = makeKBundleFiniteRelSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalProofDAGFiniteRelSuccessor0({ KBundle, Purpose });
}

test('FiniteRel global gate activates every primitive kernel coordinate and keeps finals quarantined', async () => {
  const out = await CheckGlobalProofDAGFiniteRelSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGFiniteRelSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.predecessorGlobalFinalNodesQuarantined, true);
  assert.deepEqual(
    out.NF.predecessorGlobalSemanticKernelNodeIds,
    predecessorNodeIds,
  );
  assert.equal(out.NF.semanticKBundleDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKBundleDevelopmentOnly, true);
  assert.equal(out.NF.semanticKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.semanticKBundleSupportedRules, finiteRelRules);
  assert.deepEqual(out.NF.semanticKBundleMissingRules, []);
  assert.equal(out.NF.semanticKImplFinalReady, true);
  assert.equal(out.NF.semanticKBundleFinalProbeAccepted, false);
  assert.equal(out.NF.kBundleFinalReady, false);
  assert.equal(out.NF.legacyGlobalDAGAccepted, true);
  assert.equal(out.NF.legacyGlobalDAGSemanticStatus, 'structural-only');
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, [
    ...predecessorNodeIds,
    'K.FiniteRel',
  ]);
  assert.deepEqual(out.NF.semanticOverlay.blockedKernelNodeIds, []);
  assert.equal(out.NF.semanticOverlay.primitiveSemanticRuleCoverageComplete, true);
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
    'KBundle.FiniteRelFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.computedGlobalGate.primitiveSemanticRuleCoverageComplete, true);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('FiniteRel global gate rejects final-theorem purpose while higher semantic surfaces are blocked', async () => {
  const out = await CheckGlobalProofDAGFiniteRelSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFiniteRelSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel successor global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit FiniteRel global final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGFiniteRelFinalTheoremReadiness0(
    makeInput0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFiniteRelFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel semantic global-DAG final readiness requires a final-theorem purpose record',
  );
});

test('explicit FiniteRel global final gate remains closed beyond primitive coverage', async () => {
  const out = await CheckGlobalProofDAGFiniteRelFinalTheoremReadiness0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFiniteRelFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.blockers.length, 2);
});

test('FiniteRel global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFiniteRelSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel semantic global-DAG rejects caller-supplied readiness assertions',
  );
});

test('FiniteRel global gate rejects a caller-provided final-purpose child KBundle', async () => {
  const input = makeInput0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFiniteRelSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('FiniteRel global gate rejects a stale TruthVec KBundle', async () => {
  const input = makeGlobalProofDAGFiniteRelSuccessor0({
    KBundle: makeKBundleTruthVecSuccessor0(),
  });

  const out = await CheckGlobalProofDAGFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFiniteRelSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'FiniteRel development semantic KBundle rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'FiniteRel semantic KBundle kind must be KBundleSemanticFiniteRelSuccessor0',
  );
});

test('FiniteRel global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeInput0();
  input.Policy.predecessorGlobalGateCannotImplyFiniteRelReadiness = false;

  const out = await CheckGlobalProofDAGFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFiniteRelSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel semantic global-DAG release policy must match the fail-closed policy',
  );
});

test('FiniteRel global gate propagates successor KBundle structural rejection', async () => {
  const bundle = makeKBundleFiniteRelSuccessor0();
  bundle.PSigma.theorems = bundle.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const input = makeGlobalProofDAGFiniteRelSuccessor0({ KBundle: bundle });

  const out = await CheckGlobalProofDAGFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFiniteRelSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'TruthVec predecessor global gate rejected the fifteen-rule semantic base',
  );
});

test('FiniteRel global gate propagates legacy structural graph rejection', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.filter(
    (node) => node.id !== 'Final.AcceptedPackageImpliesPEqualsNP',
  );
  const input = makeGlobalProofDAGFiniteRelSuccessor0({
    KBundle: makeKBundleFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
    }),
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFiniteRelSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'TruthVec predecessor global gate rejected the fifteen-rule semantic base',
  );
});

test('computed FiniteRel global gate binds the expanded KBundle readiness digest', async () => {
  const out = await CheckGlobalProofDAGFiniteRelSuccessor0(makeInput0());

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
    'Gate.KBundle.FiniteRelFinalReadiness',
    'Gate.GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(
    out.NF.semanticOverlay.semanticKernelNodeIds.includes('K.FiniteRel'),
    true,
  );
  assert.deepEqual(out.NF.semanticOverlay.blockedKernelNodeIds, []);
});
