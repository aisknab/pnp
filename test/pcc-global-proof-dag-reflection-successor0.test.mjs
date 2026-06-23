import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleSigmaSuccessor0,
} from '../pcc-kbundle-sigma-successor0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from '../pcc-kbundle-reflection-successor0.mjs';

import {
  makeGlobalProofDAGNode0,
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
  CheckGlobalProofDAGReflectionFinalTheoremReadiness0,
  CheckGlobalProofDAGReflectionSuccessor0,
  makeGlobalProofDAGReflectionSuccessor0,
} from '../pcc-global-proof-dag-reflection-successor0.mjs';

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

const reflectionNodeIds = [
  'Reflection.CheckVerifierFrag0',
  'Reflection.CheckBoot0',
  'Reflection.CheckBootBatch0',
  'Reflection.CheckBootAudit0',
  'Reflection.CheckKImpl0',
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
    programId: 'global.reflection.program',
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
    evaluationId: 'global.reflection.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global.reflection',
      RuleName: 'FiniteRel',
      Conclusion: deriveSemanticFiniteRelJudgment0({ spec }),
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({ Purpose = 'development' } = {}) {
  const KBundle = makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalProofDAGReflectionSuccessor0({ KBundle, Purpose });
}

test('semantic reflection global gate activates reflection nodes and keeps finals quarantined', async () => {
  const out = await CheckGlobalProofDAGReflectionSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGReflectionSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.predecessorGlobalFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.predecessorGlobalSemanticKernelNodeIds, completeNodeIds);
  assert.deepEqual(out.NF.predecessorGlobalSemanticSigmaNodeIds, [
    'Sigma.V53',
    'Sigma.V54',
  ]);
  assert.equal(out.NF.predecessorSemanticK0ConformanceReady, true);
  assert.equal(out.NF.predecessorSemanticSigmaReady, true);
  assert.equal(out.NF.predecessorSemanticReflectionReady, false);
  assert.equal(out.NF.semanticKBundleDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKBundleDevelopmentOnly, true);
  assert.deepEqual(out.NF.semanticKBundleSupportedRules, completeRules);
  assert.deepEqual(out.NF.semanticKBundleMissingRules, []);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.equal(out.NF.semanticReflectionReady, true);
  assert.equal(out.NF.semanticKBundleFinalProbeAccepted, true);
  assert.equal(out.NF.kBundleFinalReady, true);

  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, completeNodeIds);
  assert.deepEqual(out.NF.semanticOverlay.blockedKernelNodeIds, []);
  assert.deepEqual(out.NF.semanticOverlay.semanticSigmaNodeIds, [
    'Sigma.V53',
    'Sigma.V54',
  ]);
  assert.deepEqual(out.NF.semanticOverlay.blockedSigmaNodeIds, []);
  assert.deepEqual(
    out.NF.semanticOverlay.semanticReflectionNodeIds,
    reflectionNodeIds,
  );
  assert.deepEqual(out.NF.semanticOverlay.blockedReflectionNodeIds, []);
  assert.equal(out.NF.semanticOverlay.semanticReflectionBindings.length, 5);
  assert.equal(out.NF.semanticOverlay.primitiveSemanticRuleCoverageComplete, true);
  assert.equal(out.NF.semanticOverlay.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticOverlay.semanticSigmaReady, true);
  assert.equal(out.NF.semanticOverlay.semanticReflectionReady, true);
  assert.equal(out.NF.semanticOverlay.globalSemanticNodeDerivationsReady, false);
  assert.equal(out.NF.boundedExecutableReflectionRefinementsOnly, true);
  assert.equal(out.NF.unrestrictedCheckerSoundnessNotClaimed, true);

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
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('semantic reflection global gate rejects final purpose while global node derivations remain blocked', async () => {
  const out = await CheckGlobalProofDAGReflectionSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGReflectionSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic reflection global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 1);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit semantic reflection global final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGReflectionFinalTheoremReadiness0(
    makeInput0(),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGReflectionFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('semantic reflection global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGReflectionSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'semantic reflection global-DAG rejects caller-supplied readiness assertions',
  );
});

test('semantic reflection global gate rejects a final-purpose child KBundle', async () => {
  const input = makeInput0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGReflectionSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('semantic reflection global gate rejects a stale Sigma-only KBundle', async () => {
  const input = makeGlobalProofDAGReflectionSuccessor0({
    KBundle: makeKBundleSigmaSuccessor0(),
  });

  const out = await CheckGlobalProofDAGReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGReflectionSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'semantic reflection development KBundle rejected',
  );
});

test('semantic reflection global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeInput0();
  input.Policy.predecessorGlobalGateCannotImplyReflectionReadiness = false;

  const out = await CheckGlobalProofDAGReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGReflectionSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'semantic reflection global-DAG release policy must match the fail-closed policy',
  );
});

test('semantic reflection global gate rejects a malformed legacy reflection node at the overlay boundary', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.map((node) => (
    node.id === 'Reflection.CheckBoot0'
      ? makeGlobalProofDAGNode0({
          id: 'Reflection.CheckBoot0',
          kind: 'reflection',
          label: 'CheckBoot0',
          premises: ['K.Record'],
          conclusion: {
            tag: 'ReflectionAccepted0',
            checker: 'CheckBoot0',
          },
        })
      : node
  ));
  const input = makeGlobalProofDAGReflectionSuccessor0({
    KBundle: makeKBundleReflectionSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
    }),
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGReflectionSuccessor0.semanticOverlay');
  assert.equal(
    out.Witness.reason,
    'semantic reflection node must retain the exact Record and Transport prerequisites',
  );
});

test('semantic reflection overlay binds every reflection node to its computed refinement digest', async () => {
  const out = await CheckGlobalProofDAGReflectionSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const refinementByChecker = new Map(
    out.NF.semanticReflectionRefinementDigests.map((entry) => [
      entry.checker,
      entry,
    ]),
  );
  for (const binding of out.NF.semanticOverlay.semanticReflectionBindings) {
    const refinement = refinementByChecker.get(binding.checker);
    assert.equal(binding.refinementDigest.hex, refinement.digest.hex);
    assert.equal(binding.registryEntryDigest.hex, refinement.registryEntryDigest.hex);
    assert.equal(binding.checkerContractDigest.hex, refinement.checkerContractDigest.hex);
    assert.equal(binding.positiveRecordDigest.hex, refinement.positiveRecordDigest.hex);
    assert.equal(binding.negativeRecordDigest.hex, refinement.negativeRecordDigest.hex);
    assert.equal(binding.conclusionDigest.hex, refinement.conclusionDigest.hex);
  }
  assert.equal(
    out.NF.computedGlobalGate.semanticKBundleComputedReadinessDigest.hex,
    out.NF.semanticKBundleComputedReadinessDigest.hex,
  );
  const bundleGate = out.NF.computedGlobalGate.nodes.find(
    (node) => node.id === 'Gate.KBundle.ReflectionFinalReadiness',
  );
  assert.equal(bundleGate.ready, true);
});
