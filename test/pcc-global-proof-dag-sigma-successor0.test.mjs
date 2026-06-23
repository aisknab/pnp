import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleK0ConformanceSuccessor0,
} from '../pcc-kbundle-k0conformance-successor0.mjs';

import {
  makeKBundleSigmaSuccessor0,
} from '../pcc-kbundle-sigma-successor0.mjs';

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
  CheckGlobalProofDAGSigmaFinalTheoremReadiness0,
  CheckGlobalProofDAGSigmaSuccessor0,
  makeGlobalProofDAGSigmaSuccessor0,
} from '../pcc-global-proof-dag-sigma-successor0.mjs';

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
    programId: 'global.sigma.program',
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
    evaluationId: 'global.sigma.eval',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global.sigma',
      RuleName: 'FiniteRel',
      Conclusion: conclusion,
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({ Purpose = 'development' } = {}) {
  const KBundle = makeKBundleSigmaSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeGlobalProofDAGSigmaSuccessor0({ KBundle, Purpose });
}

test('semantic Sigma global gate activates Sigma nodes and keeps finals quarantined', async () => {
  const out = await CheckGlobalProofDAGSigmaSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGSigmaSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalAccepted, true);
  assert.equal(out.NF.predecessorGlobalDevelopmentOnly, true);
  assert.equal(out.NF.predecessorGlobalPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.predecessorGlobalFinalNodesQuarantined, true);
  assert.deepEqual(out.NF.predecessorGlobalSemanticKernelNodeIds, completeNodeIds);
  assert.equal(out.NF.predecessorSemanticK0ConformanceReady, true);
  assert.equal(out.NF.predecessorSemanticSigmaReady, false);
  assert.equal(out.NF.semanticKBundleDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKBundleDevelopmentOnly, true);
  assert.deepEqual(out.NF.semanticKBundleSupportedRules, completeRules);
  assert.deepEqual(out.NF.semanticKBundleMissingRules, []);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.deepEqual(out.NF.semanticSigmaTheorems, ['V53', 'V54']);
  assert.equal(out.NF.semanticReflectionReady, false);
  assert.equal(out.NF.semanticKBundleFinalProbeAccepted, false);
  assert.equal(out.NF.kBundleFinalReady, false);
  assert.deepEqual(out.NF.semanticOverlay.semanticKernelNodeIds, completeNodeIds);
  assert.deepEqual(out.NF.semanticOverlay.blockedKernelNodeIds, []);
  assert.deepEqual(out.NF.semanticOverlay.semanticSigmaNodeIds, [
    'Sigma.V53',
    'Sigma.V54',
  ]);
  assert.deepEqual(out.NF.semanticOverlay.blockedSigmaNodeIds, []);
  assert.equal(out.NF.semanticOverlay.semanticSigmaBindings.length, 2);
  assert.equal(out.NF.semanticOverlay.primitiveSemanticRuleCoverageComplete, true);
  assert.equal(out.NF.semanticOverlay.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticOverlay.semanticSigmaReady, true);
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
    'KBundle.SigmaFinalReadiness',
    'GlobalDAG.SemanticNodeDerivations',
  ]);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('semantic Sigma global gate rejects final purpose while reflection/global derivations are blocked', async () => {
  const out = await CheckGlobalProofDAGSigmaSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSigmaSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(
    out.Witness.reason,
    'semantic Sigma global proof DAG is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 2);
  assert.equal(out.Witness.quarantinedFinalNodeIds.length, 4);
});

test('explicit semantic Sigma global final gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGSigmaFinalTheoremReadiness0(makeInput0());

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGSigmaFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('semantic Sigma global gate rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.finalTheoremReady = true;
  input.activeFinalNodeIds = ['Final.AcceptedPackageImpliesPEqualsNP'];

  const out = await CheckGlobalProofDAGSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSigmaSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'semantic Sigma global-DAG rejects caller-supplied readiness assertions',
  );
});

test('semantic Sigma global gate rejects a final-purpose child KBundle', async () => {
  const input = makeInput0();
  input.KBundle.Purpose = 'final-theorem';

  const out = await CheckGlobalProofDAGSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSigmaSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('semantic Sigma global gate rejects a stale K0-conformance-only KBundle', async () => {
  const input = makeGlobalProofDAGSigmaSuccessor0({
    KBundle: makeKBundleK0ConformanceSuccessor0(),
  });

  const out = await CheckGlobalProofDAGSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSigmaSuccessor0.semanticKBundle');
  assert.equal(
    out.Witness.reason,
    'semantic Sigma development KBundle rejected',
  );
});

test('semantic Sigma global gate rejects a weakened final-node quarantine policy', async () => {
  const input = makeInput0();
  input.Policy.predecessorGlobalGateCannotImplySigmaReadiness = false;

  const out = await CheckGlobalProofDAGSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSigmaSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'semantic Sigma global-DAG release policy must match the fail-closed policy',
  );
});

test('semantic Sigma global gate rejects a malformed legacy Sigma node at the overlay boundary', async () => {
  const legacy = makeSyntheticGlobalProofDAG0();
  legacy.Nodes = legacy.Nodes.map((node) => (
    node.id === 'Sigma.V53'
      ? makeGlobalProofDAGNode0({
          id: 'Sigma.V53',
          kind: 'sigma',
          label: 'V53',
          premises: ['K.FiniteRel'],
          conclusion: {
            tag: 'SigmaTheoremAccepted0',
            theorem: 'V53',
          },
        })
      : node
  ));
  const input = makeGlobalProofDAGSigmaSuccessor0({
    KBundle: makeKBundleSigmaSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
    }),
    LegacyGlobalProofDAG: legacy,
  });

  const out = await CheckGlobalProofDAGSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGSigmaSuccessor0.semanticOverlay');
  assert.equal(
    out.Witness.reason,
    'semantic Sigma node must retain the exact finite-relation and integer-arithmetic prerequisites',
  );
});

test('semantic Sigma overlay binds each global Sigma node to its derivation digest', async () => {
  const out = await CheckGlobalProofDAGSigmaSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const derivationByTheorem = new Map(
    out.NF.semanticSigmaDerivationDigests.map((entry) => [entry.theorem, entry]),
  );
  for (const binding of out.NF.semanticOverlay.semanticSigmaBindings) {
    const derivation = derivationByTheorem.get(binding.theorem);
    assert.equal(binding.derivationDigest.hex, derivation.digest.hex);
    assert.equal(binding.conclusionDigest.hex, derivation.conclusionDigest.hex);
    assert.equal(binding.checkerContractDigest.hex, derivation.checkerContractDigest.hex);
    assert.equal(binding.registryEntryDigest.hex, derivation.registryEntryDigest.hex);
  }
  assert.equal(
    out.NF.computedGlobalGate.semanticKBundleComputedReadinessDigest.hex,
    out.NF.semanticKBundleComputedReadinessDigest.hex,
  );
});
