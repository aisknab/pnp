import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplTruthVecSuccessor0,
} from '../pcc-kimpl-truthvec-successor0.mjs';

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
  CheckKBundleFiniteRelFinalTheoremReadiness0,
  CheckKBundleFiniteRelSuccessor0,
  makeKBundleFiniteRelSuccessor0,
} from '../pcc-kbundle-finiterel-successor0.mjs';

const predecessorRules = [
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
];

const finiteRelRules = [...predecessorRules, 'FiniteRel'];

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
    programId: 'kbundle.finiterel.program',
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
    evaluationId: 'kbundle.finiterel.eval',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.kbundle',
      RuleName: 'FiniteRel',
      Conclusion: conclusion,
      Payload: { op: 'verify', spec },
    }),
  ]);
}

test('FiniteRel KBundle completes primitive coverage but remains development-only', async () => {
  const out = await CheckKBundleFiniteRelSuccessor0(
    makeKBundleFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleFiniteRelSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorKBundlePublicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.predecessorKBundleSupportedRules, predecessorRules);
  assert.deepEqual(out.NF.predecessorKBundleMissingRules, ['FiniteRel']);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplDevelopmentOnly, true);
  assert.equal(out.NF.semanticKImplPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticKImplKernelReady, true);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, finiteRelRules);
  assert.deepEqual(out.NF.semanticKImplMissingRules, []);
  assert.equal(out.NF.semanticFiniteRelNodeCount, 1);
  assert.equal(
    out.NF.semanticKImplFinalChecker,
    'CheckKImplFiniteRelFinalTheoremReadiness0',
  );
  assert.equal(out.NF.semanticKImplFinalProbeAccepted, true);
  assert.equal(out.NF.semanticKImplFinalReady, true);
  assert.equal(out.NF.legacyBundleAccepted, true);
  assert.equal(out.NF.legacyConformanceSemanticStatus, 'structural-only');
  assert.equal(out.NF.legacySigmaSemanticStatus, 'registry-shape-only');
  assert.equal(out.NF.legacyReflectionSemanticStatus, 'mapping-shape-only');
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.computedReadiness.blockerCoordinates, [
    'K0.SemanticConformance',
    'Sigma.SemanticDerivations',
    'Reflection.SemanticSoundness',
  ]);
  const kernelBlocker = out.NF.computedReadiness.blockers.find(
    (entry) => entry.coordinate === 'KImpl.SemanticRuleCoverage',
  );
  assert.equal(kernelBlocker.ready, true);
  assert.equal(kernelBlocker.reason, null);
});

test('FiniteRel KBundle rejects final-theorem purpose while non-kernel surfaces are incomplete', async () => {
  const out = await CheckKBundleFiniteRelSuccessor0(
    makeKBundleFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteRelSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 3);
});

test('explicit FiniteRel KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleFiniteRelFinalTheoremReadiness0(
    makeKBundleFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleFiniteRelFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('explicit FiniteRel KBundle final gate remains blocked beyond KImpl', async () => {
  const out = await CheckKBundleFiniteRelFinalTheoremReadiness0(
    makeKBundleFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleFiniteRelFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 3);
  const kernelBlocker = out.Witness.blockers.find(
    (entry) => entry.coordinate === 'KImpl.SemanticRuleCoverage',
  );
  assert.equal(kernelBlocker.ready, true);
});

test('FiniteRel KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleFiniteRelSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteRelSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('FiniteRel KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleFiniteRelSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteRelSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('FiniteRel KBundle rejects a stale TruthVec-only child KImpl', async () => {
  const input = makeKBundleFiniteRelSuccessor0();
  input.SemanticKImpl = makeKImplTruthVecSuccessor0();

  const out = await CheckKBundleFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteRelSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'FiniteRel development semantic KImpl successor rejected',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'FiniteRel successor KImpl kind must be KImplSemanticFiniteRelSuccessor0',
  );
});

test('FiniteRel KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleFiniteRelSuccessor0();
  input.Policy.predecessorKBundleCannotImplyFiniteRelReadiness = false;

  const out = await CheckKBundleFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteRelSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel semantic KBundle release policy must match the fail-closed policy',
  );
});

test('FiniteRel KBundle propagates Sigma structural rejection through the TruthVec predecessor boundary', async () => {
  const input = makeKBundleFiniteRelSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleFiniteRelSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'TruthVec predecessor KBundle rejected the fifteen-rule semantic base',
  );
});

test('FiniteRel KBundle readiness binds the accepting KImpl final-probe digest', async () => {
  const out = await CheckKBundleFiniteRelSuccessor0(
    makeKBundleFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
    }),
  );

  assert.equal(out.tag, 'accept');
  const blocker = out.NF.computedReadiness.blockers.find(
    (entry) => entry.coordinate === 'KImpl.SemanticRuleCoverage',
  );
  assert.equal(blocker.ready, true);
  assert.equal(
    blocker.digest.hex,
    out.NF.semanticKImplFinalProbeDigest.hex,
  );
  assert.equal(
    blocker.checker,
    'CheckKImplFiniteRelFinalTheoremReadiness0',
  );
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
