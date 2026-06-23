import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplTruthVecSuccessor0,
} from '../pcc-kimpl-truthvec-successor0.mjs';

import {
  CheckKBundleK0ConformanceFinalTheoremReadiness0,
  CheckKBundleK0ConformanceSuccessor0,
  makeKBundleK0ConformanceSuccessor0,
} from '../pcc-kbundle-k0conformance-successor0.mjs';

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

const completeRules = [
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
    programId: 'kbundle.k0conformance.program',
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
    evaluationId: 'kbundle.k0conformance.eval',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.k0conformance.kbundle',
      RuleName: 'FiniteRel',
      Conclusion: conclusion,
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({ Purpose = 'development' } = {}) {
  return makeKBundleK0ConformanceSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
    Purpose,
  });
}

test('semantic K0 conformance KBundle makes K0 ready and leaves Sigma/reflection blocked', async () => {
  const out = await CheckKBundleK0ConformanceSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleK0ConformanceSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorSemanticConformanceReady, false);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplKernelReady, true);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, completeRules);
  assert.deepEqual(out.NF.semanticKImplMissingRules, []);
  assert.equal(out.NF.semanticConformanceReady, true);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticConformanceObligationCount, 16);
  assert.equal(out.NF.semanticSigmaReady, false);
  assert.equal(out.NF.semanticReflectionReady, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.computedReadiness.blockerCoordinates, [
    'Sigma.SemanticDerivations',
    'Reflection.SemanticSoundness',
  ]);
  assert.equal(
    out.NF.computedReadiness.blockers.find(
      (entry) => entry.coordinate === 'K0.SemanticConformance',
    ).ready,
    true,
  );
});

test('semantic K0 conformance KBundle rejects final purpose while Sigma/reflection are incomplete', async () => {
  const out = await CheckKBundleK0ConformanceSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleK0ConformanceSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 2);
});

test('explicit semantic K0 conformance KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleK0ConformanceFinalTheoremReadiness0(makeInput0());

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleK0ConformanceFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('semantic K0 conformance KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.semanticConformanceReady = true;

  const out = await CheckKBundleK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleK0ConformanceSuccessor0.input');
  assert.deepEqual(out.Path, ['semanticConformanceReady']);
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance KBundle rejects caller-supplied readiness assertions',
  );
});

test('semantic K0 conformance KBundle rejects a final-purpose child KImpl', async () => {
  const input = makeInput0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleK0ConformanceSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('semantic K0 conformance KBundle rejects a stale TruthVec-only child KImpl', async () => {
  const input = makeKBundleK0ConformanceSuccessor0();
  input.SemanticKImpl = makeKImplTruthVecSuccessor0();

  const out = await CheckKBundleK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleK0ConformanceSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'FiniteRel development semantic KImpl successor rejected',
  );
});

test('semantic K0 conformance KBundle rejects a stale semantic conformance obligation', async () => {
  const input = makeInput0();
  input.K0SemanticConformance = {
    ...input.K0SemanticConformance,
    obligations: input.K0SemanticConformance.obligations.map((entry) => (
      entry.ruleName === 'Eq'
        ? { ...entry, proofChecker: 'CheckSemanticKernelProofFiniteRel0' }
        : entry
    )),
  };

  const out = await CheckKBundleK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleK0ConformanceSuccessor0.semanticConformance');
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance checker rejected the conformance surface',
  );
});

test('semantic K0 conformance KBundle propagates Sigma structural rejection through the predecessor boundary', async () => {
  const input = makeInput0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleK0ConformanceSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleK0ConformanceSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'FiniteRel predecessor KBundle rejected the complete primitive semantic base',
  );
});
