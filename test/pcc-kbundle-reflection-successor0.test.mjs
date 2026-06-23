import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplTruthVecSuccessor0,
} from '../pcc-kimpl-truthvec-successor0.mjs';

import {
  CheckKBundleReflectionFinalTheoremReadiness0,
  CheckKBundleReflectionSuccessor0,
  makeKBundleReflectionSuccessor0,
} from '../pcc-kbundle-reflection-successor0.mjs';

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

const requiredCheckers = [
  'CheckVerifierFrag0',
  'CheckBoot0',
  'CheckBootBatch0',
  'CheckBootAudit0',
  'CheckKImpl0',
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
    programId: 'kbundle.reflection.program',
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
    evaluationId: 'kbundle.reflection.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.kbundle.reflection',
      RuleName: 'FiniteRel',
      Conclusion: deriveSemanticFiniteRelJudgment0({ spec }),
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({ Purpose = 'development' } = {}) {
  return makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
    Purpose,
  });
}

test('semantic reflection KBundle makes every bundle semantic surface ready in development mode', async () => {
  const out = await CheckKBundleReflectionSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleReflectionSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorSemanticK0ConformanceReady, true);
  assert.equal(out.NF.predecessorSemanticSigmaReady, true);
  assert.equal(out.NF.predecessorSemanticReflectionReady, false);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplKernelReady, true);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, completeRules);
  assert.deepEqual(out.NF.semanticKImplMissingRules, []);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.equal(out.NF.semanticReflectionReady, true);
  assert.equal(out.NF.semanticReflectionSoundnessSurfaceReady, true);
  assert.deepEqual(out.NF.semanticReflectionCheckers, requiredCheckers);
  assert.equal(out.NF.semanticReflectionCount, 5);
  assert.equal(out.NF.boundedExecutableReflectionRefinementsOnly, true);
  assert.equal(out.NF.unrestrictedCheckerSoundnessNotClaimed, true);
  assert.deepEqual(out.NF.computedReadiness.blockerCoordinates, []);
  assert.equal(out.NF.computedReadiness.finalTheoremReady, true);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('semantic reflection KBundle accepts explicit final purpose after all bundle surfaces are ready', async () => {
  const out = await CheckKBundleReflectionSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'final-theorem-ready');
  assert.equal(out.NF.finalTheoremReady, true);
  assert.equal(out.NF.publicTheoremEmissionAllowed, true);
  assert.deepEqual(out.NF.computedReadiness.blockerCoordinates, []);
});

test('explicit semantic reflection KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleReflectionFinalTheoremReadiness0(makeInput0());

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleReflectionFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('explicit semantic reflection KBundle final gate accepts a final-purpose record', async () => {
  const out = await CheckKBundleReflectionFinalTheoremReadiness0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.finalTheoremReady, true);
  assert.equal(out.NF.publicTheoremEmissionAllowed, true);
});

test('semantic reflection KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.semanticReflectionReady = true;

  const out = await CheckKBundleReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleReflectionSuccessor0.input');
  assert.deepEqual(out.Path, ['semanticReflectionReady']);
  assert.equal(
    out.Witness.reason,
    'semantic reflection KBundle rejects caller-supplied readiness assertions',
  );
});

test('semantic reflection KBundle rejects a final-purpose child KImpl', async () => {
  const input = makeInput0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleReflectionSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('semantic reflection KBundle rejects a stale TruthVec-only child KImpl', async () => {
  const input = makeKBundleReflectionSuccessor0();
  input.SemanticKImpl = makeKImplTruthVecSuccessor0();

  const out = await CheckKBundleReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleReflectionSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'FiniteRel development semantic KImpl successor rejected',
  );
});

test('semantic reflection KBundle rejects a stale reflection checker contract', async () => {
  const input = makeInput0();
  input.ReflectionSemanticRefinements = {
    ...input.ReflectionSemanticRefinements,
    refinements: input.ReflectionSemanticRefinements.refinements.map((entry) => (
      entry.checker === 'CheckBootAudit0'
        ? {
            ...entry,
            checkerContractDigest: {
              alg: 'SHA256',
              hex: '0'.repeat(64),
            },
          }
        : entry
    )),
  };

  const out = await CheckKBundleReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleReflectionSuccessor0.semanticReflection');
  assert.equal(
    out.Witness.reason,
    'semantic reflection checker rejected the refinement surface',
  );
});

test('semantic reflection KBundle propagates missing legacy reflection coverage through the predecessor boundary', async () => {
  const input = makeInput0();
  input.ReflectionRegistry.reflections = input.ReflectionRegistry.reflections.filter(
    (entry) => entry.checker !== 'CheckBoot0',
  );

  const out = await CheckKBundleReflectionSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleReflectionSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'semantic Sigma predecessor KBundle rejected before reflection upgrade',
  );
});

test('semantic reflection KBundle binds the reflection checker digest into final readiness', async () => {
  const out = await CheckKBundleReflectionSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const blocker = out.NF.computedReadiness.blockers.find(
    (entry) => entry.coordinate === 'Reflection.SemanticSoundness',
  );
  assert.equal(blocker.ready, true);
  assert.equal(
    blocker.digest.hex,
    out.NF.semanticReflectionDigest.hex,
  );
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
