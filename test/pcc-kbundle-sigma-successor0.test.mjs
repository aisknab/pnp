import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKImplTruthVecSuccessor0,
} from '../pcc-kimpl-truthvec-successor0.mjs';

import {
  CheckKBundleSigmaFinalTheoremReadiness0,
  CheckKBundleSigmaSuccessor0,
  makeKBundleSigmaSuccessor0,
} from '../pcc-kbundle-sigma-successor0.mjs';

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
    programId: 'kbundle.sigma.program',
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
    evaluationId: 'kbundle.sigma.eval',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.kbundle.sigma',
      RuleName: 'FiniteRel',
      Conclusion: conclusion,
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({ Purpose = 'development' } = {}) {
  return makeKBundleSigmaSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
    Purpose,
  });
}

test('semantic Sigma KBundle makes V53/V54 ready and leaves reflection blocked', async () => {
  const out = await CheckKBundleSigmaSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleSigmaSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorKBundleAccepted, true);
  assert.equal(out.NF.predecessorKBundleDevelopmentOnly, true);
  assert.equal(out.NF.predecessorSemanticK0ConformanceReady, true);
  assert.equal(out.NF.predecessorSemanticSigmaReady, false);
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplKernelReady, true);
  assert.deepEqual(out.NF.semanticKImplSupportedRules, completeRules);
  assert.deepEqual(out.NF.semanticKImplMissingRules, []);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.equal(out.NF.semanticSigmaDerivationsReady, true);
  assert.equal(out.NF.semanticSigmaDerivationCount, 2);
  assert.deepEqual(out.NF.semanticSigmaTheorems, ['V53', 'V54']);
  assert.equal(out.NF.v53Ready, true);
  assert.equal(out.NF.v54Ready, true);
  assert.equal(out.NF.semanticReflectionReady, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.computedReadiness.blockerCoordinates, [
    'Reflection.SemanticSoundness',
  ]);
  assert.equal(
    out.NF.computedReadiness.blockers.find(
      (entry) => entry.coordinate === 'Sigma.SemanticDerivations',
    ).ready,
    true,
  );
});

test('semantic Sigma KBundle rejects final purpose while reflection remains incomplete', async () => {
  const out = await CheckKBundleSigmaSuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSigmaSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'semantic Sigma KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 1);
});

test('explicit semantic Sigma KBundle final gate rejects a development-purpose record', async () => {
  const out = await CheckKBundleSigmaFinalTheoremReadiness0(makeInput0());

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleSigmaFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('semantic Sigma KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.semanticSigmaReady = true;

  const out = await CheckKBundleSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSigmaSuccessor0.input');
  assert.deepEqual(out.Path, ['semanticSigmaReady']);
  assert.equal(
    out.Witness.reason,
    'semantic Sigma KBundle rejects caller-supplied readiness assertions',
  );
});

test('semantic Sigma KBundle rejects a final-purpose child KImpl', async () => {
  const input = makeInput0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSigmaSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
});

test('semantic Sigma KBundle rejects a stale TruthVec-only child KImpl', async () => {
  const input = makeKBundleSigmaSuccessor0();
  input.SemanticKImpl = makeKImplTruthVecSuccessor0();

  const out = await CheckKBundleSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSigmaSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'FiniteRel development semantic KImpl successor rejected',
  );
});

test('semantic Sigma KBundle rejects a stale V53 checker binding', async () => {
  const input = makeInput0();
  input.SigmaSemanticDerivations = {
    ...input.SigmaSemanticDerivations,
    derivations: input.SigmaSemanticDerivations.derivations.map((entry) => (
      entry.theorem === 'V53'
        ? { ...entry, checker: 'CheckSemanticSigmaV54Derivation0' }
        : entry
    )),
  };

  const out = await CheckKBundleSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSigmaSuccessor0.semanticSigma');
  assert.equal(
    out.Witness.reason,
    'semantic Sigma checker rejected the derivation surface',
  );
});

test('semantic Sigma KBundle propagates missing V54 through the predecessor boundary', async () => {
  const input = makeInput0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleSigmaSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSigmaSuccessor0.predecessorKBundle');
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance predecessor KBundle rejected before Sigma upgrade',
  );
});

test('semantic Sigma readiness binds the accepting Sigma checker digest', async () => {
  const out = await CheckKBundleSigmaSuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const blocker = out.NF.computedReadiness.blockers.find(
    (entry) => entry.coordinate === 'Sigma.SemanticDerivations',
  );
  assert.equal(blocker.ready, true);
  assert.equal(blocker.checker, 'CheckSemanticSigma0');
  assert.equal(blocker.digest.hex, out.NF.semanticSigmaDigest.hex);
  assert.equal(out.NF.computedReadinessDigest.alg, 'SHA256');
});
