import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelConformanceSuite0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplTruthVecSuccessor0,
} from '../pcc-kimpl-truthvec-successor0.mjs';

import {
  makeKImplFiniteRelSuccessor0,
} from '../pcc-kimpl-finiterel-successor0.mjs';

import {
  CheckSemanticK0Conformance0,
  makeSemanticK0ConformanceInput0,
  makeSemanticK0ConformanceSuite0,
} from '../pcc-k0-semantic-conformance0.mjs';

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
    programId: 'k0.semantic.finiterel.program',
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
    evaluationId: 'k0.semantic.finiterel.eval',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.k0.semantic',
      RuleName: 'FiniteRel',
      Conclusion: conclusion,
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0({ K0 = makeKernelConformanceSuite0() } = {}) {
  const KImpl = makeKImplFiniteRelSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  return makeSemanticK0ConformanceInput0({
    KImpl,
    K0,
    SemanticConformance: makeSemanticK0ConformanceSuite0({ K0 }),
  });
}

test('semantic K0 conformance accepts exact local soundness obligations for every primitive rule', async () => {
  const out = await CheckSemanticK0Conformance0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckSemanticK0Conformance0');
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticConformanceReady, true);
  assert.equal(out.NF.semanticKImplFinalReady, true);
  assert.equal(out.NF.semanticKernelReady, true);
  assert.equal(out.NF.primitiveRuleCoverageComplete, true);
  assert.deepEqual(out.NF.missingSemanticRules, []);
  assert.equal(out.NF.semanticConformanceObligationCount, 16);
  assert.deepEqual(out.NF.semanticConformanceCoveredRules, [
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
  ]);
  assert.equal(out.NF.sigmaReady, false);
  assert.equal(out.NF.reflectionReady, false);
});

test('semantic K0 conformance rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeInput0(),
    semanticK0ConformanceReady: true,
  };

  const out = await CheckSemanticK0Conformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticK0Conformance0.input');
  assert.deepEqual(out.Path, ['semanticK0ConformanceReady']);
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance rejects caller-supplied readiness or soundness assertions',
  );
});

test('semantic K0 conformance rejects caller soundness fields inside an obligation', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    SemanticConformance: {
      ...base.SemanticConformance,
      obligations: base.SemanticConformance.obligations.map((entry, index) => (
        index === 0 ? { ...entry, sound: true } : entry
      )),
    },
  };

  const out = await CheckSemanticK0Conformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticK0Conformance0.semanticConformanceSuite');
  assert.deepEqual(out.Path, ['SemanticConformance', 'obligations', 0, 'sound']);
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance obligation rejects caller-supplied soundness assertions',
  );
});

test('semantic K0 conformance rejects a stale executable checker binding', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    SemanticConformance: {
      ...base.SemanticConformance,
      obligations: base.SemanticConformance.obligations.map((entry) => (
        entry.ruleName === 'FiniteRel'
          ? { ...entry, primitiveChecker: 'CheckSemanticKernelProofTruthVec0' }
          : entry
      )),
    },
  };

  const out = await CheckSemanticK0Conformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticK0Conformance0.semanticConformanceSuite');
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance obligation must exactly match the computed local soundness binding',
  );
});

test('semantic K0 conformance rejects missing legacy structural coverage before upgrade', async () => {
  const K0 = makeKernelConformanceSuite0();
  K0.nodes = K0.nodes.filter((node) => node.RuleName !== 'FiniteRel');
  const input = makeInput0({ K0 });

  const out = await CheckSemanticK0Conformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticK0Conformance0.legacyConformance');
  assert.equal(
    out.Witness.reason,
    'legacy K0 conformance shape checker rejected before semantic upgrade',
  );
});

test('semantic K0 conformance rejects a stale TruthVec-only KImpl', async () => {
  const K0 = makeKernelConformanceSuite0();
  const input = makeSemanticK0ConformanceInput0({
    KImpl: makeKImplTruthVecSuccessor0(),
    K0,
    SemanticConformance: makeSemanticK0ConformanceSuite0({ K0 }),
  });

  const out = await CheckSemanticK0Conformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticK0Conformance0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'semantic K0 conformance requires a complete final-ready primitive semantic KImpl',
  );
});
