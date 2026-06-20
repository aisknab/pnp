import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticDAGIndJudgment0,
  makeSemanticDAGIndCase0,
  makeSemanticInductionDAG0,
  makeSemanticInductionDAGNode0,
} from '../pcc-kernel-dagind-semantic0.mjs';

import {
  CheckKImplDAGIndFinalTheoremReadiness0,
  CheckKImplDAGIndSuccessor0,
  makeKImplDAGIndSuccessor0,
} from '../pcc-kimpl-dagind-successor0.mjs';

function makeDAGIndProof0({ invalid = false } = {}) {
  const graphId = 'successor.graph';
  const graph = makeSemanticInductionDAG0(graphId, [
    makeSemanticInductionDAGNode0('a'),
    makeSemanticInductionDAGNode0('b', ['a']),
  ]);

  const a = makeSemanticVar0('a', 'Bool');
  const b = makeSemanticVar0('b', 'Bool');
  const invA = makeSemanticEqJudgment0(a, a);
  const invB = makeSemanticEqJudgment0(b, b);

  const caseA = makeSemanticDAGIndCase0({
    graphId,
    nodeId: 'a',
    current: invA,
  });
  const caseB = makeSemanticDAGIndCase0({
    graphId,
    nodeId: 'b',
    current: invB,
    predecessorInvariants: [
      { nodeId: 'a', invariant: invalid ? invB : invA },
    ],
  });

  const caseProofIds = ['case.a', 'case.b'];
  const conclusion = deriveSemanticDAGIndJudgment0({
    graph,
    caseRecords: [
      caseA,
      makeSemanticDAGIndCase0({
        graphId,
        nodeId: 'b',
        current: invB,
        predecessorInvariants: [{ nodeId: 'a', invariant: invA }],
      }),
    ],
    caseProofIds,
  });

  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'inv.a',
      RuleName: 'Eq',
      Conclusion: invA,
      Payload: { op: 'refl' },
    }),
    makeSemanticProofNode0({
      id: 'inv.b',
      RuleName: 'Eq',
      Conclusion: invB,
      Payload: { op: 'refl' },
    }),
    makeSemanticProofNode0({
      id: 'inv.b.copy',
      RuleName: 'Eq',
      Conclusion: invB,
      Payload: { op: 'refl' },
    }),
    makeSemanticProofNode0({
      id: 'case.a',
      RuleName: 'Record',
      Premises: ['inv.a'],
      Conclusion: caseA,
      Payload: {
        op: 'intro',
        recordType: `DAGIndCase0.${graphId}.a`,
        fieldNames: ['current'],
      },
    }),
    makeSemanticProofNode0({
      id: 'case.b',
      RuleName: 'Record',
      Premises: invalid ? ['inv.b', 'inv.b.copy'] : ['inv.b', 'inv.a'],
      Conclusion: caseB,
      Payload: {
        op: 'intro',
        recordType: `DAGIndCase0.${graphId}.b`,
        fieldNames: ['current', 'pred.a'],
      },
    }),
    makeSemanticProofNode0({
      id: 'dag.close',
      RuleName: 'DAGInd',
      Premises: caseProofIds,
      Conclusion: conclusion,
      Payload: { op: 'close', graph },
    }),
  ]);
}

test('DAGInd successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplDAGIndSuccessor0(makeKImplDAGIndSuccessor0({
    SemanticProofDAG: makeDAGIndProof0(),
    Purpose: 'development',
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplDAGIndSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticDAGIndNodeCount, 1);
  assert.equal(out.NF.semanticKernelReady, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.supportedSemanticRules.includes('DAGInd'), true);
  assert.equal(out.NF.missingSemanticRules.includes('DAGInd'), false);
  assert.equal(out.NF.missingSemanticRules.includes('LedgerInd'), true);
  assert.equal(out.NF.missingSemanticRules.length, 12);
});

test('DAGInd successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplDAGIndSuccessor0(makeKImplDAGIndSuccessor0({
    SemanticProofDAG: makeDAGIndProof0(),
    Purpose: 'final-theorem',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDAGIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'DAGInd-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('DAGInd'), false);
  assert.equal(out.Witness.missingRules.length, 12);
});

test('DAGInd final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplDAGIndFinalTheoremReadiness0(makeKImplDAGIndSuccessor0({
    SemanticProofDAG: makeDAGIndProof0(),
    Purpose: 'development',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDAGIndFinalTheoremReadiness0.purpose');
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'DAGInd final-theorem readiness requires a final-theorem purpose record',
  );
});

test('DAGInd final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplDAGIndFinalTheoremReadiness0(makeKImplDAGIndSuccessor0({
    SemanticProofDAG: makeDAGIndProof0(),
    Purpose: 'final-theorem',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDAGIndFinalTheoremReadiness0.semanticReadiness');
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('DAGInd successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplDAGIndSuccessor0({
    SemanticProofDAG: makeDAGIndProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplDAGIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDAGIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'DAGInd successor rejects caller-supplied semantic readiness assertions',
  );
});

test('DAGInd successor rejects a weakened release policy', async () => {
  const input = makeKImplDAGIndSuccessor0({
    SemanticProofDAG: makeDAGIndProof0(),
  });
  input.Policy.finalTheoremRequiresCompleteSemanticKernel = false;

  const out = await CheckKImplDAGIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDAGIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'DAGInd successor release policy must match the fail-closed policy',
  );
});

test('DAGInd successor rejects an invalid predecessor case in development mode', async () => {
  const out = await CheckKImplDAGIndSuccessor0(makeKImplDAGIndSuccessor0({
    SemanticProofDAG: makeDAGIndProof0({ invalid: true }),
    Purpose: 'development',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDAGIndSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'DAGInd predecessor invariant must exactly match the earlier node invariant',
  );
});

test('DAGInd successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
  });

  const out = await CheckKImplDAGIndSuccessor0(makeKImplDAGIndSuccessor0({
    KImpl: badKImpl,
    SemanticProofDAG: makeDAGIndProof0(),
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDAGIndSuccessor0.predecessorSuccessor');
  assert.equal(
    out.Witness.inner.witness.inner.witness.inner.witness.reason,
    'kernel rule table is missing a primitive rule',
  );
});
