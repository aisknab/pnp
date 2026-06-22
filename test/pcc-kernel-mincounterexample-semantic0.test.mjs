import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofMinCounterexample0,
  CheckSemanticKernelReadinessMinCounterexample0,
  deriveSemanticMinCounterexampleJudgment0,
  makeSemanticMinCandidate0,
  makeSemanticMinCounterexampleEvidence0,
  makeSemanticMinCounterexampleSearch0,
} from '../pcc-kernel-mincounterexample-semantic0.mjs';

function eqProof0(id, conclusion) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Conclusion: conclusion,
    Payload: { op: 'refl' },
  });
}

function recordProof0(id, conclusion, proofId) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Record',
    Premises: [proofId],
    Conclusion: conclusion,
    Payload: {
      op: 'intro',
      recordType: conclusion.recordType,
      fieldNames: conclusion.fields.map((field) => field.name),
    },
  });
}

function makeFixture0() {
  const searchId = 'minimum.counterexample';
  const candidates = ['c0', 'c1', 'c2'].map((id, index) => {
    const holdsTerm = makeSemanticConst0(`${id}.holds`, 'Term');
    const failsTerm = makeSemanticConst0(`${id}.fails`, 'Term');
    return makeSemanticMinCandidate0({
      index,
      id,
      orderKey: index,
      holdsJudgment: makeSemanticEqJudgment0(holdsTerm, holdsTerm),
      failsJudgment: makeSemanticEqJudgment0(failsTerm, failsTerm),
    });
  });
  const search = makeSemanticMinCounterexampleSearch0({
    searchId,
    candidates,
    terminalCoordinate: 'minimum.output',
  });

  const evidenceSpecs = [
    { candidateIndex: 0, status: 'holds' },
    { candidateIndex: 1, status: 'holds' },
    { candidateIndex: 2, status: 'fails' },
  ];
  const proofNodes = [];
  const evidenceRecords = [];
  const evidenceProofIds = [];

  for (const spec of evidenceSpecs) {
    const candidate = candidates[spec.candidateIndex];
    const judgment = spec.status === 'holds'
      ? candidate.holdsJudgment
      : candidate.failsJudgment;
    const judgmentProofId = `judgment.${candidate.id}.${spec.status}`;
    const evidenceProofId = `case.${candidate.id}.${spec.status}`;
    const evidence = makeSemanticMinCounterexampleEvidence0({
      searchId,
      candidateId: candidate.id,
      status: spec.status,
      judgment,
    });
    proofNodes.push(eqProof0(judgmentProofId, judgment));
    proofNodes.push(recordProof0(evidenceProofId, evidence, judgmentProofId));
    evidenceRecords.push(evidence);
    evidenceProofIds.push(evidenceProofId);
  }

  const conclusion = deriveSemanticMinCounterexampleJudgment0({
    search,
    evidenceRecords,
    evidenceProofIds,
  });
  const selectNode = makeSemanticProofNode0({
    id: 'minimum.select',
    RuleName: 'MinCounterexample',
    Premises: evidenceProofIds,
    Conclusion: conclusion,
    Payload: { op: 'select', search },
  });
  proofNodes.push(selectNode);

  return {
    searchId,
    candidates,
    search,
    evidenceRecords,
    evidenceProofIds,
    conclusion,
    selectNode,
    proofNodes,
  };
}

function addEvidence0({
  fixture,
  candidateIndex,
  status,
  proofNodes,
  evidenceProofId = `case.${fixture.candidates[candidateIndex].id}.${status}`,
}) {
  const candidate = fixture.candidates[candidateIndex];
  const judgment = status === 'holds'
    ? candidate.holdsJudgment
    : candidate.failsJudgment;
  const judgmentProofId = `judgment.${candidate.id}.${status}.extra`;
  const evidence = makeSemanticMinCounterexampleEvidence0({
    searchId: fixture.searchId,
    candidateId: candidate.id,
    status,
    judgment,
  });
  proofNodes.push(eqProof0(judgmentProofId, judgment));
  proofNodes.push(recordProof0(evidenceProofId, evidence, judgmentProofId));
  return { evidence, evidenceProofId };
}

test('MinCounterexample computes the least failing candidate from accepted evidence', () => {
  const fixture = makeFixture0();
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0(fixture.proofNodes),
  );

  assert.equal(out.tag, 'accept');
  assert.deepEqual(out.NF.supportedRules, [
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
  ]);
  assert.equal(out.NF.minCounterexampleNodeCount, 1);
  assert.equal(
    out.NF.missingRequiredRules.includes('MinCounterexample'),
    false,
  );
  assert.deepEqual(fixture.conclusion.candidateOrder, ['c0', 'c1', 'c2']);
  assert.deepEqual(fixture.conclusion.earlierCandidateIds, ['c0', 'c1']);
  assert.equal(fixture.conclusion.selectedCandidateId, 'c2');
  assert.equal(fixture.conclusion.selectedCandidateIndex, 2);
  assert.equal(fixture.conclusion.selectedOrderKey, 2);
  assert.equal(fixture.conclusion.earlierCandidatesSatisfy, true);
  assert.equal(fixture.conclusion.selectedCandidateFails, true);
  assert.equal(fixture.conclusion.leastFailureComputed, true);
  assert.equal(fixture.conclusion.noSearchSolverOrOracleUsed, true);
});

test('MinCounterexample accepts failure at the first candidate', () => {
  const fixture = makeFixture0();
  const nodes = [];
  const { evidence, evidenceProofId } = addEvidence0({
    fixture,
    candidateIndex: 0,
    status: 'fails',
    proofNodes: nodes,
    evidenceProofId: 'case.c0.fails.first',
  });
  const conclusion = deriveSemanticMinCounterexampleJudgment0({
    search: fixture.search,
    evidenceRecords: [evidence],
    evidenceProofIds: [evidenceProofId],
  });
  nodes.push(makeSemanticProofNode0({
    id: 'minimum.first',
    RuleName: 'MinCounterexample',
    Premises: [evidenceProofId],
    Conclusion: conclusion,
    Payload: { op: 'select', search: fixture.search },
  }));

  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0(nodes),
  );
  assert.equal(out.tag, 'accept');
  assert.equal(conclusion.selectedCandidateId, 'c0');
  assert.deepEqual(conclusion.earlierCandidateIds, []);
});

test('MinCounterexample rejects noncanonical candidate order', () => {
  const fixture = makeFixture0();
  const badSearch = {
    ...fixture.search,
    candidates: [
      { ...fixture.candidates[1], index: 0 },
      { ...fixture.candidates[0], index: 1 },
      fixture.candidates[2],
    ],
  };
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      {
        ...fixture.selectNode,
        Payload: { op: 'select', search: badSearch },
      },
    ]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample candidates must be in canonical orderKey-then-id order',
  );
});

test('MinCounterexample rejects identical hold and failure judgments', () => {
  const fixture = makeFixture0();
  const badCandidate = {
    ...fixture.candidates[0],
    failsJudgment: fixture.candidates[0].holdsJudgment,
  };
  const badSearch = {
    ...fixture.search,
    candidates: [badCandidate, ...fixture.candidates.slice(1)],
  };
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      {
        ...fixture.selectNode,
        Payload: { op: 'select', search: badSearch },
      },
    ]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample holds and fails judgments must be distinct',
  );
});

test('MinCounterexample rejects evidence supplied out of candidate order', () => {
  const fixture = makeFixture0();
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      {
        ...fixture.selectNode,
        Premises: [
          fixture.evidenceProofIds[1],
          fixture.evidenceProofIds[0],
          fixture.evidenceProofIds[2],
        ],
      },
    ]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample evidence must contain the exact candidate hold or failure judgment',
  );
});

test('MinCounterexample rejects omission of an earlier candidate', () => {
  const fixture = makeFixture0();
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      {
        ...fixture.selectNode,
        Premises: [
          fixture.evidenceProofIds[1],
          fixture.evidenceProofIds[2],
        ],
      },
    ]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample evidence must contain the exact candidate hold or failure judgment',
  );
});

test('MinCounterexample rejects an all-holds domain with no failure evidence', () => {
  const fixture = makeFixture0();
  const prefix = fixture.proofNodes.slice(0, -1);
  const { evidenceProofId } = addEvidence0({
    fixture,
    candidateIndex: 2,
    status: 'holds',
    proofNodes: prefix,
    evidenceProofId: 'case.c2.holds.all',
  });
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...prefix,
      {
        ...fixture.selectNode,
        Premises: [
          fixture.evidenceProofIds[0],
          fixture.evidenceProofIds[1],
          evidenceProofId,
        ],
      },
    ]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample candidate domain contains no accepted failing candidate',
  );
});

test('MinCounterexample rejects evidence after the first failure', () => {
  const fixture = makeFixture0();
  const nodes = fixture.proofNodes.slice(0, -1);
  const failure = addEvidence0({
    fixture,
    candidateIndex: 1,
    status: 'fails',
    proofNodes: nodes,
    evidenceProofId: 'case.c1.fails.early',
  });
  const later = addEvidence0({
    fixture,
    candidateIndex: 2,
    status: 'holds',
    proofNodes: nodes,
    evidenceProofId: 'case.c2.holds.after',
  });
  nodes.push({
    ...fixture.selectNode,
    Premises: [
      fixture.evidenceProofIds[0],
      failure.evidenceProofId,
      later.evidenceProofId,
    ],
  });

  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0(nodes),
  );
  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample failure evidence must be the terminal evidence premise',
  );
});

test('MinCounterexample rejects a substituted hold judgment', () => {
  const fixture = makeFixture0();
  const badEvidence = makeSemanticMinCounterexampleEvidence0({
    searchId: fixture.searchId,
    candidateId: 'c0',
    status: 'holds',
    judgment: fixture.candidates[1].holdsJudgment,
  });
  const badCase = recordProof0(
    fixture.evidenceProofIds[0],
    badEvidence,
    'judgment.c1.holds',
  );
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0(fixture.proofNodes.map(
      (node) => node.id === fixture.evidenceProofIds[0] ? badCase : node,
    )),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample evidence must contain the exact candidate hold or failure judgment',
  );
});

test('MinCounterexample rejects caller-supplied selected candidate assertions', () => {
  const fixture = makeFixture0();
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      {
        ...fixture.selectNode,
        Payload: {
          op: 'select',
          search: fixture.search,
          selectedCandidateId: 'c2',
          least: true,
        },
      },
    ]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofMinCounterexample0.shape');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample payload rejects caller-supplied selected candidate, minimality, completion, search, solver, or oracle assertions',
  );
});

test('MinCounterexample rejects caller-supplied minimality fields in the search', () => {
  const fixture = makeFixture0();
  const badSearch = { ...fixture.search, minimal: true };
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      {
        ...fixture.selectNode,
        Payload: { op: 'select', search: badSearch },
      },
    ]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample search rejects undeclared selected-candidate, least, minimal, complete, solver, search, or oracle assertions',
  );
});

test('MinCounterexample rejects a mutated terminal conclusion', () => {
  const fixture = makeFixture0();
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      {
        ...fixture.selectNode,
        Conclusion: {
          ...fixture.conclusion,
          selectedCandidateId: 'c1',
        },
      },
    ]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample conclusion must exactly equal the computed least-failing-candidate decision',
  );
});

test('MinCounterexample accepts only Record.intro evidence', () => {
  const fixture = makeFixture0();
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      {
        ...fixture.selectNode,
        Premises: [
          'judgment.c0.holds',
          fixture.evidenceProofIds[1],
          fixture.evidenceProofIds[2],
        ],
      },
    ]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample evidence premise must be accepted Record.intro evidence',
  );
});

test('predecessor rules cannot consume MinCounterexample conclusions without explicit semantics', () => {
  const fixture = makeFixture0();
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.minimum',
    RuleName: 'Eq',
    Premises: ['minimum.select'],
    Conclusion: fixture.candidates[0].holdsJudgment,
    Payload: { op: 'symm' },
  });
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([...fixture.proofNodes, illegal]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofMinCounterexample0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd sub-DAG rejected under the predecessor semantic checker',
  );
});

test('MinCounterexample readiness removes MinCounterexample but leaves four primitive families missing', () => {
  const out = CheckSemanticKernelReadinessMinCounterexample0();

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckSemanticKernelReadinessMinCounterexample0.coverage',
  );
  assert.equal(out.Witness.missingRules.includes('MinCounterexample'), false);
  assert.equal(out.Witness.missingRules.includes('IntArith'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 4);
});
