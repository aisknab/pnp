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

function candidate0(id, index) {
  const holdsTerm = makeSemanticConst0(`${id}.holds`, 'Term');
  const failsTerm = makeSemanticConst0(`${id}.fails`, 'Term');
  return makeSemanticMinCandidate0({
    index,
    id,
    orderKey: index,
    holdsJudgment: makeSemanticEqJudgment0(holdsTerm, holdsTerm),
    failsJudgment: makeSemanticEqJudgment0(failsTerm, failsTerm),
  });
}

function evidence0(searchId, candidate, status) {
  return makeSemanticMinCounterexampleEvidence0({
    searchId,
    candidateId: candidate.id,
    status,
    judgment: status === 'holds'
      ? candidate.holdsJudgment
      : candidate.failsJudgment,
  });
}

function makeFixture0() {
  const searchId = 'minimum.counterexample';
  const candidates = [candidate0('c0', 0), candidate0('c1', 1), candidate0('c2', 2)];
  const search = makeSemanticMinCounterexampleSearch0({
    searchId,
    candidates,
    terminalCoordinate: 'minimum.output',
  });
  const specs = [
    { candidate: candidates[0], status: 'holds' },
    { candidate: candidates[1], status: 'holds' },
    { candidate: candidates[2], status: 'fails' },
  ];
  const proofNodes = [];
  const evidenceRecords = [];
  const evidenceProofIds = [];

  for (const spec of specs) {
    const judgment = spec.status === 'holds'
      ? spec.candidate.holdsJudgment
      : spec.candidate.failsJudgment;
    const judgmentId = `judgment.${spec.candidate.id}.${spec.status}`;
    const caseId = `case.${spec.candidate.id}.${spec.status}`;
    const evidence = evidence0(searchId, spec.candidate, spec.status);
    proofNodes.push(eqProof0(judgmentId, judgment));
    proofNodes.push(recordProof0(caseId, evidence, judgmentId));
    evidenceRecords.push(evidence);
    evidenceProofIds.push(caseId);
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
  assert.deepEqual(fixture.conclusion.candidateOrder, ['c0', 'c1', 'c2']);
  assert.deepEqual(fixture.conclusion.earlierCandidateIds, ['c0', 'c1']);
  assert.equal(fixture.conclusion.selectedCandidateId, 'c2');
  assert.equal(fixture.conclusion.selectedCandidateIndex, 2);
  assert.equal(fixture.conclusion.leastFailureComputed, true);
  assert.equal(fixture.conclusion.noSearchSolverOrOracleUsed, true);
});

test('MinCounterexample accepts failure at the first candidate', () => {
  const fixture = makeFixture0();
  const candidate = fixture.candidates[0];
  const evidence = evidence0(fixture.searchId, candidate, 'fails');
  const judgmentId = 'judgment.c0.fails.first';
  const caseId = 'case.c0.fails.first';
  const conclusion = deriveSemanticMinCounterexampleJudgment0({
    search: fixture.search,
    evidenceRecords: [evidence],
    evidenceProofIds: [caseId],
  });
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      eqProof0(judgmentId, candidate.failsJudgment),
      recordProof0(caseId, evidence, judgmentId),
      makeSemanticProofNode0({
        id: 'minimum.first',
        RuleName: 'MinCounterexample',
        Premises: [caseId],
        Conclusion: conclusion,
        Payload: { op: 'select', search: fixture.search },
      }),
    ]),
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
      { ...fixture.selectNode, Payload: { op: 'select', search: badSearch } },
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
  const badSearch = {
    ...fixture.search,
    candidates: [
      {
        ...fixture.candidates[0],
        failsJudgment: fixture.candidates[0].holdsJudgment,
      },
      ...fixture.candidates.slice(1),
    ],
  };
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      { ...fixture.selectNode, Payload: { op: 'select', search: badSearch } },
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

test('MinCounterexample rejects an all-holds domain with no failure evidence', () => {
  const fixture = makeFixture0();
  const c2 = fixture.candidates[2];
  const holds = evidence0(fixture.searchId, c2, 'holds');
  const nodes = fixture.proofNodes.slice(0, -1);
  nodes.push(eqProof0('judgment.c2.holds.all', c2.holdsJudgment));
  nodes.push(recordProof0('case.c2.holds.all', holds, 'judgment.c2.holds.all'));
  nodes.push({
    ...fixture.selectNode,
    Premises: [
      fixture.evidenceProofIds[0],
      fixture.evidenceProofIds[1],
      'case.c2.holds.all',
    ],
  });

  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0(nodes),
  );
  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample candidate domain contains no accepted failing candidate',
  );
});

test('MinCounterexample rejects evidence after the first failure', () => {
  const fixture = makeFixture0();
  const c1 = fixture.candidates[1];
  const c2 = fixture.candidates[2];
  const c1Fails = evidence0(fixture.searchId, c1, 'fails');
  const c2Holds = evidence0(fixture.searchId, c2, 'holds');
  const nodes = fixture.proofNodes.slice(0, -1);
  nodes.push(eqProof0('judgment.c1.fails.early', c1.failsJudgment));
  nodes.push(recordProof0('case.c1.fails.early', c1Fails, 'judgment.c1.fails.early'));
  nodes.push(eqProof0('judgment.c2.holds.after', c2.holdsJudgment));
  nodes.push(recordProof0('case.c2.holds.after', c2Holds, 'judgment.c2.holds.after'));
  nodes.push({
    ...fixture.selectNode,
    Premises: [
      fixture.evidenceProofIds[0],
      'case.c1.fails.early',
      'case.c2.holds.after',
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
  const aliasId = 'judgment.c1.holds.alias';
  const badEvidence = makeSemanticMinCounterexampleEvidence0({
    searchId: fixture.searchId,
    candidateId: 'c0',
    status: 'holds',
    judgment: fixture.candidates[1].holdsJudgment,
  });
  const badCase = recordProof0(
    fixture.evidenceProofIds[0],
    badEvidence,
    aliasId,
  );
  const nodes = [
    eqProof0(aliasId, fixture.candidates[1].holdsJudgment),
    ...fixture.proofNodes.map(
      (node) => node.id === fixture.evidenceProofIds[0] ? badCase : node,
    ),
  ];
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0(nodes),
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

test('MinCounterexample rejects a mutated terminal conclusion', () => {
  const fixture = makeFixture0();
  const out = CheckSemanticKernelProofMinCounterexample0(
    makeSemanticProofDAG0([
      ...fixture.proofNodes.slice(0, -1),
      {
        ...fixture.selectNode,
        Conclusion: { ...fixture.conclusion, selectedCandidateId: 'c1' },
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
