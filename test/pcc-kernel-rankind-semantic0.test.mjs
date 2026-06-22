import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofRankInd0,
  CheckSemanticKernelReadinessRankInd0,
  deriveSemanticRankIndJudgment0,
  makeSemanticRank0,
  makeSemanticRankIndCase0,
  makeSemanticRankItem0,
  makeSemanticRankProgram0,
} from '../pcc-kernel-rankind-semantic0.mjs';

function eqProof0(id, conclusion) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Conclusion: conclusion,
    Payload: { op: 'refl' },
  });
}

function recordProof0(id, conclusion, proofByField) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Record',
    Premises: conclusion.fields.map((field) => proofByField[field.name]),
    Conclusion: conclusion,
    Payload: {
      op: 'intro',
      recordType: conclusion.recordType,
      fieldNames: conclusion.fields.map((field) => field.name),
    },
  });
}

function makeValidRankFixture0() {
  const programId = 'rank.descent';
  const terms = ['a0', 'a1', 'a2', 'a3']
    .map((name) => makeSemanticConst0(name, 'Term'));
  const invariants = terms.map((term) => makeSemanticEqJudgment0(term, term));

  const b0 = makeSemanticRankItem0({
    index: 0,
    id: 'b0',
    rank: makeSemanticRank0([0, 0]),
    invariant: invariants[0],
  });
  const b1 = makeSemanticRankItem0({
    index: 1,
    id: 'b1',
    rank: makeSemanticRank0([0, 0]),
    invariant: invariants[1],
  });
  const s0 = makeSemanticRankItem0({
    index: 2,
    id: 's0',
    rank: makeSemanticRank0([0, 1]),
    predecessorIds: ['b0', 'b1'],
    invariant: invariants[2],
  });
  const s1 = makeSemanticRankItem0({
    index: 3,
    id: 's1',
    rank: makeSemanticRank0([1, 0]),
    predecessorIds: ['s0'],
    invariant: invariants[3],
  });
  const items = [b0, b1, s0, s1];
  const byId = new Map(items.map((item) => [item.id, item]));
  const program = makeSemanticRankProgram0({
    programId,
    rankArity: 2,
    items,
    terminalItemId: 's1',
    terminalCoordinate: 'rank.output',
  });

  const proofNodes = [];
  const invariantProofIds = new Map();
  for (const item of items) {
    const proofId = `invariant.${item.id}`;
    proofNodes.push(eqProof0(proofId, item.invariant));
    invariantProofIds.set(item.id, proofId);
  }

  const caseRecords = [];
  const caseProofIds = [];
  for (const item of items) {
    const caseRecord = makeSemanticRankIndCase0({
      programId,
      itemId: item.id,
      invariant: item.invariant,
      dependencyInvariants: item.predecessorIds.map((predecessorId) => ({
        itemId: predecessorId,
        invariant: byId.get(predecessorId).invariant,
      })),
    });
    const proofByField = {
      invariant: invariantProofIds.get(item.id),
    };
    for (const predecessorId of item.predecessorIds) {
      proofByField[`dep.${predecessorId}`] = invariantProofIds.get(predecessorId);
    }
    const caseId = `case.${item.id}`;
    proofNodes.push(recordProof0(caseId, caseRecord, proofByField));
    caseRecords.push(caseRecord);
    caseProofIds.push(caseId);
  }

  const conclusion = deriveSemanticRankIndJudgment0({
    program,
    caseRecords,
    caseProofIds,
  });
  proofNodes.push(makeSemanticProofNode0({
    id: 'rank.close',
    RuleName: 'RankInd',
    Premises: caseProofIds,
    Conclusion: conclusion,
    Payload: { op: 'close', program },
  }));

  return {
    programId,
    terms,
    invariants,
    items,
    byId,
    program,
    proofNodes,
    invariantProofIds,
    caseRecords,
    caseProofIds,
    conclusion,
  };
}

test('RankInd closes exact zero-rank bases and strictly decreasing dependencies', () => {
  const fixture = makeValidRankFixture0();
  const out = CheckSemanticKernelProofRankInd0(
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
  ]);
  assert.equal(out.NF.rankIndNodeCount, 1);
  assert.equal(out.NF.missingRequiredRules.includes('RankInd'), false);
  assert.deepEqual(fixture.conclusion.itemOrder, ['b0', 'b1', 's0', 's1']);
  assert.deepEqual(fixture.conclusion.baseItemIds, ['b0', 'b1']);
  assert.deepEqual(fixture.conclusion.stepItemIds, ['s0', 's1']);
  assert.equal(fixture.conclusion.rankArity, 2);
  assert.equal(fixture.conclusion.terminalItemId, 's1');
  assert.equal(fixture.conclusion.terminalCoordinate, 'rank.output');
  assert.deepEqual(
    fixture.conclusion.terminalInvariant,
    fixture.byId.get('s1').invariant,
  );
  assert.equal(fixture.conclusion.canonicalRankOrder, true);
  assert.equal(fixture.conclusion.zeroRankBasePrefix, true);
  assert.equal(fixture.conclusion.strictRankDecrease, true);
  assert.equal(fixture.conclusion.localInvariantEvidenceExact, true);
  assert.equal(fixture.conclusion.allItemsContributeToTerminal, true);
});

test('RankInd rejects a base item with nonzero rank', () => {
  const fixture = makeValidRankFixture0();
  const badItems = fixture.items.map((item) => (
    item.id === 'b1'
      ? { ...item, rank: makeSemanticRank0([0, 1]) }
      : item
  ));
  const badProgram = { ...fixture.program, items: badItems };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'RankInd base items must have the exact zero rank');
});

test('RankInd rejects a step item with zero rank', () => {
  const fixture = makeValidRankFixture0();
  const badItems = fixture.items.map((item) => (
    item.id === 's0'
      ? { ...item, rank: makeSemanticRank0([0, 0]) }
      : item
  ));
  const badProgram = { ...fixture.program, items: badItems };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'RankInd step items must have a nonzero rank');
});

test('RankInd rejects noncanonical equal-rank item order', () => {
  const fixture = makeValidRankFixture0();
  const b0 = { ...fixture.byId.get('b0'), index: 1 };
  const b1 = { ...fixture.byId.get('b1'), index: 0 };
  const badProgram = {
    ...fixture.program,
    items: [b1, b0, fixture.byId.get('s0'), fixture.byId.get('s1')],
  };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'RankInd items must be in canonical lexicographic rank-then-id order',
  );
});

test('RankInd rejects a dependency with equal rank', () => {
  const fixture = makeValidRankFixture0();
  const badItems = fixture.items.map((item) => (
    item.id === 's1'
      ? { ...item, rank: makeSemanticRank0([0, 1]) }
      : item
  ));
  const badProgram = { ...fixture.program, items: badItems };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'RankInd every predecessor rank must be strictly smaller than the item rank',
  );
});

test('RankInd rejects a predecessor that is not an earlier item', () => {
  const fixture = makeValidRankFixture0();
  const badItems = fixture.items.map((item) => (
    item.id === 's0'
      ? { ...item, predecessorIds: ['s1'] }
      : item
  ));
  const badProgram = { ...fixture.program, items: badItems };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'RankInd predecessor must reference an earlier item');
});

test('RankInd rejects a local step case missing one predecessor invariant', () => {
  const fixture = makeValidRankFixture0();
  const s0 = fixture.byId.get('s0');
  const shortCase = makeSemanticRankIndCase0({
    programId: fixture.programId,
    itemId: 's0',
    invariant: s0.invariant,
    dependencyInvariants: [{
      itemId: 'b0',
      invariant: fixture.byId.get('b0').invariant,
    }],
  });
  const shortCaseNode = recordProof0('case.s0', shortCase, {
    invariant: fixture.invariantProofIds.get('s0'),
    'dep.b0': fixture.invariantProofIds.get('b0'),
  });
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0(
    fixture.proofNodes.map((node) => node.id === 'case.s0' ? shortCaseNode : node),
  ));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'RankInd case fields must contain the exact invariant and predecessor invariants',
  );
});

test('RankInd rejects a substituted predecessor invariant in a local case', () => {
  const fixture = makeValidRankFixture0();
  const s0 = fixture.byId.get('s0');
  const badCase = makeSemanticRankIndCase0({
    programId: fixture.programId,
    itemId: 's0',
    invariant: s0.invariant,
    dependencyInvariants: [
      { itemId: 'b0', invariant: fixture.byId.get('b1').invariant },
      { itemId: 'b1', invariant: fixture.byId.get('b1').invariant },
    ],
  });
  const alias = eqProof0(
    'invariant.b1.alias',
    fixture.byId.get('b1').invariant,
  );
  const badCaseNode = recordProof0('case.s0', badCase, {
    invariant: fixture.invariantProofIds.get('s0'),
    'dep.b0': 'invariant.b1.alias',
    'dep.b1': fixture.invariantProofIds.get('b1'),
  });
  const firstCaseIndex = fixture.proofNodes.findIndex((node) => node.id === 'case.b0');
  const nodes = [
    ...fixture.proofNodes.slice(0, firstCaseIndex),
    alias,
    ...fixture.proofNodes.slice(firstCaseIndex).map(
      (node) => node.id === 'case.s0' ? badCaseNode : node,
    ),
  ];
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'RankInd case fields must contain the exact invariant and predecessor invariants',
  );
});

test('RankInd rejects an item that does not contribute to the terminal item', () => {
  const fixture = makeValidRankFixture0();
  const badItems = fixture.items.map((item) => (
    item.id === 's0'
      ? { ...item, predecessorIds: ['b0'] }
      : item
  ));
  const badProgram = { ...fixture.program, items: badItems };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'RankInd every declared item must contribute to the terminal item',
  );
  assert.deepEqual(out.Witness.deadItemIds, ['b1']);
});

test('RankInd rejects caller-supplied well-foundedness assertions', () => {
  const fixture = makeValidRankFixture0();
  const badProgram = { ...fixture.program, wellFounded: true };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofRankInd0.shape');
  assert.equal(
    out.Witness.reason,
    'RankInd program rejects undeclared well-foundedness, rank-complete, induction-complete, or terminal-ready assertions',
  );
});

test('RankInd rejects local cases supplied out of item order', () => {
  const fixture = makeValidRankFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Premises: ['case.b1', 'case.b0', 'case.s0', 'case.s1'],
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'RankInd case recordType must bind the program and item id',
  );
});

test('RankInd rejects a mutated terminal conclusion', () => {
  const fixture = makeValidRankFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Conclusion: {
        ...fixture.conclusion,
        terminalCoordinate: 'wrong.output',
      },
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'RankInd conclusion must exactly equal the computed finite rank-induction closure',
  );
});

test('RankInd accepts only Record.intro local case evidence', () => {
  const fixture = makeValidRankFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Premises: [
        fixture.invariantProofIds.get('b0'),
        'case.b1',
        'case.s0',
        'case.s1',
      ],
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'RankInd case premise must be accepted Record.intro evidence',
  );
});

test('predecessor rules cannot consume RankInd conclusions without explicit semantics', () => {
  const fixture = makeValidRankFixture0();
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.rank',
    RuleName: 'Eq',
    Premises: ['rank.close'],
    Conclusion: fixture.invariants[0],
    Payload: { op: 'symm' },
  });
  const out = CheckSemanticKernelProofRankInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes,
    illegal,
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofRankInd0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall sub-DAG rejected under the predecessor semantic checker',
  );
});

test('RankInd readiness removes RankInd but leaves five primitive families missing', () => {
  const out = CheckSemanticKernelReadinessRankInd0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessRankInd0.coverage');
  assert.equal(out.Witness.missingRules.includes('RankInd'), false);
  assert.equal(out.Witness.missingRules.includes('MinCounterexample'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 5);
});
