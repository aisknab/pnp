import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofLedgerInd0,
  CheckSemanticKernelReadinessLedgerInd0,
  deriveSemanticLedgerIndJudgment0,
  makeSemanticLedger0,
  makeSemanticLedgerEntry0,
  makeSemanticLedgerIndCase0,
} from '../pcc-kernel-ledgerind-semantic0.mjs';

function reflexiveJudgment0(name) {
  const term = makeSemanticVar0(name, 'LedgerAtom');
  return makeSemanticEqJudgment0(term, term);
}

function eqProof0(id, judgment) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Conclusion: judgment,
    Payload: { op: 'refl' },
  });
}

function recordCaseNode0({
  id,
  ledgerId,
  entryId,
  entry,
  transition,
  current,
  previous = null,
  premiseIds,
}) {
  const fields = previous === null
    ? ['current', 'entry', 'transition']
    : ['current', 'entry', 'previous', 'transition'];

  return makeSemanticProofNode0({
    id,
    RuleName: 'Record',
    Premises: premiseIds,
    Conclusion: makeSemanticLedgerIndCase0({
      ledgerId,
      entryId,
      entry,
      transition,
      current,
      previous,
    }),
    Payload: {
      op: 'intro',
      recordType: `LedgerIndCase0.${ledgerId}.${entryId}`,
      fieldNames: fields,
    },
  });
}

function makeValidLedgerFixture0() {
  const ledgerId = 'charge.ledger';
  const entry0 = reflexiveJudgment0('entry0');
  const entry1 = reflexiveJudgment0('entry1');
  const entry2 = reflexiveJudgment0('entry2');
  const transition0 = reflexiveJudgment0('transition0');
  const transition1 = reflexiveJudgment0('transition1');
  const transition2 = reflexiveJudgment0('transition2');
  const state0 = reflexiveJudgment0('state0');
  const state1 = reflexiveJudgment0('state1');
  const state2 = reflexiveJudgment0('state2');

  const ledger = makeSemanticLedger0(ledgerId, [
    makeSemanticLedgerEntry0({
      index: 0,
      id: 'e0',
      entry: entry0,
      transition: transition0,
    }),
    makeSemanticLedgerEntry0({
      index: 1,
      id: 'e1',
      previousId: 'e0',
      entry: entry1,
      transition: transition1,
    }),
    makeSemanticLedgerEntry0({
      index: 2,
      id: 'e2',
      previousId: 'e1',
      entry: entry2,
      transition: transition2,
    }),
  ]);

  const case0 = makeSemanticLedgerIndCase0({
    ledgerId,
    entryId: 'e0',
    entry: entry0,
    transition: transition0,
    current: state0,
  });
  const case1 = makeSemanticLedgerIndCase0({
    ledgerId,
    entryId: 'e1',
    entry: entry1,
    transition: transition1,
    current: state1,
    previous: state0,
  });
  const case2 = makeSemanticLedgerIndCase0({
    ledgerId,
    entryId: 'e2',
    entry: entry2,
    transition: transition2,
    current: state2,
    previous: state1,
  });

  const caseProofIds = ['case.e0', 'case.e1', 'case.e2'];
  const conclusion = deriveSemanticLedgerIndJudgment0({
    ledger,
    caseRecords: [case0, case1, case2],
    caseProofIds,
  });

  const proofNodes = [
    eqProof0('entry.0', entry0),
    eqProof0('entry.1', entry1),
    eqProof0('entry.2', entry2),
    eqProof0('transition.0', transition0),
    eqProof0('transition.1', transition1),
    eqProof0('transition.2', transition2),
    eqProof0('state.0', state0),
    eqProof0('state.1', state1),
    eqProof0('state.2', state2),
    recordCaseNode0({
      id: 'case.e0',
      ledgerId,
      entryId: 'e0',
      entry: entry0,
      transition: transition0,
      current: state0,
      premiseIds: ['state.0', 'entry.0', 'transition.0'],
    }),
    recordCaseNode0({
      id: 'case.e1',
      ledgerId,
      entryId: 'e1',
      entry: entry1,
      transition: transition1,
      current: state1,
      previous: state0,
      premiseIds: ['state.1', 'entry.1', 'state.0', 'transition.1'],
    }),
    recordCaseNode0({
      id: 'case.e2',
      ledgerId,
      entryId: 'e2',
      entry: entry2,
      transition: transition2,
      current: state2,
      previous: state1,
      premiseIds: ['state.2', 'entry.2', 'state.1', 'transition.2'],
    }),
    makeSemanticProofNode0({
      id: 'ledger.close',
      RuleName: 'LedgerInd',
      Premises: caseProofIds,
      Conclusion: conclusion,
      Payload: { op: 'close', ledger },
    }),
  ];

  return {
    ledgerId,
    ledger,
    conclusion,
    caseProofIds,
    cases: { case0, case1, case2 },
    judgments: {
      entry0,
      entry1,
      entry2,
      transition0,
      transition1,
      transition2,
      state0,
      state1,
      state2,
    },
    proofNodes,
  };
}

test('LedgerInd closes an exact finite ledger from accepted local cases', () => {
  const fixture = makeValidLedgerFixture0();
  const out = CheckSemanticKernelProofLedgerInd0(
    makeSemanticProofDAG0(fixture.proofNodes),
  );

  assert.equal(out.tag, 'accept');
  assert.deepEqual(
    out.NF.supportedRules,
    ['Eq', 'Subst', 'Record', 'DAGInd', 'LedgerInd'],
  );
  assert.equal(out.NF.ledgerIndNodeCount, 1);
  assert.equal(out.NF.missingRequiredRules.includes('LedgerInd'), false);
  assert.deepEqual(fixture.conclusion.entryOrder, ['e0', 'e1', 'e2']);
  assert.equal(fixture.conclusion.baseEntryId, 'e0');
  assert.equal(fixture.conclusion.finalEntryId, 'e2');
  assert.deepEqual(
    fixture.conclusion.baseInvariant,
    fixture.judgments.state0,
  );
  assert.deepEqual(
    fixture.conclusion.finalInvariant,
    fixture.judgments.state2,
  );
  assert.equal(fixture.conclusion.allEntriesClosed, true);
});

test('LedgerInd rejects a previous invariant that differs from the immediately preceding state', () => {
  const fixture = makeValidLedgerFixture0();
  const badCase = recordCaseNode0({
    id: 'case.e1',
    ledgerId: fixture.ledgerId,
    entryId: 'e1',
    entry: fixture.judgments.entry1,
    transition: fixture.judgments.transition1,
    current: fixture.judgments.state1,
    previous: fixture.judgments.state2,
    premiseIds: ['state.1', 'entry.1', 'state.2', 'transition.1'],
  });
  const nodes = fixture.proofNodes.map(
    (node) => node.id === 'case.e1' ? badCase : node,
  );

  const out = CheckSemanticKernelProofLedgerInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'LedgerInd previous invariant must exactly match the immediately preceding closed invariant',
  );
});

test('LedgerInd rejects a non-base case that omits the previous invariant', () => {
  const fixture = makeValidLedgerFixture0();
  const shortCase = recordCaseNode0({
    id: 'case.e1',
    ledgerId: fixture.ledgerId,
    entryId: 'e1',
    entry: fixture.judgments.entry1,
    transition: fixture.judgments.transition1,
    current: fixture.judgments.state1,
    premiseIds: ['state.1', 'entry.1', 'transition.1'],
  });
  const nodes = fixture.proofNodes.map(
    (node) => node.id === 'case.e1' ? shortCase : node,
  );

  const out = CheckSemanticKernelProofLedgerInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'LedgerInd case fields must contain the exact entry, transition, current invariant, and prior invariant',
  );
});

test('LedgerInd rejects a case bound to the wrong declared entry judgment', () => {
  const fixture = makeValidLedgerFixture0();
  const badCase = recordCaseNode0({
    id: 'case.e1',
    ledgerId: fixture.ledgerId,
    entryId: 'e1',
    entry: fixture.judgments.entry2,
    transition: fixture.judgments.transition1,
    current: fixture.judgments.state1,
    previous: fixture.judgments.state0,
    premiseIds: ['state.1', 'entry.2', 'state.0', 'transition.1'],
  });
  const nodes = fixture.proofNodes.map(
    (node) => node.id === 'case.e1' ? badCase : node,
  );

  const out = CheckSemanticKernelProofLedgerInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'LedgerInd case entry judgment must exactly match the declared ledger entry',
  );
});

test('LedgerInd rejects a case bound to the wrong local transition judgment', () => {
  const fixture = makeValidLedgerFixture0();
  const badCase = recordCaseNode0({
    id: 'case.e1',
    ledgerId: fixture.ledgerId,
    entryId: 'e1',
    entry: fixture.judgments.entry1,
    transition: fixture.judgments.transition2,
    current: fixture.judgments.state1,
    previous: fixture.judgments.state0,
    premiseIds: ['state.1', 'entry.1', 'state.0', 'transition.2'],
  });
  const nodes = fixture.proofNodes.map(
    (node) => node.id === 'case.e1' ? badCase : node,
  );

  const out = CheckSemanticKernelProofLedgerInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'LedgerInd case transition judgment must exactly match the declared local transition',
  );
});

test('LedgerInd rejects a ledger whose previousId skips the immediate predecessor', () => {
  const fixture = makeValidLedgerFixture0();
  const badLedger = {
    ...fixture.ledger,
    entries: fixture.ledger.entries.map((entry) => (
      entry.id === 'e2' ? { ...entry, previousId: 'e0' } : entry
    )),
  };
  const closeNode = fixture.proofNodes.at(-1);
  const nodes = [
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', ledger: badLedger } },
  ];

  const out = CheckSemanticKernelProofLedgerInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofLedgerInd0.shape');
  assert.equal(
    out.Witness.reason,
    'LedgerInd previousId must name the immediately preceding ledger entry',
  );
});

test('LedgerInd rejects local case proofs supplied out of ledger order', () => {
  const fixture = makeValidLedgerFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const nodes = [
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Premises: ['case.e1', 'case.e0', 'case.e2'],
    },
  ];

  const out = CheckSemanticKernelProofLedgerInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'LedgerInd case recordType must bind the ledger and entry id',
  );
});

test('LedgerInd rejects a mutated final closure conclusion', () => {
  const fixture = makeValidLedgerFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const nodes = [
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Conclusion: {
        ...fixture.conclusion,
        finalEntryId: 'e1',
      },
    },
  ];

  const out = CheckSemanticKernelProofLedgerInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'LedgerInd conclusion must exactly equal the computed all-entry closure',
  );
});

test('LedgerInd accepts only Record.intro local case evidence', () => {
  const entry = reflexiveJudgment0('entry');
  const transition = reflexiveJudgment0('transition');
  const ledger = makeSemanticLedger0('single.ledger', [
    makeSemanticLedgerEntry0({
      index: 0,
      id: 'e0',
      entry,
      transition,
    }),
  ]);
  const fakeConclusion = {
    kind: 'SemanticLedgerIndJudgment0',
    version: 0,
    ledgerId: 'single.ledger',
    entryOrder: ['e0'],
    baseEntryId: 'e0',
    finalEntryId: 'e0',
    caseProofIds: ['entry.proof'],
    cases: [],
    baseInvariant: entry,
    finalInvariant: entry,
    allEntriesClosed: true,
  };

  const out = CheckSemanticKernelProofLedgerInd0(makeSemanticProofDAG0([
    eqProof0('entry.proof', entry),
    makeSemanticProofNode0({
      id: 'ledger.close',
      RuleName: 'LedgerInd',
      Premises: ['entry.proof'],
      Conclusion: fakeConclusion,
      Payload: { op: 'close', ledger },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'LedgerInd case premise must be accepted Record.intro evidence',
  );
});

test('predecessor rules cannot consume LedgerInd conclusions without explicit semantics', () => {
  const fixture = makeValidLedgerFixture0();
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.ledger',
    RuleName: 'Eq',
    Premises: ['ledger.close'],
    Conclusion: fixture.judgments.state0,
    Payload: { op: 'symm' },
  });

  const out = CheckSemanticKernelProofLedgerInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes,
    illegal,
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofLedgerInd0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd sub-DAG rejected under the predecessor semantic checker',
  );
});

test('LedgerInd readiness removes LedgerInd but leaves eleven rule families missing', () => {
  const out = CheckSemanticKernelReadinessLedgerInd0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessLedgerInd0.coverage');
  assert.equal(out.Witness.missingRules.includes('LedgerInd'), false);
  assert.equal(out.Witness.missingRules.includes('OblTopoInd'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 11);
});
