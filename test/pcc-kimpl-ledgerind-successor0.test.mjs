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
  deriveSemanticLedgerIndJudgment0,
  makeSemanticLedger0,
  makeSemanticLedgerEntry0,
  makeSemanticLedgerIndCase0,
} from '../pcc-kernel-ledgerind-semantic0.mjs';

import {
  CheckKImplLedgerIndFinalTheoremReadiness0,
  CheckKImplLedgerIndSuccessor0,
  makeKImplLedgerIndSuccessor0,
} from '../pcc-kimpl-ledgerind-successor0.mjs';

function reflexive0(name) {
  const term = makeSemanticVar0(name, 'LedgerAtom');
  return makeSemanticEqJudgment0(term, term);
}

function proof0(id, judgment) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Conclusion: judgment,
    Payload: { op: 'refl' },
  });
}

function makeLedgerProof0({ invalid = false } = {}) {
  const ledgerId = 'successor.ledger';
  const entry0 = reflexive0('entry0');
  const entry1 = reflexive0('entry1');
  const transition0 = reflexive0('transition0');
  const transition1 = reflexive0('transition1');
  const state0 = reflexive0('state0');
  const state1 = reflexive0('state1');

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
    previous: invalid ? state1 : state0,
  });

  const caseProofIds = ['case.e0', 'case.e1'];
  const validCase1 = makeSemanticLedgerIndCase0({
    ledgerId,
    entryId: 'e1',
    entry: entry1,
    transition: transition1,
    current: state1,
    previous: state0,
  });
  const conclusion = deriveSemanticLedgerIndJudgment0({
    ledger,
    caseRecords: [case0, validCase1],
    caseProofIds,
  });

  return makeSemanticProofDAG0([
    proof0('entry.0', entry0),
    proof0('entry.1', entry1),
    proof0('transition.0', transition0),
    proof0('transition.1', transition1),
    proof0('state.0', state0),
    proof0('state.1', state1),
    proof0('state.1.copy', state1),
    makeSemanticProofNode0({
      id: 'case.e0',
      RuleName: 'Record',
      Premises: ['state.0', 'entry.0', 'transition.0'],
      Conclusion: case0,
      Payload: {
        op: 'intro',
        recordType: `LedgerIndCase0.${ledgerId}.e0`,
        fieldNames: ['current', 'entry', 'transition'],
      },
    }),
    makeSemanticProofNode0({
      id: 'case.e1',
      RuleName: 'Record',
      Premises: invalid
        ? ['state.1', 'entry.1', 'state.1.copy', 'transition.1']
        : ['state.1', 'entry.1', 'state.0', 'transition.1'],
      Conclusion: case1,
      Payload: {
        op: 'intro',
        recordType: `LedgerIndCase0.${ledgerId}.e1`,
        fieldNames: ['current', 'entry', 'previous', 'transition'],
      },
    }),
    makeSemanticProofNode0({
      id: 'ledger.close',
      RuleName: 'LedgerInd',
      Premises: caseProofIds,
      Conclusion: conclusion,
      Payload: { op: 'close', ledger },
    }),
  ]);
}

test('LedgerInd successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplLedgerIndSuccessor0(
    makeKImplLedgerIndSuccessor0({
      SemanticProofDAG: makeLedgerProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplLedgerIndSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticLedgerIndNodeCount, 1);
  assert.equal(out.NF.semanticKernelReady, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.supportedSemanticRules.includes('LedgerInd'), true);
  assert.equal(out.NF.missingSemanticRules.includes('LedgerInd'), false);
  assert.equal(out.NF.missingSemanticRules.includes('OblTopoInd'), true);
  assert.equal(out.NF.missingSemanticRules.length, 11);
});

test('LedgerInd successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplLedgerIndSuccessor0(
    makeKImplLedgerIndSuccessor0({
      SemanticProofDAG: makeLedgerProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplLedgerIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('LedgerInd'), false);
  assert.equal(out.Witness.missingRules.length, 11);
});

test('LedgerInd final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplLedgerIndFinalTheoremReadiness0(
    makeKImplLedgerIndSuccessor0({
      SemanticProofDAG: makeLedgerProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplLedgerIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd final-theorem readiness requires a final-theorem purpose record',
  );
});

test('LedgerInd final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplLedgerIndFinalTheoremReadiness0(
    makeKImplLedgerIndSuccessor0({
      SemanticProofDAG: makeLedgerProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplLedgerIndFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('LedgerInd successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplLedgerIndSuccessor0({
    SemanticProofDAG: makeLedgerProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplLedgerIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd successor rejects caller-supplied semantic readiness assertions',
  );
});

test('LedgerInd successor rejects a weakened release policy', async () => {
  const input = makeKImplLedgerIndSuccessor0({
    SemanticProofDAG: makeLedgerProof0(),
  });
  input.Policy.localTransitionJudgmentsMustBeAccepted = false;

  const out = await CheckKImplLedgerIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplLedgerIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'LedgerInd successor release policy must match the fail-closed policy',
  );
});

test('LedgerInd successor rejects an invalid previous-state case in development mode', async () => {
  const out = await CheckKImplLedgerIndSuccessor0(
    makeKImplLedgerIndSuccessor0({
      SemanticProofDAG: makeLedgerProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplLedgerIndSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'LedgerInd previous invariant must exactly match the immediately preceding closed invariant',
  );
});

test('LedgerInd successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
  });

  const out = await CheckKImplLedgerIndSuccessor0(
    makeKImplLedgerIndSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeLedgerProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplLedgerIndSuccessor0.predecessorSuccessor');
  assert.equal(
    out.Witness.inner.witness.inner.witness.inner.witness.inner.witness.reason,
    'kernel rule table is missing a primitive rule',
  );
});
