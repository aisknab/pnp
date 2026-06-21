import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplLedgerIndSuccessor0,
} from '../pcc-kimpl-ledgerind-successor0.mjs';

import {
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticOblTopoIndJudgment0,
  makeSemanticObligation0,
  makeSemanticObligationCreationEvidence0,
  makeSemanticObligationDischargeEvidence0,
  makeSemanticObligationPlan0,
  makeSemanticOblTopoIndCase0,
} from '../pcc-kernel-obltopoind-semantic0.mjs';

import {
  CheckKImplOblTopoIndFinalTheoremReadiness0,
  CheckKImplOblTopoIndSuccessor0,
  makeKImplOblTopoIndSuccessor0,
} from '../pcc-kimpl-obltopoind-successor0.mjs';

function judgment0(name) {
  const term = makeSemanticVar0(name, 'ObligationAtom');
  return makeSemanticEqJudgment0(term, term);
}

function eqProof0(id, conclusion) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Conclusion: conclusion,
    Payload: { op: 'refl' },
  });
}

function recordProof0(id, conclusion, premises) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Record',
    Premises: premises,
    Conclusion: conclusion,
    Payload: {
      op: 'intro',
      recordType: conclusion.recordType,
      fieldNames: conclusion.fields.map((field) => field.name),
    },
  });
}

function makeObligationProof0({ invalid = false } = {}) {
  const planId = 'successor.obligation.plan';
  const source = judgment0('source');
  const target = judgment0('target');
  const frontier = judgment0('frontier');
  const projection = judgment0('projection');
  const result = judgment0('result');
  const alternateResult = judgment0('alternateResult');
  const fullWitness = judgment0('fullWitness');
  const closed = judgment0('closed');

  const creation = makeSemanticObligationCreationEvidence0({
    planId,
    obligationId: 'o0',
    mode: 'Full',
    source,
    target,
    frontier,
    projection,
  });
  const discharge = makeSemanticObligationDischargeEvidence0({
    planId,
    obligationId: 'o0',
    mode: 'Full',
    rule: 'R6',
    result,
    fullWitness,
  });
  const alternateDischarge = makeSemanticObligationDischargeEvidence0({
    planId,
    obligationId: 'o0',
    mode: 'Full',
    rule: 'R6',
    result: alternateResult,
    fullWitness,
  });

  const obligation = makeSemanticObligation0({
    id: 'o0',
    mode: 'Full',
    dependencies: [],
    createIndex: 0,
    dischargeIndex: 1,
    dischargeRule: 'R6',
    creationEvidence: creation,
    dischargeEvidence: discharge,
  });
  const plan = makeSemanticObligationPlan0(planId, [obligation]);
  const caseRecord = makeSemanticOblTopoIndCase0({
    planId,
    obligationId: 'o0',
    creation,
    discharge: invalid ? alternateDischarge : discharge,
    closed,
  });
  const caseProofIds = ['case.o0'];
  const validCaseRecord = makeSemanticOblTopoIndCase0({
    planId,
    obligationId: 'o0',
    creation,
    discharge,
    closed,
  });
  const conclusion = deriveSemanticOblTopoIndJudgment0({
    plan,
    caseRecords: [validCaseRecord],
    caseProofIds,
  });

  return makeSemanticProofDAG0([
    eqProof0('source', source),
    eqProof0('target', target),
    eqProof0('frontier', frontier),
    eqProof0('projection', projection),
    eqProof0('result', result),
    eqProof0('alternateResult', alternateResult),
    eqProof0('fullWitness', fullWitness),
    eqProof0('closed', closed),
    recordProof0('creation.o0', creation, [
      'frontier',
      'projection',
      'source',
      'target',
    ]),
    recordProof0('discharge.o0', discharge, [
      'fullWitness',
      'result',
    ]),
    recordProof0('discharge.o0.alternate', alternateDischarge, [
      'fullWitness',
      'alternateResult',
    ]),
    recordProof0('case.o0', caseRecord, [
      'closed',
      'creation.o0',
      invalid ? 'discharge.o0.alternate' : 'discharge.o0',
    ]),
    makeSemanticProofNode0({
      id: 'obligations.close',
      RuleName: 'OblTopoInd',
      Premises: caseProofIds,
      Conclusion: conclusion,
      Payload: { op: 'close', plan },
    }),
  ]);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('OblTopoInd successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplOblTopoIndSuccessor0(
    makeKImplOblTopoIndSuccessor0({
      SemanticProofDAG: makeObligationProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplOblTopoIndSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticOblTopoIndNodeCount, 1);
  assert.equal(out.NF.semanticKernelReady, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.supportedSemanticRules, [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
    'OblTopoInd',
  ]);
  assert.equal(out.NF.missingSemanticRules.includes('OblTopoInd'), false);
  assert.equal(out.NF.missingSemanticRules.includes('TraceInd'), true);
  assert.equal(out.NF.missingSemanticRules.length, 10);
});

test('OblTopoInd successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplOblTopoIndSuccessor0(
    makeKImplOblTopoIndSuccessor0({
      SemanticProofDAG: makeObligationProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplOblTopoIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('OblTopoInd'), false);
  assert.equal(out.Witness.missingRules.length, 10);
});

test('OblTopoInd final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplOblTopoIndFinalTheoremReadiness0(
    makeKImplOblTopoIndSuccessor0({
      SemanticProofDAG: makeObligationProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplOblTopoIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd final-theorem readiness requires a final-theorem purpose record',
  );
});

test('OblTopoInd final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplOblTopoIndFinalTheoremReadiness0(
    makeKImplOblTopoIndSuccessor0({
      SemanticProofDAG: makeObligationProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplOblTopoIndFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('OblTopoInd successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplOblTopoIndSuccessor0({
    SemanticProofDAG: makeObligationProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplOblTopoIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd successor rejects caller-supplied semantic readiness assertions',
  );
});

test('OblTopoInd successor rejects a weakened release policy', async () => {
  const input = makeKImplOblTopoIndSuccessor0({
    SemanticProofDAG: makeObligationProof0(),
  });
  input.Policy.terminalNoOpenObligationsRequired = false;

  const out = await CheckKImplOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplOblTopoIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'OblTopoInd successor release policy must match the fail-closed policy',
  );
});

test('OblTopoInd successor rejects a stale LedgerInd-only child KImpl', async () => {
  const input = makeKImplOblTopoIndSuccessor0({
    SemanticProofDAG: makeObligationProof0(),
  });
  input.kind = makeKImplLedgerIndSuccessor0().kind;

  const out = await CheckKImplOblTopoIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplOblTopoIndSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd successor KImpl kind must be KImplSemanticOblTopoIndSuccessor0',
  );
});

test('OblTopoInd successor rejects invalid discharge linkage in development mode', async () => {
  const out = await CheckKImplOblTopoIndSuccessor0(
    makeKImplOblTopoIndSuccessor0({
      SemanticProofDAG: makeObligationProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplOblTopoIndSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'OblTopoInd case discharge evidence must exactly match the declared permitted discharge',
  );
});

test('OblTopoInd successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
  });

  const out = await CheckKImplOblTopoIndSuccessor0(
    makeKImplOblTopoIndSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeObligationProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplOblTopoIndSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
