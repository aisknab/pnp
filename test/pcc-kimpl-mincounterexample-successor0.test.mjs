import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplRankIndSuccessor0,
} from '../pcc-kimpl-rankind-successor0.mjs';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticMinCounterexampleJudgment0,
  makeSemanticMinCandidate0,
  makeSemanticMinCounterexampleEvidence0,
  makeSemanticMinCounterexampleSearch0,
} from '../pcc-kernel-mincounterexample-semantic0.mjs';

import {
  CheckKImplMinCounterexampleFinalTheoremReadiness0,
  CheckKImplMinCounterexampleSuccessor0,
  makeKImplMinCounterexampleSuccessor0,
} from '../pcc-kimpl-mincounterexample-successor0.mjs';

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

function makeMinCounterexampleProof0({ invalid = false } = {}) {
  const searchId = 'successor.minimum';
  const c0HoldsTerm = makeSemanticConst0('c0.holds', 'Term');
  const c0FailsTerm = makeSemanticConst0('c0.fails', 'Term');
  const c1HoldsTerm = makeSemanticConst0('c1.holds', 'Term');
  const c1FailsTerm = makeSemanticConst0('c1.fails', 'Term');
  const c0 = makeSemanticMinCandidate0({
    index: 0,
    id: 'c0',
    orderKey: 0,
    holdsJudgment: makeSemanticEqJudgment0(c0HoldsTerm, c0HoldsTerm),
    failsJudgment: makeSemanticEqJudgment0(c0FailsTerm, c0FailsTerm),
  });
  const c1 = makeSemanticMinCandidate0({
    index: 1,
    id: 'c1',
    orderKey: 1,
    holdsJudgment: makeSemanticEqJudgment0(c1HoldsTerm, c1HoldsTerm),
    failsJudgment: makeSemanticEqJudgment0(c1FailsTerm, c1FailsTerm),
  });
  const search = makeSemanticMinCounterexampleSearch0({
    searchId,
    candidates: [c0, c1],
    terminalCoordinate: 'result',
  });
  const c0Evidence = makeSemanticMinCounterexampleEvidence0({
    searchId,
    candidateId: 'c0',
    status: 'holds',
    judgment: c0.holdsJudgment,
  });
  const c1Evidence = makeSemanticMinCounterexampleEvidence0({
    searchId,
    candidateId: 'c1',
    status: 'fails',
    judgment: c1.failsJudgment,
  });
  const evidenceProofIds = ['case.c0.holds', 'case.c1.fails'];
  const validConclusion = deriveSemanticMinCounterexampleJudgment0({
    search,
    evidenceRecords: [c0Evidence, c1Evidence],
    evidenceProofIds,
  });
  const conclusion = invalid
    ? { ...validConclusion, selectedCandidateId: 'c0' }
    : validConclusion;

  return makeSemanticProofDAG0([
    eqProof0('judgment.c0.holds', c0.holdsJudgment),
    recordProof0('case.c0.holds', c0Evidence, 'judgment.c0.holds'),
    eqProof0('judgment.c1.fails', c1.failsJudgment),
    recordProof0('case.c1.fails', c1Evidence, 'judgment.c1.fails'),
    makeSemanticProofNode0({
      id: 'minimum.select',
      RuleName: 'MinCounterexample',
      Premises: evidenceProofIds,
      Conclusion: conclusion,
      Payload: { op: 'select', search },
    }),
  ]);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('MinCounterexample successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplMinCounterexampleSuccessor0(
    makeKImplMinCounterexampleSuccessor0({
      SemanticProofDAG: makeMinCounterexampleProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplMinCounterexampleSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticMinCounterexampleNodeCount, 1);
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
    'TraceInd',
    'FiniteExhaust',
    'DPInd',
    'Hall',
    'RankInd',
    'MinCounterexample',
  ]);
  assert.equal(
    out.NF.missingSemanticRules.includes('MinCounterexample'),
    false,
  );
  assert.equal(out.NF.missingSemanticRules.includes('IntArith'), true);
  assert.equal(out.NF.missingSemanticRules.length, 4);
});

test('MinCounterexample successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplMinCounterexampleSuccessor0(
    makeKImplMinCounterexampleSuccessor0({
      SemanticProofDAG: makeMinCounterexampleProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplMinCounterexampleSuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('MinCounterexample'), false);
  assert.equal(out.Witness.missingRules.length, 4);
});

test('MinCounterexample final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplMinCounterexampleFinalTheoremReadiness0(
    makeKImplMinCounterexampleSuccessor0({
      SemanticProofDAG: makeMinCounterexampleProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplMinCounterexampleFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample final-theorem readiness requires a final-theorem purpose record',
  );
});

test('MinCounterexample final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplMinCounterexampleFinalTheoremReadiness0(
    makeKImplMinCounterexampleSuccessor0({
      SemanticProofDAG: makeMinCounterexampleProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplMinCounterexampleFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('MinCounterexample successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplMinCounterexampleSuccessor0({
    SemanticProofDAG: makeMinCounterexampleProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplMinCounterexampleSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample successor rejects caller-supplied semantic readiness assertions',
  );
});

test('MinCounterexample successor rejects a weakened release policy', async () => {
  const input = makeKImplMinCounterexampleSuccessor0({
    SemanticProofDAG: makeMinCounterexampleProof0(),
  });
  input.Policy.firstFailureComputedFromEvidencePrefix = false;

  const out = await CheckKImplMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplMinCounterexampleSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'MinCounterexample successor release policy must match the fail-closed policy',
  );
});

test('MinCounterexample successor rejects a stale RankInd-only successor record', async () => {
  const input = makeKImplMinCounterexampleSuccessor0({
    SemanticProofDAG: makeMinCounterexampleProof0(),
  });
  input.kind = makeKImplRankIndSuccessor0().kind;

  const out = await CheckKImplMinCounterexampleSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplMinCounterexampleSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'MinCounterexample successor KImpl kind must be KImplSemanticMinCounterexampleSuccessor0',
  );
});

test('MinCounterexample successor rejects a mutated least-candidate conclusion in development mode', async () => {
  const out = await CheckKImplMinCounterexampleSuccessor0(
    makeKImplMinCounterexampleSuccessor0({
      SemanticProofDAG: makeMinCounterexampleProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplMinCounterexampleSuccessor0.semanticProof',
  );
  assert.equal(
    out.Witness.inner.witness.reason,
    'MinCounterexample conclusion must exactly equal the computed least-failing-candidate decision',
  );
});

test('MinCounterexample successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter(
      (rule) => rule.name !== 'IntArith',
    ),
  });

  const out = await CheckKImplMinCounterexampleSuccessor0(
    makeKImplMinCounterexampleSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeMinCounterexampleProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplMinCounterexampleSuccessor0.predecessorSuccessor',
  );
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
