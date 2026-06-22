import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplHallSuccessor0,
} from '../pcc-kimpl-hall-successor0.mjs';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticRankIndJudgment0,
  makeSemanticRank0,
  makeSemanticRankIndCase0,
  makeSemanticRankItem0,
  makeSemanticRankProgram0,
} from '../pcc-kernel-rankind-semantic0.mjs';

import {
  CheckKImplRankIndFinalTheoremReadiness0,
  CheckKImplRankIndSuccessor0,
  makeKImplRankIndSuccessor0,
} from '../pcc-kimpl-rankind-successor0.mjs';

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

function makeRankProof0({ invalid = false } = {}) {
  const programId = 'successor.rank';
  const baseTerm = makeSemanticConst0('base.term', 'Term');
  const stepTerm = makeSemanticConst0('step.term', 'Term');
  const baseInvariant = makeSemanticEqJudgment0(baseTerm, baseTerm);
  const stepInvariant = makeSemanticEqJudgment0(stepTerm, stepTerm);

  const b0 = makeSemanticRankItem0({
    index: 0,
    id: 'b0',
    rank: makeSemanticRank0([0]),
    invariant: baseInvariant,
  });
  const s0 = makeSemanticRankItem0({
    index: 1,
    id: 's0',
    rank: makeSemanticRank0([1]),
    predecessorIds: ['b0'],
    invariant: stepInvariant,
  });
  const program = makeSemanticRankProgram0({
    programId,
    rankArity: 1,
    items: [b0, s0],
    terminalItemId: 's0',
    terminalCoordinate: 'result',
  });

  const b0Case = makeSemanticRankIndCase0({
    programId,
    itemId: 'b0',
    invariant: baseInvariant,
  });
  const s0Case = makeSemanticRankIndCase0({
    programId,
    itemId: 's0',
    invariant: stepInvariant,
    dependencyInvariants: [{ itemId: 'b0', invariant: baseInvariant }],
  });
  const caseProofIds = ['case.b0', 'case.s0'];
  const validConclusion = deriveSemanticRankIndJudgment0({
    program,
    caseRecords: [b0Case, s0Case],
    caseProofIds,
  });
  const conclusion = invalid
    ? { ...validConclusion, terminalCoordinate: 'wrong.result' }
    : validConclusion;

  return makeSemanticProofDAG0([
    eqProof0('invariant.b0', baseInvariant),
    eqProof0('invariant.s0', stepInvariant),
    recordProof0('case.b0', b0Case, {
      invariant: 'invariant.b0',
    }),
    recordProof0('case.s0', s0Case, {
      'dep.b0': 'invariant.b0',
      invariant: 'invariant.s0',
    }),
    makeSemanticProofNode0({
      id: 'rank.close',
      RuleName: 'RankInd',
      Premises: caseProofIds,
      Conclusion: conclusion,
      Payload: { op: 'close', program },
    }),
  ]);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('RankInd successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplRankIndSuccessor0(
    makeKImplRankIndSuccessor0({
      SemanticProofDAG: makeRankProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplRankIndSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticRankIndNodeCount, 1);
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
  ]);
  assert.equal(out.NF.missingSemanticRules.includes('RankInd'), false);
  assert.equal(out.NF.missingSemanticRules.includes('MinCounterexample'), true);
  assert.equal(out.NF.missingSemanticRules.length, 5);
});

test('RankInd successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplRankIndSuccessor0(
    makeKImplRankIndSuccessor0({
      SemanticProofDAG: makeRankProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRankIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'RankInd-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('RankInd'), false);
  assert.equal(out.Witness.missingRules.length, 5);
});

test('RankInd final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplRankIndFinalTheoremReadiness0(
    makeKImplRankIndSuccessor0({
      SemanticProofDAG: makeRankProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplRankIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'RankInd final-theorem readiness requires a final-theorem purpose record',
  );
});

test('RankInd final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplRankIndFinalTheoremReadiness0(
    makeKImplRankIndSuccessor0({
      SemanticProofDAG: makeRankProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplRankIndFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('RankInd successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplRankIndSuccessor0({
    SemanticProofDAG: makeRankProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplRankIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRankIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'RankInd successor rejects caller-supplied semantic readiness assertions',
  );
});

test('RankInd successor rejects a weakened release policy', async () => {
  const input = makeKImplRankIndSuccessor0({
    SemanticProofDAG: makeRankProof0(),
  });
  input.Policy.strictRankDecreaseRequired = false;

  const out = await CheckKImplRankIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRankIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'RankInd successor release policy must match the fail-closed policy',
  );
});

test('RankInd successor rejects a stale Hall-only successor record', async () => {
  const input = makeKImplRankIndSuccessor0({
    SemanticProofDAG: makeRankProof0(),
  });
  input.kind = makeKImplHallSuccessor0().kind;

  const out = await CheckKImplRankIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRankIndSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'RankInd successor KImpl kind must be KImplSemanticRankIndSuccessor0',
  );
});

test('RankInd successor rejects a mutated terminal closure in development mode', async () => {
  const out = await CheckKImplRankIndSuccessor0(
    makeKImplRankIndSuccessor0({
      SemanticProofDAG: makeRankProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRankIndSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'RankInd conclusion must exactly equal the computed finite rank-induction closure',
  );
});

test('RankInd successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter(
      (rule) => rule.name !== 'MinCounterexample',
    ),
  });

  const out = await CheckKImplRankIndSuccessor0(
    makeKImplRankIndSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeRankProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRankIndSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
