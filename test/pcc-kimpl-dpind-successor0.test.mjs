import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplFiniteExhaustSuccessor0,
} from '../pcc-kimpl-finiteexhaust-successor0.mjs';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticDPIndJudgment0,
  makeSemanticDPBaseState0,
  makeSemanticDPIndCase0,
  makeSemanticDPProgram0,
  makeSemanticDPStepState0,
} from '../pcc-kernel-dpind-semantic0.mjs';

import {
  CheckKImplDPIndFinalTheoremReadiness0,
  CheckKImplDPIndSuccessor0,
  makeKImplDPIndSuccessor0,
} from '../pcc-kimpl-dpind-successor0.mjs';

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

function makeDPProof0({ invalid = false } = {}) {
  const programId = 'successor.dp';
  const seed = makeSemanticConst0('seed', 'Cost');
  const alternate = makeSemanticConst0('alternate', 'Cost');
  const b0 = makeSemanticDPBaseState0({
    index: 0,
    id: 'b0',
    baseTerm: seed,
  });
  const s0 = makeSemanticDPStepState0({
    index: 1,
    id: 's0',
    predecessorIds: ['b0'],
    predecessorValues: [b0.value],
    operator: 'extend',
    valueSort: 'Cost',
  });
  const program = makeSemanticDPProgram0({
    programId,
    valueSort: 'Cost',
    states: [b0, s0],
    terminalStateId: 's0',
    terminalCoordinate: 'result',
  });

  const b0Case = makeSemanticDPIndCase0({
    programId,
    stateId: 'b0',
    equation: b0.equation,
    value: b0.value,
  });
  const s0Case = makeSemanticDPIndCase0({
    programId,
    stateId: 's0',
    equation: s0.equation,
    value: s0.value,
    dependencyValues: [{
      stateId: 'b0',
      value: invalid ? alternate : b0.value,
    }],
  });
  const caseProofIds = ['case.b0', 'case.s0'];
  const validS0Case = makeSemanticDPIndCase0({
    programId,
    stateId: 's0',
    equation: s0.equation,
    value: s0.value,
    dependencyValues: [{ stateId: 'b0', value: b0.value }],
  });
  const conclusion = deriveSemanticDPIndJudgment0({
    program,
    caseRecords: [b0Case, validS0Case],
    caseProofIds,
  });

  return makeSemanticProofDAG0([
    eqProof0('equation.b0', b0.equation),
    eqProof0('value.b0', makeSemanticEqJudgment0(b0.value, b0.value)),
    eqProof0('equation.s0', s0.equation),
    eqProof0('value.s0', makeSemanticEqJudgment0(s0.value, s0.value)),
    eqProof0('value.alternate', makeSemanticEqJudgment0(alternate, alternate)),
    recordProof0('case.b0', b0Case, {
      equation: 'equation.b0',
      value: 'value.b0',
    }),
    recordProof0('case.s0', s0Case, {
      'dep.b0': invalid ? 'value.alternate' : 'value.b0',
      equation: 'equation.s0',
      value: 'value.s0',
    }),
    makeSemanticProofNode0({
      id: 'dp.close',
      RuleName: 'DPInd',
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

test('DPInd successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplDPIndSuccessor0(
    makeKImplDPIndSuccessor0({
      SemanticProofDAG: makeDPProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplDPIndSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticDPIndNodeCount, 1);
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
  ]);
  assert.equal(out.NF.missingSemanticRules.includes('DPInd'), false);
  assert.equal(out.NF.missingSemanticRules.includes('Hall'), true);
  assert.equal(out.NF.missingSemanticRules.length, 7);
});

test('DPInd successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplDPIndSuccessor0(
    makeKImplDPIndSuccessor0({
      SemanticProofDAG: makeDPProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDPIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'DPInd-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('DPInd'), false);
  assert.equal(out.Witness.missingRules.length, 7);
});

test('DPInd final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplDPIndFinalTheoremReadiness0(
    makeKImplDPIndSuccessor0({
      SemanticProofDAG: makeDPProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplDPIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'DPInd final-theorem readiness requires a final-theorem purpose record',
  );
});

test('DPInd final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplDPIndFinalTheoremReadiness0(
    makeKImplDPIndSuccessor0({
      SemanticProofDAG: makeDPProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplDPIndFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('DPInd successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplDPIndSuccessor0({
    SemanticProofDAG: makeDPProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplDPIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDPIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'DPInd successor rejects caller-supplied semantic readiness assertions',
  );
});

test('DPInd successor rejects a weakened release policy', async () => {
  const input = makeKImplDPIndSuccessor0({
    SemanticProofDAG: makeDPProof0(),
  });
  input.Policy.hiddenOptimizationForbidden = false;

  const out = await CheckKImplDPIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDPIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'DPInd successor release policy must match the fail-closed policy',
  );
});

test('DPInd successor rejects a stale FiniteExhaust-only successor record', async () => {
  const input = makeKImplDPIndSuccessor0({
    SemanticProofDAG: makeDPProof0(),
  });
  input.kind = makeKImplFiniteExhaustSuccessor0().kind;

  const out = await CheckKImplDPIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDPIndSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'DPInd successor KImpl kind must be KImplSemanticDPIndSuccessor0',
  );
});

test('DPInd successor rejects invalid predecessor-value linkage in development mode', async () => {
  const out = await CheckKImplDPIndSuccessor0(
    makeKImplDPIndSuccessor0({
      SemanticProofDAG: makeDPProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDPIndSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'DPInd predecessor value must exactly match the earlier evaluated state value',
  );
});

test('DPInd successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
  });

  const out = await CheckKImplDPIndSuccessor0(
    makeKImplDPIndSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeDPProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplDPIndSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
