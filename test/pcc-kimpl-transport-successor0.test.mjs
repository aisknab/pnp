import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplIntArithSuccessor0,
} from '../pcc-kimpl-intarith-successor0.mjs';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticTransportJudgment0,
  makeSemanticTransportCarrier0,
  makeSemanticTransportCoordinate0,
  makeSemanticTransportFactEvidence0,
  makeSemanticTransportMapEntry0,
  makeSemanticTransportSpec0,
} from '../pcc-kernel-transport-semantic0.mjs';

import {
  CheckKImplTransportFinalTheoremReadiness0,
  CheckKImplTransportSuccessor0,
  makeKImplTransportSuccessor0,
} from '../pcc-kimpl-transport-successor0.mjs';

function makeTransportProof0({ invalid = false } = {}) {
  const sourceCarrier = makeSemanticTransportCarrier0({
    carrierId: 'successor.source',
    mode: 'full',
    coordinates: [
      makeSemanticTransportCoordinate0({
        index: 0,
        id: 'source.coordinate',
        role: 'payload',
      }),
    ],
  });
  const targetCarrier = makeSemanticTransportCarrier0({
    carrierId: 'successor.target',
    mode: 'full',
    coordinates: [
      makeSemanticTransportCoordinate0({
        index: 0,
        id: 'target.coordinate',
        role: 'payload',
      }),
    ],
  });
  const spec = makeSemanticTransportSpec0({
    transportId: 'successor.transport',
    operation: 'rename',
    sourceCarrier,
    targetCarrier,
    mapping: [
      makeSemanticTransportMapEntry0({
        index: 0,
        sourceCoordinateId: 'source.coordinate',
        targetCoordinateId: 'target.coordinate',
      }),
    ],
  });
  const term = makeSemanticConst0('successor.fact', 'Term');
  const factJudgment = makeSemanticEqJudgment0(term, term);
  const evidence = makeSemanticTransportFactEvidence0({
    carrierId: sourceCarrier.carrierId,
    coordinateId: sourceCarrier.coordinates[0].id,
    judgment: factJudgment,
  });
  const proofId = 'fact.successor.source';
  const validConclusion = deriveSemanticTransportJudgment0({
    spec,
    evidenceRecords: [evidence],
    evidenceProofIds: [proofId],
  });
  const conclusion = invalid
    ? { ...validConclusion, constructiveFullUseAllowed: false }
    : validConclusion;
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'judgment.successor.fact',
      RuleName: 'Eq',
      Conclusion: factJudgment,
      Payload: { op: 'refl' },
    }),
    makeSemanticProofNode0({
      id: proofId,
      RuleName: 'Record',
      Premises: ['judgment.successor.fact'],
      Conclusion: evidence,
      Payload: {
        op: 'intro',
        recordType: evidence.recordType,
        fieldNames: ['fact'],
      },
    }),
    makeSemanticProofNode0({
      id: 'transport.successor',
      RuleName: 'Transport',
      Premises: [proofId],
      Conclusion: conclusion,
      Payload: { op: 'rename', spec },
    }),
  ]);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('Transport successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplTransportSuccessor0(
    makeKImplTransportSuccessor0({
      SemanticProofDAG: makeTransportProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplTransportSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticTransportNodeCount, 1);
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
    'IntArith',
    'Transport',
  ]);
  assert.equal(out.NF.missingSemanticRules.includes('Transport'), false);
  assert.equal(out.NF.missingSemanticRules.includes('TruthVec'), true);
  assert.equal(out.NF.missingSemanticRules.includes('FiniteRel'), true);
  assert.equal(out.NF.missingSemanticRules.length, 2);
});

test('Transport successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplTransportSuccessor0(
    makeKImplTransportSuccessor0({
      SemanticProofDAG: makeTransportProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTransportSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'Transport-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('Transport'), false);
  assert.equal(out.Witness.missingRules.length, 2);
});

test('Transport final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplTransportFinalTheoremReadiness0(
    makeKImplTransportSuccessor0({
      SemanticProofDAG: makeTransportProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplTransportFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'Transport final-theorem readiness requires a final-theorem purpose record',
  );
});

test('Transport final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplTransportFinalTheoremReadiness0(
    makeKImplTransportSuccessor0({
      SemanticProofDAG: makeTransportProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplTransportFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('TruthVec'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('Transport successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplTransportSuccessor0({
    SemanticProofDAG: makeTransportProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTransportSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'Transport successor rejects caller-supplied semantic readiness assertions',
  );
});

test('Transport successor rejects a weakened release policy', async () => {
  const input = makeKImplTransportSuccessor0({
    SemanticProofDAG: makeTransportProof0(),
  });
  input.Policy.projectionIsComparisonOnly = false;

  const out = await CheckKImplTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTransportSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'Transport successor release policy must match the fail-closed policy',
  );
});

test('Transport successor rejects a stale IntArith-only successor record', async () => {
  const input = makeKImplTransportSuccessor0({
    SemanticProofDAG: makeTransportProof0(),
  });
  input.kind = makeKImplIntArithSuccessor0().kind;

  const out = await CheckKImplTransportSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTransportSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'Transport successor KImpl kind must be KImplSemanticTransportSuccessor0',
  );
});

test('Transport successor rejects a mutated transport conclusion in development mode', async () => {
  const out = await CheckKImplTransportSuccessor0(
    makeKImplTransportSuccessor0({
      SemanticProofDAG: makeTransportProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTransportSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'Transport conclusion must exactly equal the computed carrier transport decision',
  );
});

test('Transport successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter(
      (rule) => rule.name !== 'TruthVec',
    ),
  });
  const out = await CheckKImplTransportSuccessor0(
    makeKImplTransportSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeTransportProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTransportSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
