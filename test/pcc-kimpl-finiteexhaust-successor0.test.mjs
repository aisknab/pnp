import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplTraceIndSuccessor0,
} from '../pcc-kimpl-traceind-successor0.mjs';

import {
  makeSemanticApp0,
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
  substituteSemanticJudgment0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticFiniteExhaustJudgment0,
  makeSemanticFiniteDomain0,
  makeSemanticFiniteExhaustCase0,
} from '../pcc-kernel-finiteexhaust-semantic0.mjs';

import {
  CheckKImplFiniteExhaustFinalTheoremReadiness0,
  CheckKImplFiniteExhaustSuccessor0,
  makeKImplFiniteExhaustSuccessor0,
} from '../pcc-kimpl-finiteexhaust-successor0.mjs';

function eqProof0(id, judgment) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Conclusion: judgment,
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

function makeFiniteProof0({ invalid = false } = {}) {
  const domainId = 'successor.bool.domain';
  const variable = makeSemanticVar0('x', 'Bool');
  const falseTerm = makeSemanticConst0('false', 'Bool');
  const trueTerm = makeSemanticConst0('true', 'Bool');
  const bodyTerm = makeSemanticApp0('probe', [variable], 'Bool');
  const body = makeSemanticEqJudgment0(bodyTerm, bodyTerm);
  const domain = makeSemanticFiniteDomain0({
    domainId,
    elementSort: 'Bool',
    elements: [falseTerm, trueTerm],
  });

  const proofNodes = [];
  const caseRecords = [];
  const caseProofIds = [];
  const instances = domain.elements.map((element) => (
    substituteSemanticJudgment0(body, variable, element)
  ));

  for (let index = 0; index < domain.elements.length; index += 1) {
    const element = domain.elements[index];
    const instance = invalid && index === 0 ? instances[1] : instances[index];
    const elementId = `element.${index}`;
    const instanceId = `instance.${index}`;
    const alternateId = `alternate.${index}`;
    const caseId = `case.${index}`;

    proofNodes.push(eqProof0(
      elementId,
      makeSemanticEqJudgment0(element, element),
    ));
    proofNodes.push(eqProof0(instanceId, instances[index]));
    if (invalid && index === 0) {
      proofNodes.push(eqProof0(alternateId, instances[1]));
    }

    const caseRecord = makeSemanticFiniteExhaustCase0({
      domainId,
      index,
      element,
      instance,
    });
    proofNodes.push(recordProof0(caseId, caseRecord, {
      element: elementId,
      instance: invalid && index === 0 ? alternateId : instanceId,
    }));
    caseRecords.push(caseRecord);
    caseProofIds.push(caseId);
  }

  const validCaseRecords = invalid
    ? caseRecords.map((record, index) => (
      index === 0
        ? makeSemanticFiniteExhaustCase0({
          domainId,
          index,
          element: domain.elements[index],
          instance: instances[index],
        })
        : record
    ))
    : caseRecords;
  const conclusion = deriveSemanticFiniteExhaustJudgment0({
    domain,
    variable,
    body,
    caseRecords: validCaseRecords,
    caseProofIds,
  });

  proofNodes.push(makeSemanticProofNode0({
    id: 'finite.close',
    RuleName: 'FiniteExhaust',
    Premises: caseProofIds,
    Conclusion: conclusion,
    Payload: { op: 'close', domain, variable, body },
  }));

  return makeSemanticProofDAG0(proofNodes);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('FiniteExhaust successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplFiniteExhaustSuccessor0(
    makeKImplFiniteExhaustSuccessor0({
      SemanticProofDAG: makeFiniteProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplFiniteExhaustSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticFiniteExhaustNodeCount, 1);
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
  ]);
  assert.equal(out.NF.missingSemanticRules.includes('FiniteExhaust'), false);
  assert.equal(out.NF.missingSemanticRules.includes('DPInd'), true);
  assert.equal(out.NF.missingSemanticRules.length, 8);
});

test('FiniteExhaust successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplFiniteExhaustSuccessor0(
    makeKImplFiniteExhaustSuccessor0({
      SemanticProofDAG: makeFiniteProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteExhaustSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteExhaust'), false);
  assert.equal(out.Witness.missingRules.length, 8);
});

test('FiniteExhaust final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplFiniteExhaustFinalTheoremReadiness0(
    makeKImplFiniteExhaustSuccessor0({
      SemanticProofDAG: makeFiniteProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplFiniteExhaustFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust final-theorem readiness requires a final-theorem purpose record',
  );
});

test('FiniteExhaust final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplFiniteExhaustFinalTheoremReadiness0(
    makeKImplFiniteExhaustSuccessor0({
      SemanticProofDAG: makeFiniteProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplFiniteExhaustFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('FiniteExhaust successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplFiniteExhaustSuccessor0({
    SemanticProofDAG: makeFiniteProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplFiniteExhaustSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteExhaustSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust successor rejects caller-supplied semantic readiness assertions',
  );
});

test('FiniteExhaust successor rejects a weakened release policy', async () => {
  const input = makeKImplFiniteExhaustSuccessor0({
    SemanticProofDAG: makeFiniteProof0(),
  });
  input.Policy.canonicalCompleteEnumerationRequired = false;

  const out = await CheckKImplFiniteExhaustSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteExhaustSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust successor release policy must match the fail-closed policy',
  );
});

test('FiniteExhaust successor rejects a stale TraceInd-only record', async () => {
  const input = makeKImplFiniteExhaustSuccessor0({
    SemanticProofDAG: makeFiniteProof0(),
  });
  input.kind = makeKImplTraceIndSuccessor0().kind;

  const out = await CheckKImplFiniteExhaustSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteExhaustSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust successor KImpl kind must be KImplSemanticFiniteExhaustSuccessor0',
  );
});

test('FiniteExhaust successor rejects invalid per-element instantiation in development mode', async () => {
  const out = await CheckKImplFiniteExhaustSuccessor0(
    makeKImplFiniteExhaustSuccessor0({
      SemanticProofDAG: makeFiniteProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteExhaustSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'FiniteExhaust case instance must exactly equal body substitution at the enumerated element',
  );
});

test('FiniteExhaust successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
  });

  const out = await CheckKImplFiniteExhaustSuccessor0(
    makeKImplFiniteExhaustSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeFiniteProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteExhaustSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
