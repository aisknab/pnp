import assert from 'node:assert/strict';
import { test } from 'node:test';

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
  CheckSemanticKernelProofFiniteExhaust0,
  CheckSemanticKernelReadinessFiniteExhaust0,
  deriveSemanticFiniteExhaustJudgment0,
  makeSemanticFiniteDomain0,
  makeSemanticFiniteExhaustCase0,
} from '../pcc-kernel-finiteexhaust-semantic0.mjs';

function eqProof0(id, judgment, premises = [], op = 'refl') {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Premises: premises,
    Conclusion: judgment,
    Payload: { op },
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

function makeValidFixture0() {
  const domainId = 'bool.domain';
  const falseTerm = makeSemanticConst0('false', 'Bool');
  const trueTerm = makeSemanticConst0('true', 'Bool');
  const variable = makeSemanticVar0('x', 'Bool');
  const bodyTerm = makeSemanticApp0('probe', [variable], 'Bool');
  const body = makeSemanticEqJudgment0(bodyTerm, bodyTerm);
  const domain = makeSemanticFiniteDomain0({
    domainId,
    elementSort: 'Bool',
    elements: [trueTerm, falseTerm],
  });

  const proofNodes = [];
  const caseRecords = [];
  const caseProofIds = [];
  const elementProofIds = [];
  const instanceProofIds = [];
  const instances = [];

  for (let index = 0; index < domain.elements.length; index += 1) {
    const element = domain.elements[index];
    const instance = substituteSemanticJudgment0(body, variable, element);
    const elementProofId = `element.${index}`;
    const instanceProofId = `instance.${index}`;
    const caseProofId = `case.${index}`;
    const caseRecord = makeSemanticFiniteExhaustCase0({
      domainId,
      index,
      element,
      instance,
    });

    proofNodes.push(eqProof0(
      elementProofId,
      makeSemanticEqJudgment0(element, element),
    ));
    proofNodes.push(eqProof0(instanceProofId, instance));
    proofNodes.push(recordProof0(caseProofId, caseRecord, {
      element: elementProofId,
      instance: instanceProofId,
    }));

    caseRecords.push(caseRecord);
    caseProofIds.push(caseProofId);
    elementProofIds.push(elementProofId);
    instanceProofIds.push(instanceProofId);
    instances.push(instance);
  }

  const conclusion = deriveSemanticFiniteExhaustJudgment0({
    domain,
    variable,
    body,
    caseRecords,
    caseProofIds,
  });
  proofNodes.push(makeSemanticProofNode0({
    id: 'finite.close',
    RuleName: 'FiniteExhaust',
    Premises: caseProofIds,
    Conclusion: conclusion,
    Payload: {
      op: 'close',
      domain,
      variable,
      body,
    },
  }));

  return {
    domainId,
    domain,
    variable,
    body,
    caseRecords,
    caseProofIds,
    elementProofIds,
    instanceProofIds,
    instances,
    conclusion,
    proofNodes,
  };
}

test('FiniteExhaust computes an exact universal conclusion from every canonical domain case', () => {
  const fixture = makeValidFixture0();
  const out = CheckSemanticKernelProofFiniteExhaust0(
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
  ]);
  assert.equal(out.NF.finiteExhaustNodeCount, 1);
  assert.equal(out.NF.missingRequiredRules.includes('FiniteExhaust'), false);
  assert.equal(fixture.conclusion.cardinality, 2);
  assert.deepEqual(
    fixture.conclusion.universalJudgment.domain,
    fixture.domain.elements,
  );
  assert.equal(fixture.conclusion.canonicalEnumeration, true);
  assert.equal(fixture.conclusion.allElementsCovered, true);
  assert.equal(fixture.conclusion.noDuplicateElements, true);
  assert.equal(fixture.conclusion.noOmittedElements, true);
  assert.equal(fixture.conclusion.exactCardinality, true);
});

test('FiniteExhaust rejects duplicate domain elements', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const duplicateDomain = {
    ...fixture.domain,
    elements: [fixture.domain.elements[0], fixture.domain.elements[0]],
  };
  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { ...closeNode.Payload, domain: duplicateDomain } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofFiniteExhaust0.shape');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust domain enumeration must not contain duplicate elements',
  );
});

test('FiniteExhaust rejects a noncanonical enumeration order', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const reversedDomain = {
    ...fixture.domain,
    elements: [...fixture.domain.elements].reverse(),
  };
  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { ...closeNode.Payload, domain: reversedDomain } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust domain elements must be in canonical order',
  );
});

test('FiniteExhaust rejects a false cardinality assertion', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const badDomain = { ...fixture.domain, cardinality: 3 };
  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { ...closeNode.Payload, domain: badDomain } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust domain cardinality must exactly equal enumeration length',
  );
});

test('FiniteExhaust rejects caller-supplied domain completeness flags', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const assertedDomain = { ...fixture.domain, complete: true };
  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { ...closeNode.Payload, domain: assertedDomain } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust domain rejects undeclared completeness assertions',
  );
});

test('FiniteExhaust rejects an omitted per-element case', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Premises: closeNode.Premises.slice(0, -1) },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust requires exactly one accepted local case for every domain element',
  );
});

test('FiniteExhaust rejects cases supplied out of canonical domain order', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Premises: [...closeNode.Premises].reverse() },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust case recordType must bind the domain and canonical element index',
  );
});

test('FiniteExhaust rejects a case instantiated at the wrong element', () => {
  const fixture = makeValidFixture0();
  const wrongInstanceId = 'instance.wrong.0';
  const wrongCase = makeSemanticFiniteExhaustCase0({
    domainId: fixture.domainId,
    index: 0,
    element: fixture.domain.elements[0],
    instance: fixture.instances[1],
  });
  const wrongCaseNode = recordProof0('case.0', wrongCase, {
    element: fixture.elementProofIds[0],
    instance: wrongInstanceId,
  });
  const nodes = [];
  for (const node of fixture.proofNodes) {
    if (node.id === 'case.0') {
      nodes.push(eqProof0(wrongInstanceId, fixture.instances[1]));
      nodes.push(wrongCaseNode);
    } else {
      nodes.push(node);
    }
  }
  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust case instance must exactly equal body substitution at the enumerated element',
  );
});

test('FiniteExhaust rejects a mutated computed universal conclusion', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const badConclusion = {
    ...fixture.conclusion,
    universalJudgment: {
      ...fixture.conclusion.universalJudgment,
      domain: [...fixture.conclusion.elements].reverse(),
    },
  };
  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Conclusion: badConclusion },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust universal judgment must exactly bind the enumerated domain and body',
  );
});

test('FiniteExhaust accepts only Record.intro per-element case evidence', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Premises: [fixture.instanceProofIds[0], fixture.caseProofIds[1]],
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteExhaust case premise must be accepted Record.intro evidence',
  );
});

test('predecessor rules cannot consume FiniteExhaust conclusions without explicit semantics', () => {
  const fixture = makeValidFixture0();
  const illegal = eqProof0(
    'eq.after.finite',
    fixture.instances[0],
    ['finite.close'],
    'symm',
  );

  const out = CheckSemanticKernelProofFiniteExhaust0(makeSemanticProofDAG0([
    ...fixture.proofNodes,
    illegal,
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofFiniteExhaust0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd sub-DAG rejected under the predecessor semantic checker',
  );
});

test('FiniteExhaust readiness removes FiniteExhaust but leaves eight rule families missing', () => {
  const out = CheckSemanticKernelReadinessFiniteExhaust0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessFiniteExhaust0.coverage');
  assert.equal(out.Witness.missingRules.includes('FiniteExhaust'), false);
  assert.equal(out.Witness.missingRules.includes('DPInd'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 8);
});
