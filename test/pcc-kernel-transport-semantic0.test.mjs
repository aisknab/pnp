import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofTransport0,
  CheckSemanticKernelReadinessTransport0,
  deriveSemanticTransportJudgment0,
  makeSemanticTransportCarrier0,
  makeSemanticTransportCoordinate0,
  makeSemanticTransportFactEvidence0,
  makeSemanticTransportMapEntry0,
  makeSemanticTransportSpec0,
} from '../pcc-kernel-transport-semantic0.mjs';

function eqJudgment0(name) {
  const term = makeSemanticConst0(name, 'Term');
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

function recordProof0(id, conclusion, premiseId) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Record',
    Premises: [premiseId],
    Conclusion: conclusion,
    Payload: {
      op: 'intro',
      recordType: conclusion.recordType,
      fieldNames: ['fact'],
    },
  });
}

function coordinate0(index, id, role) {
  return makeSemanticTransportCoordinate0({ index, id, role });
}

function map0(index, sourceCoordinateId, targetCoordinateId) {
  return makeSemanticTransportMapEntry0({
    index,
    sourceCoordinateId,
    targetCoordinateId,
  });
}

function makeEvidenceNodes0(carrier, prefix = carrier.carrierId) {
  const nodes = [];
  const records = [];
  const proofIds = [];
  for (const coordinate of carrier.coordinates) {
    const judgment = eqJudgment0(`${prefix}.${coordinate.id}`);
    const judgmentId = `judgment.${prefix}.${coordinate.index}`;
    const factId = `fact.${prefix}.${coordinate.index}`;
    const evidence = makeSemanticTransportFactEvidence0({
      carrierId: carrier.carrierId,
      coordinateId: coordinate.id,
      judgment,
    });
    nodes.push(eqProof0(judgmentId, judgment));
    nodes.push(recordProof0(factId, evidence, judgmentId));
    records.push(evidence);
    proofIds.push(factId);
  }
  return { nodes, records, proofIds };
}

function makeRenameFixture0() {
  const sourceCarrier = makeSemanticTransportCarrier0({
    carrierId: 'source.full',
    mode: 'full',
    coordinates: [
      coordinate0(0, 'source.in', 'boundary'),
      coordinate0(1, 'source.out', 'interface'),
    ],
  });
  const targetCarrier = makeSemanticTransportCarrier0({
    carrierId: 'target.full',
    mode: 'full',
    coordinates: [
      coordinate0(0, 'target.in', 'boundary'),
      coordinate0(1, 'target.out', 'interface'),
    ],
  });
  const spec = makeSemanticTransportSpec0({
    transportId: 'transport.rename.full',
    operation: 'rename',
    sourceCarrier,
    targetCarrier,
    mapping: [
      map0(0, 'source.in', 'target.in'),
      map0(1, 'source.out', 'target.out'),
    ],
  });
  const evidence = makeEvidenceNodes0(sourceCarrier, 'rename');
  const conclusion = deriveSemanticTransportJudgment0({
    spec,
    evidenceRecords: evidence.records,
    evidenceProofIds: evidence.proofIds,
  });
  const node = makeSemanticProofNode0({
    id: 'transport.rename',
    RuleName: 'Transport',
    Premises: evidence.proofIds,
    Conclusion: conclusion,
    Payload: { op: 'rename', spec },
  });
  return { sourceCarrier, targetCarrier, spec, evidence, conclusion, node };
}

function makeProjectionFixture0() {
  const sourceCarrier = makeSemanticTransportCarrier0({
    carrierId: 'carrier.full',
    mode: 'full',
    coordinates: [
      coordinate0(0, 'full.in', 'boundary'),
      coordinate0(1, 'full.hidden', 'profile'),
      coordinate0(2, 'full.out', 'interface'),
    ],
  });
  const targetCarrier = makeSemanticTransportCarrier0({
    carrierId: 'carrier.quotient',
    mode: 'quotient',
    coordinates: [
      coordinate0(0, 'quotient.in', 'boundary'),
      coordinate0(1, 'quotient.out', 'interface'),
    ],
  });
  const spec = makeSemanticTransportSpec0({
    transportId: 'transport.project.full',
    operation: 'project',
    sourceCarrier,
    targetCarrier,
    mapping: [
      map0(0, 'full.in', 'quotient.in'),
      map0(1, 'full.out', 'quotient.out'),
    ],
  });
  const evidence = makeEvidenceNodes0(sourceCarrier, 'project');
  const conclusion = deriveSemanticTransportJudgment0({
    spec,
    evidenceRecords: evidence.records,
    evidenceProofIds: evidence.proofIds,
  });
  const node = makeSemanticProofNode0({
    id: 'transport.project',
    RuleName: 'Transport',
    Premises: evidence.proofIds,
    Conclusion: conclusion,
    Payload: { op: 'project', spec },
  });
  return { sourceCarrier, targetCarrier, spec, evidence, conclusion, node };
}

function makeLiftFixture0() {
  const sourceCarrier = makeSemanticTransportCarrier0({
    carrierId: 'lift.quotient',
    mode: 'quotient',
    coordinates: [
      coordinate0(0, 'quotient.in', 'boundary'),
      coordinate0(1, 'quotient.out', 'interface'),
    ],
  });
  const targetCarrier = makeSemanticTransportCarrier0({
    carrierId: 'lift.full',
    mode: 'full',
    coordinates: [
      coordinate0(0, 'full.in', 'boundary'),
      coordinate0(1, 'full.lost', 'obligation'),
      coordinate0(2, 'full.out', 'interface'),
    ],
  });
  const spec = makeSemanticTransportSpec0({
    transportId: 'transport.lift.full',
    operation: 'lift',
    sourceCarrier,
    targetCarrier,
    mapping: [
      map0(0, 'quotient.in', 'full.in'),
      map0(1, 'quotient.out', 'full.out'),
    ],
  });
  const sourceEvidence = makeEvidenceNodes0(sourceCarrier, 'lift.source');
  const lostJudgment = eqJudgment0('lift.lost.obligation');
  const lostJudgmentId = 'judgment.lift.lost';
  const lostFactId = 'fact.lift.lost';
  const lostEvidence = makeSemanticTransportFactEvidence0({
    carrierId: targetCarrier.carrierId,
    coordinateId: 'full.lost',
    judgment: lostJudgment,
  });
  const nodes = [
    ...sourceEvidence.nodes,
    eqProof0(lostJudgmentId, lostJudgment),
    recordProof0(lostFactId, lostEvidence, lostJudgmentId),
  ];
  const records = [...sourceEvidence.records, lostEvidence];
  const proofIds = [...sourceEvidence.proofIds, lostFactId];
  const conclusion = deriveSemanticTransportJudgment0({
    spec,
    evidenceRecords: records,
    evidenceProofIds: proofIds,
  });
  const node = makeSemanticProofNode0({
    id: 'transport.lift',
    RuleName: 'Transport',
    Premises: proofIds,
    Conclusion: conclusion,
    Payload: { op: 'lift', spec },
  });
  return {
    sourceCarrier,
    targetCarrier,
    spec,
    sourceEvidence,
    lostJudgment,
    lostJudgmentId,
    lostFactId,
    lostEvidence,
    nodes,
    records,
    proofIds,
    conclusion,
    node,
  };
}

function check0(nodes) {
  return CheckSemanticKernelProofTransport0(makeSemanticProofDAG0(nodes));
}

test('Transport.rename carries exact accepted facts through an order-preserving same-mode bijection', () => {
  const fixture = makeRenameFixture0();
  const out = check0([...fixture.evidence.nodes, fixture.node]);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.transportNodeCount, 1);
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
    'MinCounterexample',
    'IntArith',
    'Transport',
  ]);
  assert.deepEqual(
    fixture.conclusion.targetFacts.map((fact) => fact.targetCoordinateId),
    ['target.in', 'target.out'],
  );
  assert.equal(fixture.conclusion.projectionComparisonOnly, false);
  assert.equal(fixture.conclusion.constructiveFullUseAllowed, true);
});

test('Transport.project computes lost coordinates and remains comparison-only', () => {
  const fixture = makeProjectionFixture0();
  const out = check0([...fixture.evidence.nodes, fixture.node]);

  assert.equal(out.tag, 'accept');
  assert.deepEqual(fixture.conclusion.lostSourceCoordinateIds, ['full.hidden']);
  assert.deepEqual(fixture.conclusion.liftedTargetCoordinateIds, []);
  assert.equal(fixture.conclusion.projectionComparisonOnly, true);
  assert.equal(fixture.conclusion.quotientResultCannotJustifyFullUse, true);
  assert.equal(fixture.conclusion.constructiveTargetUseAllowed, false);
  assert.equal(fixture.conclusion.constructiveFullUseAllowed, false);
});

test('Transport.lift requires accepted evidence for every full-only coordinate', () => {
  const fixture = makeLiftFixture0();
  const out = check0([...fixture.nodes, fixture.node]);

  assert.equal(out.tag, 'accept');
  assert.deepEqual(fixture.conclusion.lostSourceCoordinateIds, []);
  assert.deepEqual(fixture.conclusion.liftedTargetCoordinateIds, ['full.lost']);
  assert.deepEqual(fixture.conclusion.liftFactProofIds, ['fact.lift.lost']);
  assert.equal(fixture.conclusion.fullLiftEvidenceComplete, true);
  assert.equal(fixture.conclusion.constructiveTargetUseAllowed, true);
  assert.equal(fixture.conclusion.constructiveFullUseAllowed, true);
});

test('Transport rejects a role-changing coordinate map', () => {
  const fixture = makeRenameFixture0();
  const badTarget = {
    ...fixture.targetCarrier,
    coordinates: [
      { ...fixture.targetCarrier.coordinates[0], role: 'charge' },
      fixture.targetCarrier.coordinates[1],
    ],
  };
  const badSpec = { ...fixture.spec, targetCarrier: badTarget };
  const out = check0([
    ...fixture.evidence.nodes,
    { ...fixture.node, Payload: { op: 'rename', spec: badSpec } },
  ]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Transport mapping must preserve coordinate roles exactly',
  );
});

test('Transport rejects a non-order-preserving map', () => {
  const sourceCarrier = makeSemanticTransportCarrier0({
    carrierId: 'order.source',
    mode: 'full',
    coordinates: [
      coordinate0(0, 'source.a', 'payload'),
      coordinate0(1, 'source.b', 'payload'),
    ],
  });
  const targetCarrier = makeSemanticTransportCarrier0({
    carrierId: 'order.target',
    mode: 'full',
    coordinates: [
      coordinate0(0, 'target.a', 'payload'),
      coordinate0(1, 'target.b', 'payload'),
    ],
  });
  const evidence = makeEvidenceNodes0(sourceCarrier, 'order');
  const badSpec = {
    kind: 'SemanticTransportSpec0',
    version: 0,
    transportId: 'transport.order.bad',
    operation: 'rename',
    sourceCarrier,
    targetCarrier,
    mapping: [
      map0(0, 'source.a', 'target.b'),
      map0(1, 'source.b', 'target.a'),
    ],
  };
  const out = check0([
    ...evidence.nodes,
    makeSemanticProofNode0({
      id: 'transport.order.bad',
      RuleName: 'Transport',
      Premises: evidence.proofIds,
      Conclusion: makeRenameFixture0().conclusion,
      Payload: { op: 'rename', spec: badSpec },
    }),
  ]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Transport mapping must preserve source and target coordinate order',
  );
});

test('Transport rejects omission of a source fact', () => {
  const fixture = makeRenameFixture0();
  const out = check0([
    ...fixture.evidence.nodes,
    { ...fixture.node, Premises: [fixture.evidence.proofIds[0]] },
  ]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Transport premises must contain every source fact and every required lift fact exactly once',
  );
});

test('Transport rejects source evidence supplied out of carrier order', () => {
  const fixture = makeRenameFixture0();
  const out = check0([
    ...fixture.evidence.nodes,
    {
      ...fixture.node,
      Premises: [fixture.evidence.proofIds[1], fixture.evidence.proofIds[0]],
    },
  ]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Transport fact evidence must be the exact carrier-coordinate fact record',
  );
});

test('Transport.lift rejects omission of full-only evidence', () => {
  const fixture = makeLiftFixture0();
  const out = check0([
    ...fixture.nodes,
    { ...fixture.node, Premises: fixture.sourceEvidence.proofIds },
  ]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Transport premises must contain every source fact and every required lift fact exactly once',
  );
});

test('Transport.lift rejects evidence bound to the wrong carrier coordinate', () => {
  const fixture = makeLiftFixture0();
  const wrongEvidence = makeSemanticTransportFactEvidence0({
    carrierId: fixture.sourceCarrier.carrierId,
    coordinateId: fixture.sourceCarrier.coordinates[0].id,
    judgment: fixture.lostJudgment,
  });
  const wrongFact = recordProof0(
    fixture.lostFactId,
    wrongEvidence,
    fixture.lostJudgmentId,
  );
  const nodes = fixture.nodes.map(
    (node) => node.id === fixture.lostFactId ? wrongFact : node,
  );
  const out = check0([...nodes, fixture.node]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Transport fact evidence must be the exact carrier-coordinate fact record',
  );
});

test('Transport rejects project syntax for quotient-to-full movement', () => {
  const fixture = makeLiftFixture0();
  const badSpec = { ...fixture.spec, operation: 'project' };
  const out = check0([
    ...fixture.nodes,
    { ...fixture.node, Payload: { op: 'project', spec: badSpec } },
  ]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Transport project requires a full source and quotient target carrier',
  );
});

test('Transport rejects caller-supplied lift completion or preservation assertions', () => {
  const fixture = makeLiftFixture0();
  const out = check0([
    ...fixture.nodes,
    {
      ...fixture.node,
      Payload: {
        op: 'lift',
        spec: fixture.spec,
        fullLiftComplete: true,
        rolesPreserved: true,
      },
    },
  ]);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofTransport0.shape');
  assert.equal(
    out.Witness.reason,
    'Transport payload rejects caller-supplied target facts, lost coordinates, lift completion, preservation, full-use, solver, search, or oracle assertions',
  );
});

test('Transport rejects a mutated computed target conclusion', () => {
  const fixture = makeProjectionFixture0();
  const out = check0([
    ...fixture.evidence.nodes,
    {
      ...fixture.node,
      Conclusion: {
        ...fixture.conclusion,
        constructiveFullUseAllowed: true,
      },
    },
  ]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Transport conclusion must exactly equal the computed carrier transport decision',
  );
});

test('Transport accepts only Record.intro fact evidence', () => {
  const fixture = makeRenameFixture0();
  const eqIds = fixture.evidence.nodes
    .filter((node) => node.RuleName === 'Eq')
    .map((node) => node.id);
  const out = check0([
    ...fixture.evidence.nodes,
    { ...fixture.node, Premises: eqIds },
  ]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Transport fact evidence premise must be accepted Record.intro evidence',
  );
});

test('predecessor rules cannot consume Transport conclusions without explicit semantics', () => {
  const fixture = makeRenameFixture0();
  const term = makeSemanticConst0('after.transport', 'Term');
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.transport',
    RuleName: 'Eq',
    Premises: ['transport.rename'],
    Conclusion: makeSemanticEqJudgment0(term, term),
    Payload: { op: 'symm' },
  });
  const out = check0([...fixture.evidence.nodes, fixture.node, illegal]);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofTransport0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd/MinCounterexample/IntArith sub-DAG rejected under the predecessor semantic checker',
  );
});

test('Transport readiness removes Transport but leaves TruthVec and FiniteRel missing', () => {
  const out = CheckSemanticKernelReadinessTransport0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessTransport0.coverage');
  assert.equal(out.Witness.missingRules.includes('Transport'), false);
  assert.equal(out.Witness.missingRules.includes('TruthVec'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 2);
});
