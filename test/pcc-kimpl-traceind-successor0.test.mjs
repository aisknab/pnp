import assert from 'node:assert/strict';
import { test } from 'node:test';

import './pcc-kbundle-traceind-successor0.test.mjs';
import './pcc-global-proof-dag-traceind-successor0.test.mjs';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplOblTopoIndSuccessor0,
} from '../pcc-kimpl-obltopoind-successor0.mjs';

import {
  makeSemanticApp0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticTraceIndJudgment0,
  makeSemanticTrace0,
  makeSemanticTraceIndCase0,
  makeSemanticTraceNANDNode0,
  makeSemanticTraceSourceNode0,
} from '../pcc-kernel-traceind-semantic0.mjs';

import {
  CheckKImplTraceIndFinalTheoremReadiness0,
  CheckKImplTraceIndSuccessor0,
  makeKImplTraceIndSuccessor0,
} from '../pcc-kimpl-traceind-successor0.mjs';

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

function makeTraceProof0({ invalid = false } = {}) {
  const traceId = 'successor.trace';
  const x0 = makeSemanticVar0('x0', 'Bool');
  const x1 = makeSemanticVar0('x1', 'Bool');
  const s0 = makeSemanticTraceSourceNode0({
    index: 0,
    id: 's0',
    sourceCoordinate: 'x0',
    sourceTerm: x0,
  });
  const s1 = makeSemanticTraceSourceNode0({
    index: 1,
    id: 's1',
    sourceCoordinate: 'x1',
    sourceTerm: x1,
  });
  const g0 = makeSemanticTraceNANDNode0({
    index: 2,
    id: 'g0',
    leftId: 's0',
    rightId: 's1',
    leftTerm: s0.valueTerm,
    rightTerm: s1.valueTerm,
  });

  const traceNodes = [s0, s1, g0];
  const trace = makeSemanticTrace0({
    traceId,
    nodes: traceNodes,
    outputNodeId: 'g0',
    outputCoordinate: 'yout',
  });

  const proofNodes = [];
  const equationProofIds = new Map();
  const invariantProofIds = new Map();
  for (const node of traceNodes) {
    const equationId = `equation.${node.id}`;
    const invariantId = `invariant.${node.id}`;
    proofNodes.push(eqProof0(equationId, node.equation));
    proofNodes.push(eqProof0(invariantId, node.invariant));
    equationProofIds.set(node.id, equationId);
    invariantProofIds.set(node.id, invariantId);
  }

  const caseRecords = [];
  const caseProofIds = [];
  for (const node of traceNodes) {
    const dependencyIds = [...new Set(node.inputIds)];
    let equation = node.equation;
    let equationProofId = equationProofIds.get(node.id);
    if (invalid && node.id === 'g0') {
      const wrongTerm = makeSemanticApp0('nand', [x1, x0], 'Bool');
      equation = makeSemanticEqJudgment0(wrongTerm, wrongTerm);
      equationProofId = 'equation.g0.wrong';
      proofNodes.push(eqProof0(equationProofId, equation));
    }

    const caseRecord = makeSemanticTraceIndCase0({
      traceId,
      nodeId: node.id,
      equation,
      current: node.invariant,
      dependencyInvariants: dependencyIds.map((dependencyId) => ({
        nodeId: dependencyId,
        invariant: traceNodes.find((entry) => entry.id === dependencyId).invariant,
      })),
    });
    const caseId = `case.${node.id}`;
    const proofByField = {
      current: invariantProofIds.get(node.id),
      equation: equationProofId,
    };
    for (const dependencyId of dependencyIds) {
      proofByField[`dep.${dependencyId}`] = invariantProofIds.get(dependencyId);
    }
    proofNodes.push(recordProof0(caseId, caseRecord, proofByField));
    caseRecords.push(caseRecord);
    caseProofIds.push(caseId);
  }

  const validCaseRecords = invalid
    ? caseRecords.map((record, index) => (
      index === 2
        ? makeSemanticTraceIndCase0({
          traceId,
          nodeId: 'g0',
          equation: g0.equation,
          current: g0.invariant,
          dependencyInvariants: [
            { nodeId: 's0', invariant: s0.invariant },
            { nodeId: 's1', invariant: s1.invariant },
          ],
        })
        : record
    ))
    : caseRecords;
  const conclusion = deriveSemanticTraceIndJudgment0({
    trace,
    caseRecords: validCaseRecords,
    caseProofIds,
  });

  proofNodes.push(makeSemanticProofNode0({
    id: 'trace.close',
    RuleName: 'TraceInd',
    Premises: caseProofIds,
    Conclusion: conclusion,
    Payload: { op: 'close', trace },
  }));

  return makeSemanticProofDAG0(proofNodes);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('TraceInd successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplTraceIndSuccessor0(
    makeKImplTraceIndSuccessor0({
      SemanticProofDAG: makeTraceProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplTraceIndSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticTraceIndNodeCount, 1);
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
  ]);
  assert.equal(out.NF.missingSemanticRules.includes('TraceInd'), false);
  assert.equal(out.NF.missingSemanticRules.includes('FiniteExhaust'), true);
  assert.equal(out.NF.missingSemanticRules.length, 9);
});

test('TraceInd successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplTraceIndSuccessor0(
    makeKImplTraceIndSuccessor0({
      SemanticProofDAG: makeTraceProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTraceIndSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'TraceInd-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('TraceInd'), false);
  assert.equal(out.Witness.missingRules.length, 9);
});

test('TraceInd final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplTraceIndFinalTheoremReadiness0(
    makeKImplTraceIndSuccessor0({
      SemanticProofDAG: makeTraceProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplTraceIndFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'TraceInd final-theorem readiness requires a final-theorem purpose record',
  );
});

test('TraceInd final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplTraceIndFinalTheoremReadiness0(
    makeKImplTraceIndSuccessor0({
      SemanticProofDAG: makeTraceProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplTraceIndFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('TraceInd successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplTraceIndSuccessor0({
    SemanticProofDAG: makeTraceProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplTraceIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTraceIndSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'TraceInd successor rejects caller-supplied semantic readiness assertions',
  );
});

test('TraceInd successor rejects a weakened release policy', async () => {
  const input = makeKImplTraceIndSuccessor0({
    SemanticProofDAG: makeTraceProof0(),
  });
  input.Policy.outputCoordinateIdentityRequired = false;

  const out = await CheckKImplTraceIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTraceIndSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'TraceInd successor release policy must match the fail-closed policy',
  );
});

test('TraceInd successor rejects a stale OblTopoInd-only record', async () => {
  const input = makeKImplTraceIndSuccessor0({
    SemanticProofDAG: makeTraceProof0(),
  });
  input.kind = makeKImplOblTopoIndSuccessor0().kind;

  const out = await CheckKImplTraceIndSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTraceIndSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'TraceInd successor KImpl kind must be KImplSemanticTraceIndSuccessor0',
  );
});

test('TraceInd successor rejects invalid local equation linkage in development mode', async () => {
  const out = await CheckKImplTraceIndSuccessor0(
    makeKImplTraceIndSuccessor0({
      SemanticProofDAG: makeTraceProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTraceIndSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'TraceInd case equation must exactly match the declared source or NAND equation',
  );
});

test('TraceInd successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
  });

  const out = await CheckKImplTraceIndSuccessor0(
    makeKImplTraceIndSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeTraceProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTraceIndSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
