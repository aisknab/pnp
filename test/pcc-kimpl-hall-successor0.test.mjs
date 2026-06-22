import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplDPIndSuccessor0,
} from '../pcc-kimpl-dpind-successor0.mjs';

import {
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticHallJudgment0,
  makeSemanticHallEdge0,
  makeSemanticHallGraph0,
} from '../pcc-kernel-hall-semantic0.mjs';

import {
  CheckKImplHallFinalTheoremReadiness0,
  CheckKImplHallSuccessor0,
  makeKImplHallSuccessor0,
} from '../pcc-kimpl-hall-successor0.mjs';

function makeHallProof0({ invalid = false } = {}) {
  const graph = makeSemanticHallGraph0({
    graphId: 'successor.matching',
    leftVertexIds: ['l0', 'l1'],
    rightVertexIds: ['r0', 'r1'],
    edges: [
      makeSemanticHallEdge0({ leftId: 'l0', rightId: 'r0' }),
      makeSemanticHallEdge0({ leftId: 'l1', rightId: 'r1' }),
    ],
  });
  const validConclusion = deriveSemanticHallJudgment0({ graph });
  const conclusion = invalid
    ? { ...validConclusion, matchingSize: 1 }
    : validConclusion;

  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'hall.decide',
      RuleName: 'Hall',
      Conclusion: conclusion,
      Payload: { op: 'decide', graph },
    }),
  ]);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('Hall successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplHallSuccessor0(
    makeKImplHallSuccessor0({
      SemanticProofDAG: makeHallProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplHallSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticHallNodeCount, 1);
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
  ]);
  assert.equal(out.NF.missingSemanticRules.includes('Hall'), false);
  assert.equal(out.NF.missingSemanticRules.includes('RankInd'), true);
  assert.equal(out.NF.missingSemanticRules.length, 6);
});

test('Hall successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplHallSuccessor0(
    makeKImplHallSuccessor0({
      SemanticProofDAG: makeHallProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplHallSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'Hall-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('Hall'), false);
  assert.equal(out.Witness.missingRules.length, 6);
});

test('Hall final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplHallFinalTheoremReadiness0(
    makeKImplHallSuccessor0({
      SemanticProofDAG: makeHallProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplHallFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'Hall final-theorem readiness requires a final-theorem purpose record',
  );
});

test('Hall final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplHallFinalTheoremReadiness0(
    makeKImplHallSuccessor0({
      SemanticProofDAG: makeHallProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplHallFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('Hall successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplHallSuccessor0({
    SemanticProofDAG: makeHallProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplHallSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'Hall successor rejects caller-supplied semantic readiness assertions',
  );
});

test('Hall successor rejects a weakened release policy', async () => {
  const input = makeKImplHallSuccessor0({
    SemanticProofDAG: makeHallProof0(),
  });
  input.Policy.callerMatchingAndDeficiencyAssertionsForbidden = false;

  const out = await CheckKImplHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplHallSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'Hall successor release policy must match the fail-closed policy',
  );
});

test('Hall successor rejects a stale DPInd-only successor record', async () => {
  const input = makeKImplHallSuccessor0({
    SemanticProofDAG: makeHallProof0(),
  });
  input.kind = makeKImplDPIndSuccessor0().kind;

  const out = await CheckKImplHallSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplHallSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'Hall successor KImpl kind must be KImplSemanticHallSuccessor0',
  );
});

test('Hall successor rejects a mutated matching conclusion in development mode', async () => {
  const out = await CheckKImplHallSuccessor0(
    makeKImplHallSuccessor0({
      SemanticProofDAG: makeHallProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplHallSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'Hall conclusion must exactly equal the computed matching-or-deficiency decision',
  );
});

test('Hall successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'RankInd'),
  });

  const out = await CheckKImplHallSuccessor0(
    makeKImplHallSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeHallProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplHallSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
