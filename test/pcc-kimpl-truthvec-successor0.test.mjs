import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplTransportSuccessor0,
} from '../pcc-kimpl-transport-successor0.mjs';

import {
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticTruthVecJudgment0,
  makeSemanticTruthVecInputNode0,
  makeSemanticTruthVecNANDNode0,
  makeSemanticTruthVecOutput0,
  makeSemanticTruthVecProgram0,
  makeSemanticTruthVecSpec0,
} from '../pcc-kernel-truthvec-semantic0.mjs';

import {
  CheckKImplTruthVecFinalTheoremReadiness0,
  CheckKImplTruthVecSuccessor0,
  makeKImplTruthVecSuccessor0,
} from '../pcc-kimpl-truthvec-successor0.mjs';

function makeTruthVecProof0({ invalid = false } = {}) {
  const program = makeSemanticTruthVecProgram0({
    programId: 'successor.truth.program',
    nodes: [
      makeSemanticTruthVecInputNode0({ index: 0, id: 'x' }),
      makeSemanticTruthVecInputNode0({ index: 1, id: 'y' }),
      makeSemanticTruthVecNANDNode0({
        index: 2,
        id: 'nand.xy',
        leftId: 'x',
        rightId: 'y',
      }),
    ],
    outputs: [
      makeSemanticTruthVecOutput0({
        index: 0,
        id: 'out.nand',
        nodeId: 'nand.xy',
      }),
    ],
  });
  const spec = makeSemanticTruthVecSpec0({
    evaluationId: 'successor.truth.eval',
    program,
  });
  const validConclusion = deriveSemanticTruthVecJudgment0({ spec });
  const conclusion = invalid
    ? {
        ...validConclusion,
        vectors: validConclusion.vectors.map((vector) => ({
          ...vector,
          bits: [false, ...vector.bits.slice(1)],
        })),
      }
    : validConclusion;

  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'truth.successor',
      RuleName: 'TruthVec',
      Conclusion: conclusion,
      Payload: { op: 'evaluate', spec },
    }),
  ]);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('TruthVec successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplTruthVecSuccessor0(
    makeKImplTruthVecSuccessor0({
      SemanticProofDAG: makeTruthVecProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplTruthVecSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticTruthVecNodeCount, 1);
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
    'TruthVec',
  ]);
  assert.deepEqual(out.NF.missingSemanticRules, ['FiniteRel']);
});

test('TruthVec successor rejects final-theorem purpose while FiniteRel is missing', async () => {
  const out = await CheckKImplTruthVecSuccessor0(
    makeKImplTruthVecSuccessor0({
      SemanticProofDAG: makeTruthVecProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTruthVecSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'TruthVec-extended successor KImpl is not ready for final-theorem use',
  );
  assert.deepEqual(out.Witness.missingRules, ['FiniteRel']);
});

test('TruthVec final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplTruthVecFinalTheoremReadiness0(
    makeKImplTruthVecSuccessor0({
      SemanticProofDAG: makeTruthVecProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplTruthVecFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'TruthVec final-theorem readiness requires a final-theorem purpose record',
  );
});

test('TruthVec final gate rejects explicit final use until FiniteRel exists', async () => {
  const out = await CheckKImplTruthVecFinalTheoremReadiness0(
    makeKImplTruthVecSuccessor0({
      SemanticProofDAG: makeTruthVecProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplTruthVecFinalTheoremReadiness0.semanticReadiness',
  );
  assert.deepEqual(out.Witness.missingRules, ['FiniteRel']);
});

test('TruthVec successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplTruthVecSuccessor0({
    SemanticProofDAG: makeTruthVecProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTruthVecSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'TruthVec successor rejects caller-supplied semantic readiness assertions',
  );
});

test('TruthVec successor rejects a weakened release policy', async () => {
  const input = makeKImplTruthVecSuccessor0({
    SemanticProofDAG: makeTruthVecProof0(),
  });
  input.Policy.everyOutputBitComputed = false;

  const out = await CheckKImplTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTruthVecSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'TruthVec successor release policy must match the fail-closed policy',
  );
});

test('TruthVec successor rejects a stale Transport-only successor record', async () => {
  const input = makeKImplTruthVecSuccessor0({
    SemanticProofDAG: makeTruthVecProof0(),
  });
  input.kind = makeKImplTransportSuccessor0().kind;

  const out = await CheckKImplTruthVecSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTruthVecSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'TruthVec successor KImpl kind must be KImplSemanticTruthVecSuccessor0',
  );
});

test('TruthVec successor rejects a mutated vector conclusion in development mode', async () => {
  const out = await CheckKImplTruthVecSuccessor0(
    makeKImplTruthVecSuccessor0({
      SemanticProofDAG: makeTruthVecProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTruthVecSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'TruthVec conclusion must exactly equal the computed ordered Boolean vectors',
  );
});

test('TruthVec successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter(
      (rule) => rule.name !== 'FiniteRel',
    ),
  });

  const out = await CheckKImplTruthVecSuccessor0(
    makeKImplTruthVecSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeTruthVecProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplTruthVecSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
