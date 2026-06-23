import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplTruthVecSuccessor0,
} from '../pcc-kimpl-truthvec-successor0.mjs';

import {
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticFiniteRelJudgment0,
  makeSemanticFiniteRelClaim0,
  makeSemanticFiniteRelDomain0,
  makeSemanticFiniteRelNode0,
  makeSemanticFiniteRelProgram0,
  makeSemanticFiniteRelSpec0,
  makeSemanticFiniteRelTuple0,
} from '../pcc-kernel-finiterel-semantic0.mjs';

import {
  CheckKImplFiniteRelFinalTheoremReadiness0,
  CheckKImplFiniteRelSuccessor0,
  makeKImplFiniteRelSuccessor0,
} from '../pcc-kimpl-finiterel-successor0.mjs';

function tuple0(index, values) {
  return makeSemanticFiniteRelTuple0({ index, values });
}

function literal0(index, id, domainIds, tupleValues) {
  return makeSemanticFiniteRelNode0({
    index,
    id,
    op: 'literal',
    domainIds,
    tuples: tupleValues.map((values, tupleIndex) => tuple0(tupleIndex, values)),
  });
}

function makeFiniteRelProof0({ invalid = false } = {}) {
  const domain = makeSemanticFiniteRelDomain0({
    index: 0,
    id: 'D',
    elements: ['a', 'b'],
  });
  const nodes = [
    literal0(0, 'R', ['D', 'D'], [['a', 'b']]),
    makeSemanticFiniteRelNode0({
      index: 1,
      id: 'R.rtc',
      op: 'reflexive-transitive-closure',
      domainIds: ['D', 'D'],
      inputIds: ['R'],
    }),
  ];
  const claims = [
    makeSemanticFiniteRelClaim0({
      index: 0,
      id: 'claim.R.in.rtc',
      claimKind: 'included',
      leftId: 'R',
      rightId: 'R.rtc',
    }),
    makeSemanticFiniteRelClaim0({
      index: 1,
      id: 'claim.rtc.closed',
      claimKind: 'reflexive-transitive-closed',
      leftId: 'R.rtc',
    }),
  ];
  const program = makeSemanticFiniteRelProgram0({
    programId: 'successor.finiterel.program',
    domains: [domain],
    nodes,
    claims,
  });
  const spec = makeSemanticFiniteRelSpec0({
    evaluationId: 'successor.finiterel.eval',
    program,
  });
  const validConclusion = deriveSemanticFiniteRelJudgment0({ spec });
  const conclusion = invalid
    ? {
        ...validConclusion,
        relations: validConclusion.relations.map((relation) => (
          relation.nodeId === 'R.rtc'
            ? { ...relation, tuples: relation.tuples.slice(0, 2) }
            : relation
        )),
      }
    : validConclusion;

  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.successor',
      RuleName: 'FiniteRel',
      Conclusion: conclusion,
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('FiniteRel successor accepts complete primitive coverage as development-only by default', async () => {
  const out = await CheckKImplFiniteRelSuccessor0(
    makeKImplFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplFiniteRelSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticFiniteRelNodeCount, 1);
  assert.equal(out.NF.semanticKernelReady, true);
  assert.deepEqual(out.NF.missingSemanticRules, []);
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
    'FiniteRel',
  ]);
});

test('FiniteRel successor accepts explicit final-theorem purpose at KImpl boundary', async () => {
  const out = await CheckKImplFiniteRelSuccessor0(
    makeKImplFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'final-theorem-ready');
  assert.equal(out.NF.semanticKernelReady, true);
  assert.equal(out.NF.finalTheoremReady, true);
  assert.equal(out.NF.publicTheoremEmissionAllowed, true);
});

test('FiniteRel final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplFiniteRelFinalTheoremReadiness0(
    makeKImplFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplFiniteRelFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel final-theorem readiness requires a final-theorem purpose record',
  );
});

test('FiniteRel final gate accepts complete primitive semantic coverage', async () => {
  const out = await CheckKImplFiniteRelFinalTheoremReadiness0(
    makeKImplFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'final-theorem-ready');
  assert.equal(out.NF.finalTheoremReady, true);
  assert.equal(out.NF.publicTheoremEmissionAllowed, true);
  assert.deepEqual(out.NF.missingSemanticRules, []);
});

test('FiniteRel successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplFiniteRelSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteRelSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel successor rejects caller-supplied semantic readiness assertions',
  );
});

test('FiniteRel successor rejects a weakened release policy', async () => {
  const input = makeKImplFiniteRelSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  input.Policy.equalityInclusionAndClosureComputed = false;

  const out = await CheckKImplFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteRelSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'FiniteRel successor release policy must match the fail-closed policy',
  );
});

test('FiniteRel successor rejects a stale TruthVec-only successor record', async () => {
  const input = makeKImplFiniteRelSuccessor0({
    SemanticProofDAG: makeFiniteRelProof0(),
  });
  input.kind = makeKImplTruthVecSuccessor0().kind;

  const out = await CheckKImplFiniteRelSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteRelSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'FiniteRel successor KImpl kind must be KImplSemanticFiniteRelSuccessor0',
  );
});

test('FiniteRel successor rejects a mutated relation conclusion in development mode', async () => {
  const out = await CheckKImplFiniteRelSuccessor0(
    makeKImplFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteRelSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'FiniteRel conclusion must exactly equal the computed relation and claim ledger',
  );
});

test('FiniteRel successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter(
      (rule) => rule.name !== 'FiniteRel',
    ),
  });

  const out = await CheckKImplFiniteRelSuccessor0(
    makeKImplFiniteRelSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeFiniteRelProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFiniteRelSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});
