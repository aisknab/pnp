import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofTruthVec0,
  CheckSemanticKernelReadinessTruthVec0,
  deriveSemanticTruthVecJudgment0,
  makeSemanticTruthVecConstNode0,
  makeSemanticTruthVecDomain0,
  makeSemanticTruthVecInputNode0,
  makeSemanticTruthVecNANDNode0,
  makeSemanticTruthVecOutput0,
  makeSemanticTruthVecProgram0,
  makeSemanticTruthVecSpec0,
} from '../pcc-kernel-truthvec-semantic0.mjs';

function makeFixture0() {
  const nodes = [
    makeSemanticTruthVecInputNode0({ index: 0, id: 'x' }),
    makeSemanticTruthVecInputNode0({ index: 1, id: 'y' }),
    makeSemanticTruthVecConstNode0({ index: 2, id: 'one', value: true }),
    makeSemanticTruthVecNANDNode0({
      index: 3,
      id: 'nand.xy',
      leftId: 'x',
      rightId: 'y',
    }),
    makeSemanticTruthVecNANDNode0({
      index: 4,
      id: 'not.x',
      leftId: 'x',
      rightId: 'x',
    }),
    makeSemanticTruthVecNANDNode0({
      index: 5,
      id: 'and.xy',
      leftId: 'nand.xy',
      rightId: 'nand.xy',
    }),
  ];
  const outputs = [
    makeSemanticTruthVecOutput0({
      index: 0,
      id: 'out.nand',
      nodeId: 'nand.xy',
    }),
    makeSemanticTruthVecOutput0({
      index: 1,
      id: 'out.and',
      nodeId: 'and.xy',
    }),
    makeSemanticTruthVecOutput0({
      index: 2,
      id: 'out.x',
      nodeId: 'x',
    }),
    makeSemanticTruthVecOutput0({
      index: 3,
      id: 'out.one',
      nodeId: 'one',
    }),
  ];
  const program = makeSemanticTruthVecProgram0({
    programId: 'truth.program.xy',
    nodes,
    outputs,
  });
  const domain = makeSemanticTruthVecDomain0({ inputIds: ['x', 'y'] });
  const spec = makeSemanticTruthVecSpec0({
    evaluationId: 'truth.eval.xy',
    program,
    domain,
  });
  const conclusion = deriveSemanticTruthVecJudgment0({ spec });
  const node = makeSemanticProofNode0({
    id: 'truth.evaluate',
    RuleName: 'TruthVec',
    Conclusion: conclusion,
    Payload: { op: 'evaluate', spec },
  });
  return { nodes, outputs, program, domain, spec, conclusion, node };
}

function runNode0(node, prefix = []) {
  return CheckSemanticKernelProofTruthVec0(
    makeSemanticProofDAG0([...prefix, node]),
  );
}

test('TruthVec computes every ordered NAND output over the canonical Boolean cube', () => {
  const fixture = makeFixture0();
  const out = runNode0(fixture.node);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.truthVecNodeCount, 1);
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
    'TruthVec',
  ]);
  assert.deepEqual(
    fixture.conclusion.domain.assignments.map((assignment) => assignment.bits),
    [
      [false, false],
      [false, true],
      [true, false],
      [true, true],
    ],
  );
  assert.deepEqual(
    fixture.conclusion.vectors.map((vector) => vector.outputId),
    ['out.nand', 'out.and', 'out.x', 'out.one'],
  );
  assert.deepEqual(fixture.conclusion.vectors[0].bits, [true, true, true, false]);
  assert.deepEqual(fixture.conclusion.vectors[1].bits, [false, false, false, true]);
  assert.deepEqual(fixture.conclusion.vectors[2].bits, [false, false, true, true]);
  assert.deepEqual(fixture.conclusion.vectors[3].bits, [true, true, true, true]);
  assert.equal(fixture.conclusion.exactBooleanCubeDomain, true);
  assert.equal(fixture.conclusion.everyOutputBitComputed, true);
  assert.equal(fixture.conclusion.outputOrderPreserved, true);
});

test('TruthVec accepts a zero-input constant program with one canonical assignment', () => {
  const program = makeSemanticTruthVecProgram0({
    programId: 'truth.program.constant',
    nodes: [
      makeSemanticTruthVecConstNode0({ index: 0, id: 'zero', value: false }),
    ],
    outputs: [
      makeSemanticTruthVecOutput0({ index: 0, id: 'out.zero', nodeId: 'zero' }),
    ],
  });
  const spec = makeSemanticTruthVecSpec0({
    evaluationId: 'truth.eval.constant',
    program,
  });
  const conclusion = deriveSemanticTruthVecJudgment0({ spec });
  const node = makeSemanticProofNode0({
    id: 'truth.constant',
    RuleName: 'TruthVec',
    Conclusion: conclusion,
    Payload: { op: 'evaluate', spec },
  });
  const out = runNode0(node);

  assert.equal(out.tag, 'accept');
  assert.equal(conclusion.assignmentCount, 1);
  assert.deepEqual(conclusion.domain.assignments[0].bits, []);
  assert.deepEqual(conclusion.vectors[0].bits, [false]);
});

test('TruthVec rejects an incomplete Boolean-cube domain', () => {
  const fixture = makeFixture0();
  const domain = {
    ...fixture.domain,
    assignments: fixture.domain.assignments.slice(0, -1),
  };
  const spec = { ...fixture.spec, domain };
  const out = runNode0({
    ...fixture.node,
    Payload: { op: 'evaluate', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofTruthVec0.shape');
  assert.equal(
    out.Witness.reason,
    'TruthVec domain must contain the complete Boolean cube',
  );
});

test('TruthVec rejects a noncanonical assignment order', () => {
  const fixture = makeFixture0();
  const assignments = fixture.domain.assignments.map((assignment, index) => (
    index === 1 ? { ...assignment, bits: [true, false] } : assignment
  ));
  const domain = { ...fixture.domain, assignments };
  const spec = { ...fixture.spec, domain };
  const out = runNode0({
    ...fixture.node,
    Payload: { op: 'evaluate', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TruthVec assignments must be in canonical binary lexicographic order',
  );
});

test('TruthVec rejects assignment bits with the wrong input arity', () => {
  const fixture = makeFixture0();
  const assignments = fixture.domain.assignments.map((assignment, index) => (
    index === 0 ? { ...assignment, bits: [false] } : assignment
  ));
  const domain = { ...fixture.domain, assignments };
  const spec = { ...fixture.spec, domain };
  const out = runNode0({
    ...fixture.node,
    Payload: { op: 'evaluate', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TruthVec assignment bits must exactly match the input arity',
  );
});

test('TruthVec rejects an input node after computation begins', () => {
  const fixture = makeFixture0();
  const program = {
    kind: 'SemanticTruthVecProgram0',
    version: 0,
    programId: 'truth.program.late.input',
    nodes: [
      makeSemanticTruthVecInputNode0({ index: 0, id: 'x' }),
      makeSemanticTruthVecConstNode0({ index: 1, id: 'one', value: true }),
      makeSemanticTruthVecInputNode0({ index: 2, id: 'y' }),
    ],
    outputs: [
      makeSemanticTruthVecOutput0({ index: 0, id: 'out.x', nodeId: 'x' }),
    ],
  };
  const spec = { ...fixture.spec, program };
  const out = runNode0({
    ...fixture.node,
    Payload: { op: 'evaluate', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TruthVec input nodes must form the initial canonical input block',
  );
});

test('TruthVec rejects a NAND input that is not an earlier program node', () => {
  const fixture = makeFixture0();
  const nodes = fixture.program.nodes.map((node) => (
    node.id === 'nand.xy'
      ? { ...node, inputIds: ['future.node', 'y'] }
      : node
  ));
  const program = { ...fixture.program, nodes };
  const spec = { ...fixture.spec, program };
  const out = runNode0({
    ...fixture.node,
    Payload: { op: 'evaluate', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TruthVec NAND input must reference an earlier program node',
  );
});

test('TruthVec rejects an unsupported Boolean operator node', () => {
  const fixture = makeFixture0();
  const nodes = fixture.program.nodes.map((node) => (
    node.id === 'nand.xy' ? { ...node, nodeKind: 'OR' } : node
  ));
  const program = { ...fixture.program, nodes };
  const spec = { ...fixture.spec, program };
  const out = runNode0({
    ...fixture.node,
    Payload: { op: 'evaluate', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'TruthVec program node kind is unsupported');
});

test('TruthVec rejects an output referencing an undeclared node', () => {
  const fixture = makeFixture0();
  const outputs = fixture.program.outputs.map((output, index) => (
    index === 0 ? { ...output, nodeId: 'missing.node' } : output
  ));
  const program = { ...fixture.program, outputs };
  const spec = { ...fixture.spec, program };
  const out = runNode0({
    ...fixture.node,
    Payload: { op: 'evaluate', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TruthVec output must reference a declared program node',
  );
});

test('TruthVec rejects caller-supplied vectors or equality assertions', () => {
  const fixture = makeFixture0();
  const out = runNode0({
    ...fixture.node,
    Payload: {
      op: 'evaluate',
      spec: fixture.spec,
      vectors: fixture.conclusion.vectors,
      equal: true,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofTruthVec0.shape');
  assert.equal(
    out.Witness.reason,
    'TruthVec payload rejects caller-supplied vectors, equality, completeness, normalization, result, solver, search, optimization, or oracle assertions',
  );
});

test('TruthVec rejects caller-supplied completeness inside the specification', () => {
  const fixture = makeFixture0();
  const spec = { ...fixture.spec, complete: true };
  const out = runNode0({
    ...fixture.node,
    Payload: { op: 'evaluate', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TruthVec specification rejects caller-supplied vectors, equality, completeness, normalization, result, solver, search, optimization, or oracle assertions',
  );
});

test('TruthVec evaluate rejects every proof premise because computation is closed', () => {
  const fixture = makeFixture0();
  const term = makeSemanticConst0('truth.premise', 'Term');
  const premise = makeSemanticProofNode0({
    id: 'eq.truth.premise',
    RuleName: 'Eq',
    Conclusion: makeSemanticEqJudgment0(term, term),
    Payload: { op: 'refl' },
  });
  const out = runNode0({
    ...fixture.node,
    Premises: ['eq.truth.premise'],
  }, [premise]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TruthVec evaluate is a closed exact finite computation and must not consume premises',
  );
});

test('TruthVec rejects a mutated computed vector conclusion', () => {
  const fixture = makeFixture0();
  const vectors = fixture.conclusion.vectors.map((vector, index) => (
    index === 0
      ? { ...vector, bits: [false, ...vector.bits.slice(1)] }
      : vector
  ));
  const out = runNode0({
    ...fixture.node,
    Conclusion: { ...fixture.conclusion, vectors },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TruthVec conclusion must exactly equal the computed ordered Boolean vectors',
  );
});

test('TruthVec rejects input arity beyond the explicit bound', () => {
  const fixture = makeFixture0();
  const nodes = Array.from({ length: 13 }, (_, index) =>
    makeSemanticTruthVecInputNode0({ index, id: `input.${index}` }));
  const program = {
    kind: 'SemanticTruthVecProgram0',
    version: 0,
    programId: 'truth.program.too.wide',
    nodes,
    outputs: [
      makeSemanticTruthVecOutput0({
        index: 0,
        id: 'out.first',
        nodeId: 'input.0',
      }),
    ],
  };
  const spec = { ...fixture.spec, program };
  const out = runNode0({
    ...fixture.node,
    Payload: { op: 'evaluate', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'TruthVec input arity exceeds maxInputs');
});

test('predecessor rules cannot consume TruthVec conclusions without explicit semantics', () => {
  const fixture = makeFixture0();
  const term = makeSemanticConst0('after.truthvec', 'Term');
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.truthvec',
    RuleName: 'Eq',
    Premises: ['truth.evaluate'],
    Conclusion: makeSemanticEqJudgment0(term, term),
    Payload: { op: 'symm' },
  });
  const out = CheckSemanticKernelProofTruthVec0(
    makeSemanticProofDAG0([fixture.node, illegal]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofTruthVec0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd/MinCounterexample/IntArith/Transport sub-DAG rejected under the predecessor semantic checker',
  );
});

test('TruthVec readiness removes TruthVec and leaves only FiniteRel missing', () => {
  const out = CheckSemanticKernelReadinessTruthVec0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessTruthVec0.coverage');
  assert.equal(out.Witness.missingRules.includes('TruthVec'), false);
  assert.deepEqual(out.Witness.missingRules, ['FiniteRel']);
});
