import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelConformanceSuite0,
  makeReflectionRegistry0,
  makeSigmaRegistry0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplFiniteRelSuccessor0,
} from '../pcc-kimpl-finiterel-successor0.mjs';

import {
  makeSemanticK0ConformanceSuite0,
} from '../pcc-k0-semantic-conformance0.mjs';

import {
  makeSemanticSigmaSuite0,
} from '../pcc-sigma-semantic0.mjs';

import {
  CheckSemanticReflection0,
  makeSemanticReflectionInput0,
  makeSemanticReflectionSuite0,
} from '../pcc-reflection-semantic0.mjs';

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

const requiredCheckers = [
  'CheckVerifierFrag0',
  'CheckBoot0',
  'CheckBootBatch0',
  'CheckBootAudit0',
  'CheckKImpl0',
];

function makeFiniteRelProof0() {
  const domain = makeSemanticFiniteRelDomain0({
    index: 0,
    id: 'D',
    elements: ['a', 'b'],
  });
  const literal = makeSemanticFiniteRelNode0({
    index: 0,
    id: 'R',
    op: 'literal',
    domainIds: ['D', 'D'],
    tuples: [makeSemanticFiniteRelTuple0({ index: 0, values: ['a', 'b'] })],
  });
  const closure = makeSemanticFiniteRelNode0({
    index: 1,
    id: 'R.rtc',
    op: 'reflexive-transitive-closure',
    domainIds: ['D', 'D'],
    inputIds: ['R'],
  });
  const program = makeSemanticFiniteRelProgram0({
    programId: 'reflection.semantic.finiterel.program',
    domains: [domain],
    nodes: [literal, closure],
    claims: [
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
    ],
  });
  const spec = makeSemanticFiniteRelSpec0({
    evaluationId: 'reflection.semantic.finiterel.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.reflection.semantic',
      RuleName: 'FiniteRel',
      Conclusion: deriveSemanticFiniteRelJudgment0({ spec }),
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0() {
  const K0 = makeKernelConformanceSuite0();
  const PSigma = makeSigmaRegistry0();
  const ReflectionRegistry = makeReflectionRegistry0();
  return makeSemanticReflectionInput0({
    KImpl: makeKImplFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
    }),
    K0,
    K0SemanticConformance: makeSemanticK0ConformanceSuite0({ K0 }),
    PSigma,
    SigmaSemanticDerivations: makeSemanticSigmaSuite0({ PSigma }),
    ReflectionRegistry,
    SemanticReflection: makeSemanticReflectionSuite0({ ReflectionRegistry }),
  });
}

test('semantic reflection checker accepts exact executable refinements for all required checkers', async () => {
  const out = await CheckSemanticReflection0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckSemanticReflection0');
  assert.equal(out.NF.semanticReflectionReady, true);
  assert.equal(out.NF.semanticReflectionContractReady, true);
  assert.equal(out.NF.semanticReflectionSoundnessSurfaceReady, true);
  assert.equal(out.NF.semanticKImplFinalReady, true);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.deepEqual(out.NF.semanticReflectionCheckers, requiredCheckers);
  assert.equal(out.NF.semanticReflectionCount, 5);
  assert.equal(out.NF.canonicalPositiveProbeCount, 5);
  assert.equal(out.NF.canonicalNegativeProbeCount, 5);
  assert.equal(out.NF.boundedExecutableRefinementsOnly, true);
  assert.equal(out.NF.unrestrictedCheckerSoundnessNotClaimed, true);
  assert.equal(out.NF.globalNodeDerivationsReady, false);

  for (const refinement of out.NF.semanticReflectionRefinements) {
    assert.equal(refinement.positiveNFKind.endsWith('NF'), true);
    assert.equal(refinement.negativeCoord.startsWith(refinement.reflectedChecker), true);
    assert.equal(refinement.boundedExecutableRefinement, true);
    assert.equal(refinement.unrestrictedCheckerSoundnessNotClaimed, true);
  }
});

test('semantic reflection checker rejects caller-supplied readiness assertions', async () => {
  const input = {
    ...makeInput0(),
    semanticReflectionReady: true,
  };
  const out = await CheckSemanticReflection0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticReflection0.input');
  assert.deepEqual(out.Path, ['semanticReflectionReady']);
  assert.equal(
    out.Witness.reason,
    'semantic reflection rejects caller-supplied readiness or soundness assertions',
  );
});

test('semantic reflection checker rejects caller soundness fields inside a refinement', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    SemanticReflection: {
      ...base.SemanticReflection,
      refinements: base.SemanticReflection.refinements.map((entry, index) => (
        index === 0 ? { ...entry, sound: true } : entry
      )),
    },
  };
  const out = await CheckSemanticReflection0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticReflection0.semanticReflectionSuite');
  assert.equal(
    out.Witness.reason,
    'semantic reflection refinement must exactly match the computed registry and executable checker binding',
  );
});

test('semantic reflection checker rejects a stale executable checker contract digest', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    SemanticReflection: {
      ...base.SemanticReflection,
      refinements: base.SemanticReflection.refinements.map((entry) => (
        entry.checker === 'CheckBoot0'
          ? {
              ...entry,
              checkerContractDigest: {
                alg: 'SHA256',
                hex: '0'.repeat(64),
              },
            }
          : entry
      )),
    },
  };
  const out = await CheckSemanticReflection0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticReflection0.semanticReflectionSuite');
  assert.equal(
    out.Witness.reason,
    'semantic reflection refinement must exactly match the computed registry and executable checker binding',
  );
});

test('semantic reflection checker rejects a stale registry-entry digest binding', async () => {
  const base = makeInput0();
  const ReflectionRegistry = {
    ...base.ReflectionRegistry,
    reflections: base.ReflectionRegistry.reflections.map((entry) => (
      entry.checker === 'CheckKImpl0'
        ? { ...entry, theorem: 'CheckKImpl0.StaleSoundness' }
        : entry
    )),
  };
  const input = {
    ...base,
    ReflectionRegistry,
  };
  const out = await CheckSemanticReflection0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticReflection0.semanticReflectionSuite');
  assert.equal(
    out.Witness.reason,
    'semantic reflection refinement must exactly match the computed registry and executable checker binding',
  );
});

test('semantic reflection checker rejects missing legacy reflection coverage before upgrade', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    ReflectionRegistry: {
      ...base.ReflectionRegistry,
      reflections: base.ReflectionRegistry.reflections.filter(
        (entry) => entry.checker !== 'CheckBoot0',
      ),
    },
  };
  const out = await CheckSemanticReflection0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticReflection0.legacyReflection');
  assert.equal(
    out.Witness.reason,
    'legacy reflection registry rejected before semantic refinement upgrade',
  );
});

test('semantic reflection checker rejects a mutated semantic Sigma derivation', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    SigmaSemanticDerivations: {
      ...base.SigmaSemanticDerivations,
      derivations: base.SigmaSemanticDerivations.derivations.map((entry) => (
        entry.theorem === 'V53'
          ? {
              ...entry,
              conclusion: {
                ...entry.conclusion,
                cutValue: 999,
              },
            }
          : entry
      )),
    },
  };
  const out = await CheckSemanticReflection0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticReflection0.semanticSigma');
  assert.equal(
    out.Witness.reason,
    'semantic reflection refinements require accepted semantic Sigma derivations',
  );
});
