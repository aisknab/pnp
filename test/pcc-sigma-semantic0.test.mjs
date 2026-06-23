import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

import {
  makeKernelConformanceSuite0,
  makeSigmaRegistry0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplFiniteRelSuccessor0,
} from '../pcc-kimpl-finiterel-successor0.mjs';

import {
  makeSemanticK0ConformanceSuite0,
} from '../pcc-k0-semantic-conformance0.mjs';

import {
  CheckSemanticSigma0,
  CheckSemanticSigmaV53Derivation0,
  CheckSemanticSigmaV54Derivation0,
  deriveSemanticSigmaV53Conclusion0,
  deriveSemanticSigmaV54Conclusion0,
  makeSemanticSigmaInput0,
  makeSemanticSigmaSuite0,
  makeSemanticSigmaV53Hyperedge0,
  makeSemanticSigmaV53Spec0,
  makeSemanticSigmaV54MinimalConsumer0,
  makeSemanticSigmaV54Spec0,
} from '../pcc-sigma-semantic0.mjs';

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
    programId: 'sigma.semantic.finiterel.program',
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
    evaluationId: 'sigma.semantic.finiterel.eval',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.sigma.semantic',
      RuleName: 'FiniteRel',
      Conclusion: conclusion,
      Payload: { op: 'verify', spec },
    }),
  ]);
}

function makeInput0() {
  const K0 = makeKernelConformanceSuite0();
  const PSigma = makeSigmaRegistry0();
  return makeSemanticSigmaInput0({
    KImpl: makeKImplFiniteRelSuccessor0({
      SemanticProofDAG: makeFiniteRelProof0(),
    }),
    K0,
    K0SemanticConformance: makeSemanticK0ConformanceSuite0({ K0 }),
    PSigma,
    SemanticSigma: makeSemanticSigmaSuite0({ PSigma }),
  });
}

function replaceDerivation0(entry, changes) {
  const {
    derivationDigest: _ignored,
    ...baseEntry
  } = entry;
  const base = {
    ...baseEntry,
    ...changes,
  };
  return {
    ...base,
    derivationDigest: digestCanonical0(base),
  };
}

test('semantic Sigma accepts exact V53 and V54 bounded derivations', async () => {
  const out = await CheckSemanticSigma0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckSemanticSigma0');
  assert.equal(out.NF.semanticSigmaReady, true);
  assert.equal(out.NF.semanticDerivationsReady, true);
  assert.equal(out.NF.semanticKImplFinalReady, true);
  assert.equal(out.NF.semanticK0ConformanceReady, true);
  assert.equal(out.NF.v53Ready, true);
  assert.equal(out.NF.v54Ready, true);
  assert.deepEqual(out.NF.semanticSigmaTheorems, ['V53', 'V54']);
  assert.equal(out.NF.semanticSigmaDerivationCount, 2);
  assert.equal(out.NF.boundedFiniteDerivationsOnly, true);
  assert.equal(out.NF.unrestrictedUniversalSchemaNotClaimed, true);
  assert.equal(out.NF.reflectionReady, false);
});

test('V53 computes the exact two-anchor pair case', () => {
  const input = makeInput0();
  const canonical = input.SemanticSigma.derivations[0];
  const spec = makeSemanticSigmaV53Spec0({
    derivationId: 'Sigma.V53.test.pair',
    anchors: ['a', 'b'],
    hyperedges: [
      makeSemanticSigmaV53Hyperedge0({
        index: 0,
        anchors: ['a', 'b'],
        weight: 5,
      }),
    ],
    cutValue: 5,
  });
  const entry = replaceDerivation0(canonical, {
    spec,
    conclusion: deriveSemanticSigmaV53Conclusion0({ spec }),
  });

  const out = CheckSemanticSigmaV53Derivation0(entry);

  assert.equal(out.tag, 'accept');
  assert.equal(entry.conclusion.classification, 'pair');
  assert.equal(entry.conclusion.pairWeight, 5);
  assert.equal(entry.conclusion.fullSpanWeight, 5);
});

test('V53 computes the four-or-more-anchor full-span case', () => {
  const input = makeInput0();
  const canonical = input.SemanticSigma.derivations[0];
  const spec = makeSemanticSigmaV53Spec0({
    derivationId: 'Sigma.V53.test.fullspan',
    anchors: ['a', 'b', 'c', 'd'],
    hyperedges: [
      makeSemanticSigmaV53Hyperedge0({
        index: 0,
        anchors: ['a', 'b', 'c', 'd'],
        weight: 2,
      }),
    ],
    cutValue: 2,
  });
  const entry = replaceDerivation0(canonical, {
    spec,
    conclusion: deriveSemanticSigmaV53Conclusion0({ spec }),
  });

  const out = CheckSemanticSigmaV53Derivation0(entry);

  assert.equal(out.tag, 'accept');
  assert.equal(entry.conclusion.classification, 'full-span');
  assert.equal(entry.conclusion.everyProperHyperedgeWeightZero, true);
  assert.equal(entry.conclusion.fullSpanWeight, 2);
});

test('V53 rejects a hypergraph whose proper-cut values are not constant', () => {
  const input = makeInput0();
  const canonical = input.SemanticSigma.derivations[0];
  const badSpec = {
    ...canonical.spec,
    hyperedges: canonical.spec.hyperedges.map((edge, index) => (
      index === 0 ? { ...edge, weight: 2 } : edge
    )),
  };
  const entry = replaceDerivation0(canonical, { spec: badSpec });

  const out = CheckSemanticSigmaV53Derivation0(entry);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticSigmaV53Derivation0.derive');
  assert.equal(
    out.Witness.reason,
    'V53 constant-cut premise does not hold on every nonempty proper cut',
  );
});

test('V53 rejects caller-supplied theorem truth assertions', () => {
  const input = makeInput0();
  const canonical = input.SemanticSigma.derivations[0];
  const badSpec = {
    ...canonical.spec,
    theoremHolds: true,
  };
  const entry = replaceDerivation0(canonical, { spec: badSpec });

  const out = CheckSemanticSigmaV53Derivation0(entry);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticSigmaV53Derivation0.spec');
  assert.equal(
    out.Witness.reason,
    'V53 specification rejects caller-supplied theorem truth, classification, proof, solver, search, optimization, or oracle assertions',
  );
});

test('V54 computes singleton cut-indicator normal form', () => {
  const input = makeInput0();
  const entry = input.SemanticSigma.derivations[1];

  const out = CheckSemanticSigmaV54Derivation0(entry);

  assert.equal(out.tag, 'accept');
  assert.equal(entry.conclusion.activationNonzero, true);
  assert.equal(entry.conclusion.hasDisjointPair, true);
  assert.equal(entry.conclusion.allDisjointPairsSingletons, true);
  assert.equal(entry.conclusion.cutIndicatorMatches, true);
  assert.deepEqual(entry.conclusion.singletonFootprint, ['a', 'b']);
});

test('V54 computes a nonsingleton disjoint-pair case without overclaiming singleton normal form', () => {
  const input = makeInput0();
  const canonical = input.SemanticSigma.derivations[1];
  const spec = makeSemanticSigmaV54Spec0({
    derivationId: 'Sigma.V54.test.nonsingleton',
    anchors: ['a', 'b', 'c', 'd'],
    minimalConsumers: [
      makeSemanticSigmaV54MinimalConsumer0({
        index: 0,
        anchors: ['a', 'b'],
      }),
      makeSemanticSigmaV54MinimalConsumer0({
        index: 1,
        anchors: ['c', 'd'],
      }),
    ],
  });
  const entry = replaceDerivation0(canonical, {
    spec,
    conclusion: deriveSemanticSigmaV54Conclusion0({ spec }),
  });

  const out = CheckSemanticSigmaV54Derivation0(entry);

  assert.equal(out.tag, 'accept');
  assert.equal(entry.conclusion.activationNonzero, true);
  assert.equal(entry.conclusion.hasDisjointPair, true);
  assert.equal(entry.conclusion.allDisjointPairsSingletons, false);
  assert.equal(entry.conclusion.singletonNormalFormApplicable, false);
  assert.equal(entry.conclusion.cutIndicatorMatches, null);
});

test('V54 rejects a nonminimal consumer family', () => {
  const input = makeInput0();
  const canonical = input.SemanticSigma.derivations[1];
  const badSpec = {
    kind: 'SemanticSigmaV54Spec0',
    version: 0,
    derivationId: 'Sigma.V54.test.nonantichain',
    anchors: ['a', 'b'],
    minimalConsumers: [
      makeSemanticSigmaV54MinimalConsumer0({ index: 0, anchors: ['a'] }),
      makeSemanticSigmaV54MinimalConsumer0({ index: 1, anchors: ['a', 'b'] }),
    ],
  };
  const entry = replaceDerivation0(canonical, { spec: badSpec });

  const out = CheckSemanticSigmaV54Derivation0(entry);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticSigmaV54Derivation0.spec');
  assert.equal(
    out.Witness.reason,
    'V54 minimalConsumers must form an inclusion antichain',
  );
});

test('semantic Sigma rejects a stale legacy registry digest binding', async () => {
  const base = makeInput0();
  const derivations = base.SemanticSigma.derivations.map((entry, index) => (
    index === 0
      ? { ...entry, registryEntryDigest: digestCanonical0({ stale: true }) }
      : entry
  ));
  const input = {
    ...base,
    SemanticSigma: {
      ...base.SemanticSigma,
      derivations,
    },
  };

  const out = await CheckSemanticSigma0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticSigma0.semanticSigmaSuite.registryBinding');
  assert.equal(
    out.Witness.reason,
    'semantic Sigma derivation must bind the exact legacy registry entry digest',
  );
});

test('semantic Sigma rejects a legacy registry missing V54', async () => {
  const base = makeInput0();
  const input = {
    ...base,
    PSigma: {
      ...base.PSigma,
      theorems: base.PSigma.theorems.filter(
        (entry) => !String(entry.id).includes('V54'),
      ),
    },
  };

  const out = await CheckSemanticSigma0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticSigma0.legacySigma');
  assert.equal(
    out.Witness.reason,
    'legacy Sigma registry rejected before semantic derivation upgrade',
  );
});
