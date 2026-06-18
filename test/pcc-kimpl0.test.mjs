import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckConformance0,
  CheckKBundle0,
  CheckKImpl0,
  CheckReflectionRegistry0,
  CheckSigmaRegistry0,
  KERNEL_RULES0,
  makeKernelConformanceSuite0,
  makeKernelProofNode0,
  makeKernelRuleTable0,
  makeReflectionRegistry0,
  makeSigmaRegistry0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

test('CheckKImpl0 accepts the synthetic proof-kernel implementation', async () => {
  const out = await CheckKImpl0(makeSyntheticKImpl0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImpl0');
  assert.equal(out.NF.primitiveRuleCount, KERNEL_RULES0.length);
  assert.equal(out.NF.ruleCount, KERNEL_RULES0.length);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckKImpl0 rejects a missing primitive kernel rule', async () => {
  const out = await CheckKImpl0(makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckKImpl0');
  assert.equal(out.Coord, 'CheckKImpl0.RuleTable');
  assert.deepEqual(out.Path, ['RuleTable', 'Hall']);
  assert.equal(out.Witness.reason, 'kernel rule table is missing a primitive rule');
});

test('CheckKImpl0 rejects opaque proof blobs inside proof nodes', async () => {
  const node = {
    ...makeKernelProofNode0({
      id: 'node.opaque',
      RuleName: 'Eq',
    }),
    opaqueProof: {
      bytes: 'not-allowed',
    },
  };

  const out = await CheckKImpl0(makeSyntheticKImpl0({
    ProofDAG: [node],
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckKImpl0');
  assert.equal(out.Coord, 'CheckKImpl0.opaqueProof');
  assert.deepEqual(out.Path, ['KImpl', 'ProofDAG', 0, 'opaqueProof']);
});

test('CheckKImpl0 rejects a proof node with a forward premise', async () => {
  const nodes = [
    makeKernelProofNode0({
      id: 'node.a',
      RuleName: 'Eq',
    }),
    makeKernelProofNode0({
      id: 'node.b',
      RuleName: 'Subst',
      Premises: ['node.c'],
    }),
    makeKernelProofNode0({
      id: 'node.c',
      RuleName: 'Record',
    }),
  ];

  const out = await CheckKImpl0(makeSyntheticKImpl0({
    ProofDAG: nodes,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckKImpl0');
  assert.equal(out.Coord, 'CheckKImpl0.ProofDAG');
  assert.deepEqual(out.Path, ['ProofDAG', 1, 'Premises', 0]);
  assert.equal(out.Witness.reason, 'proof premise must reference an earlier node');
});

test('CheckConformance0 accepts complete primitive-rule conformance coverage', async () => {
  const out = await CheckConformance0(
    makeSyntheticKImpl0(),
    makeKernelConformanceSuite0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConformance0');
  assert.equal(out.NF.primitiveRuleCount, KERNEL_RULES0.length);
  assert.equal(out.NF.nodeCount, KERNEL_RULES0.length);
});

test('CheckConformance0 rejects a conformance suite missing a primitive rule', async () => {
  const suite = makeKernelConformanceSuite0();

  suite.nodes = suite.nodes.filter((node) => node.RuleName !== 'TruthVec');

  const out = await CheckConformance0(makeSyntheticKImpl0(), suite);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConformance0');
  assert.equal(out.Coord, 'CheckConformance0.coverage');
  assert.deepEqual(out.Path, ['coverage', 'TruthVec']);
  assert.equal(out.Witness.reason, 'conformance suite is missing a primitive rule');
});

test('CheckSigmaRegistry0 accepts V53 and V54 Sigma coverage', async () => {
  const out = await CheckSigmaRegistry0(makeSigmaRegistry0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckSigmaRegistry0');
  assert.equal(out.NF.theoremCount, 2);
  assert.deepEqual(out.NF.requiredTheorems, ['V53', 'V54']);
});

test('CheckSigmaRegistry0 rejects missing V54', async () => {
  const registry = makeSigmaRegistry0();

  registry.theorems = registry.theorems.filter((entry) => !String(entry.id).includes('V54'));

  const out = await CheckSigmaRegistry0(registry);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckSigmaRegistry0');
  assert.equal(out.Coord, 'CheckSigmaRegistry0.coverage');
  assert.deepEqual(out.Path, ['coverage', 'V54']);
});

test('CheckReflectionRegistry0 accepts required checker reflections', async () => {
  const out = await CheckReflectionRegistry0(makeReflectionRegistry0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReflectionRegistry0');
  assert.equal(out.NF.reflectionCount, 5);
  assert.equal(out.NF.checkers.includes('CheckBoot0'), true);
});

test('CheckReflectionRegistry0 rejects a missing CheckBoot0 reflection', async () => {
  const registry = makeReflectionRegistry0();

  registry.reflections = registry.reflections.filter((entry) => entry.checker !== 'CheckBoot0');

  const out = await CheckReflectionRegistry0(registry);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReflectionRegistry0');
  assert.equal(out.Coord, 'CheckReflectionRegistry0.coverage');
  assert.deepEqual(out.Path, ['coverage', 'CheckBoot0']);
});

test('CheckKBundle0 accepts KImpl, K0, Sigma, and reflection registries together', async () => {
  const out = await CheckKBundle0({
    KImpl: makeSyntheticKImpl0(),
    K0: makeKernelConformanceSuite0(),
    PSigma: makeSigmaRegistry0(),
    ReflectionRegistry: makeReflectionRegistry0(),
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundle0');
  assert.equal(out.NF.kind, 'KBundle0NF');
});