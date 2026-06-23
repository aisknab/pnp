import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelConformanceSuite0,
  makeKernelRuleTable0,
} from '../pcc-kimpl0.mjs';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckK0SemanticConformance0,
  makeK0SemanticConformanceInput0,
} from '../pcc-k0-semantic-conformance0.mjs';

const rules = [
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
];

test('K0 semantic conformance binds every primitive rule to executable checker and test sources', async () => {
  const out = await CheckK0SemanticConformance0(
    makeK0SemanticConformanceInput0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckK0SemanticConformance0');
  assert.equal(out.NF.semanticConformanceReady, true);
  assert.equal(out.NF.conformanceScope, 'executable-contract-conformance');
  assert.equal(out.NF.mathematicalMetasoundnessEstablished, false);
  assert.equal(out.NF.mathematicalMetasoundnessRequiresIndependentAudit, true);
  assert.equal(out.NF.exactLegacyConformanceSuite, true);
  assert.equal(out.NF.exactLegacyRuleTable, true);
  assert.equal(out.NF.semanticKImplFinalReady, true);
  assert.equal(out.NF.ruleCount, 16);
  assert.equal(out.NF.layerCount, 15);
  assert.deepEqual(out.NF.coveredRules, rules);
  assert.deepEqual(out.NF.missingRules, []);
  assert.equal(out.NF.rules.length, 16);
  assert.deepEqual(out.NF.rules.map((item) => item.ruleName), rules);
  assert.equal(out.NF.rules.every((item) => item.ownerRecognizedRule), true);
  assert.equal(
    out.NF.rules.slice(2).every(
      (item) => item.predecessorRejectedUnsupported === true,
    ),
    true,
  );
  assert.equal(
    out.NF.rules.slice(0, 2).every(
      (item) => item.predecessorRejectedUnsupported === null,
    ),
    true,
  );
  assert.equal(
    out.NF.layers.every(
      (layer) => layer.moduleSourceDigest.alg === 'SHA256'
        && layer.testSourceDigest.alg === 'SHA256'
        && layer.testCaseCount >= 2
        && layer.negativeTestMarkerPresent === true
        && layer.emptyProofAccepted === true,
    ),
    true,
  );
  assert.equal(out.NF.layers.at(-1).readinessTag, 'accept');
  assert.equal(
    out.NF.layers.slice(0, -1).every(
      (layer) => layer.readinessTag === 'reject',
    ),
    true,
  );
  assert.equal(out.NF.allCheckerModulesDigest.alg, 'SHA256');
});

test('K0 semantic conformance rejects a noncanonical legacy conformance node', async () => {
  const input = makeK0SemanticConformanceInput0();
  const suite = makeKernelConformanceSuite0();
  input.LegacyConformance = {
    ...suite,
    nodes: suite.nodes.map((node, index) => (
      index === 0
        ? {
            ...node,
            Conclusion: {
              ...node.Conclusion,
              rule: 'Subst',
            },
          }
        : node
    )),
  };

  const out = await CheckK0SemanticConformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckK0SemanticConformance0.legacyConformance.exact',
  );
  assert.deepEqual(out.Path, ['LegacyConformance']);
  assert.equal(
    out.Witness.reason,
    'K0 semantic conformance requires the exact canonical legacy conformance suite',
  );
});

test('K0 semantic conformance rejects a stale primitive rule table', async () => {
  const input = makeK0SemanticConformanceInput0();
  input.KImpl.RuleTable = makeKernelRuleTable0().map((rule, index) => (
    index === 15
      ? { ...rule, modeSafe: false }
      : rule
  ));

  const out = await CheckK0SemanticConformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckK0SemanticConformance0.ruleTable.exact',
  );
  assert.deepEqual(out.Path, ['KImpl', 'RuleTable']);
});

test('K0 semantic conformance rejects caller-supplied readiness assertions', async () => {
  const input = makeK0SemanticConformanceInput0();
  input.semanticConformanceReady = true;
  input.mathematicalSoundness = true;

  const out = await CheckK0SemanticConformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckK0SemanticConformance0.input');
  assert.deepEqual(out.Path, ['semanticConformanceReady']);
  assert.equal(
    out.Witness.reason,
    'K0 semantic conformance rejects caller-supplied soundness or readiness assertions',
  );
});

test('K0 semantic conformance rejects a weakened checker binding', async () => {
  const input = makeK0SemanticConformanceInput0();
  input.Binding.finalProofChecker = 'CheckSemanticKernelProofTruthVec0';

  const out = await CheckK0SemanticConformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckK0SemanticConformance0.input');
  assert.deepEqual(out.Path, ['Binding']);
  assert.equal(
    out.Witness.reason,
    'K0 semantic conformance binding must match the executable checker boundary',
  );
});

test('K0 semantic conformance rejects a weakened fail-closed policy', async () => {
  const input = makeK0SemanticConformanceInput0();
  input.Policy.predecessorMustRejectUnimplementedRule = false;

  const out = await CheckK0SemanticConformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckK0SemanticConformance0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'K0 semantic conformance policy must match the fail-closed policy',
  );
});

test('K0 semantic conformance rejects when the final semantic KImpl proof is invalid', async () => {
  const term = makeSemanticConst0('k0.invalid', 'Term');
  const invalid = makeSemanticProofNode0({
    id: 'k0.invalid.finiterel',
    RuleName: 'FiniteRel',
    Conclusion: makeSemanticEqJudgment0(term, term),
    Payload: { op: 'verify' },
  });
  const input = makeK0SemanticConformanceInput0({
    SemanticProofDAG: makeSemanticProofDAG0([invalid]),
  });

  const out = await CheckK0SemanticConformance0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckK0SemanticConformance0.semanticKImpl');
  assert.equal(
    out.Witness.reason,
    'K0 semantic conformance requires an independently final-ready FiniteRel KImpl',
  );
});
