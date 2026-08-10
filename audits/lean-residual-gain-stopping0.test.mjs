import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasPrivateLeanDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH = 'lean/PNP/ResidualGainStopping.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualGainStoppingAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualGainStopping.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_gain_stopping.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.referenceMinimumImplementation_gateCount_eq_referenceMinimum`,
  `${NAMESPACE}.referenceMinimumImplementation_equivalent`,
  `${NAMESPACE}.referenceMinimumImplementation_isSemanticallyMinimum`,
  `${NAMESPACE}.referenceMinimumImplementation_residualSlack_eq_zero`,
  `${NAMESPACE}.referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos`,
  `${NAMESPACE}.residualSlack_pos_iff_exists_strictEquivalentGain`,
  `${NAMESPACE}.residualSlack_eq_zero_iff_forall_not_strictEquivalentGain`,
  `${NAMESPACE}.isSemanticallyMinimum_iff_forall_not_strictEquivalentGain`,
  `${NAMESPACE}.StrictGainChain.end_residualSlack_eq_zero_of_no_strictEquivalentGain`,
  `${NAMESPACE}.StrictGainChain.end_exactMinimumResult_of_no_strictEquivalentGain`,
  `${NAMESPACE}.strictGainChainBool_end_residualSlack_eq_zero_of_no_strictEquivalentGain`,
  `${NAMESPACE}.strictGainChainBool_end_exactMinimumResult_of_no_strictEquivalentGain`,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.referenceMinimumImplementation_gateCount_eq_referenceMinimum`,
  `${NAMESPACE}.referenceMinimumImplementation_equivalent`,
  `${NAMESPACE}.referenceMinimumImplementation_isSemanticallyMinimum`,
  `${NAMESPACE}.referenceMinimumImplementation_residualSlack_eq_zero`,
  `${NAMESPACE}.referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos`,
  `${NAMESPACE}.residualSlack_pos_iff_exists_strictEquivalentGain`,
  `${NAMESPACE}.residualSlack_eq_zero_iff_forall_not_strictEquivalentGain`,
  `${NAMESPACE}.isSemanticallyMinimum_iff_forall_not_strictEquivalentGain`,
  `${NAMESPACE}.StrictGainChain.end_residualSlack_eq_zero_of_no_strictEquivalentGain`,
  `${NAMESPACE}.strictGainChainBool_end_residualSlack_eq_zero_of_no_strictEquivalentGain`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `${NAMESPACE}.${head.name}`);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function commonFailures0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:Classical(?:\.choice)?|native_decide|exact_mod_cast|linarith|nlinarith|sorry|admit)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) {
    failures.push('host-evaluation');
  }
  if (hasLeanAssumptionDeclaration0(source)) {
    failures.push('assumption-declaration');
  }
  if (hasPrivateLeanDeclaration0(source)) {
    failures.push('private-declaration');
  }
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('unaudited-declaration-form');
  }
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|polynomialGainGenerator|completeGainRoute|pccminPolynomialExact|zeroSlackComplete)\b/u.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateStoppingSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(['PNP.ResidualGainChain'])) {
    failures.push('closed-import');
  }
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }

  const positive = declarationBlock0(
    source, 'residualSlack_pos_iff_exists_strictEquivalentGain',
  );
  const zero = declarationBlock0(
    source, 'residualSlack_eq_zero_iff_forall_not_strictEquivalentGain',
  );
  const minimum = declarationBlock0(
    source, 'isSemanticallyMinimum_iff_forall_not_strictEquivalentGain',
  );
  const chainZero = declarationBlock0(
    source,
    'StrictGainChain.end_residualSlack_eq_zero_of_no_strictEquivalentGain',
  );
  const chainExact = declarationBlock0(
    source,
    'StrictGainChain.end_exactMinimumResult_of_no_strictEquivalentGain',
  );
  const boolZero = declarationBlock0(
    source,
    'strictGainChainBool_end_residualSlack_eq_zero_of_no_strictEquivalentGain',
  );
  const boolExact = declarationBlock0(
    source,
    'strictGainChainBool_end_exactMinimumResult_of_no_strictEquivalentGain',
  );
  const referenceWitness = declarationBlock0(
    source,
    'referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos',
  );

  if (!/0 < residualSlack current ↔[\s\S]*∃ next : Implementation inputs outputs,[\s\S]*StrictEquivalentGain current next/u.test(positive)) {
    failures.push('positive-global-existence');
  }
  if (!/residualSlack current = 0 ↔[\s\S]*∀ next : Implementation inputs outputs,[\s\S]*¬StrictEquivalentGain current next/u.test(zero)) {
    failures.push('zero-global-absence');
  }
  if (!/IsSemanticallyMinimum current ↔[\s\S]*∀ next : Implementation inputs outputs,[\s\S]*¬StrictEquivalentGain current next/u.test(minimum)) {
    failures.push('minimum-global-absence');
  }
  if (!/StrictEquivalentGain current \(referenceMinimumImplementation current\)/u.test(referenceWitness)) {
    failures.push('reference-minimum-witness');
  }
  for (const block of [chainZero, chainExact, boolZero, boolExact]) {
    if (!/noGain : ∀ next : Implementation inputs outputs,[\s\S]*¬StrictEquivalentGain \(gainChainEnd current chain\) next/u.test(block)) {
      failures.push('endpoint-global-premise');
    }
  }
  if (!/ExactMinimumResult current/u.test(chainExact)
      || !/ExactMinimumResult current/u.test(boolExact)) {
    failures.push('exact-result-packaging');
  }
  if (/\b(?:firstListedGain|scanListedGains|UnresolvedResult|listedCandidates)\b/u.test(stripLeanCommentsAndStrings0(source))) {
    failures.push('finite-list-stopping');
  }
  return failures;
}

test('global strict-gain stopping source exposes the exact semantic interface', async () => {
  assert.deepEqual(validateStoppingSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all 12 public declarations exactly once', async () => {
  assert.deepEqual(printed0(await text0(AUDIT_PATH)), PUBLIC_DECLARATIONS);
  assert.equal(new Set(PUBLIC_DECLARATIONS).size, 12);
  const root = await text0('lean/PNP.lean');
  assert.match(root, /^import PNP\.ResidualGainStopping$/mu);
});

test('compiled closure is empty for every stopping declaration', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(
    inventory.declarations.map((entry) => [entry.name, entry]),
  );
  for (const name of PUBLIC_DECLARATIONS) {
    assert.deepEqual(rows.get(name)?.axioms, [], name);
  }
});

test('regression covers reference witnesses, both global directions, and both chain interfaces', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'stoppingZeroGateIdentityNoStrictGain',
    'stoppingRedundantToIdentityGain',
    'residualSlack_pos_iff_exists_strictEquivalentGain',
    'residualSlack_eq_zero_iff_forall_not_strictEquivalentGain',
    'isSemanticallyMinimum_iff_forall_not_strictEquivalentGain',
    'end_residualSlack_eq_zero_of_no_strictEquivalentGain',
    'end_exactMinimumResult_of_no_strictEquivalentGain',
    'strictGainChainBool_end_residualSlack_eq_zero_of_no_strictEquivalentGain',
    'strictGainChainBool_end_exactMinimumResult_of_no_strictEquivalentGain',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(
    stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|sorry|admit)\b/u,
  );
});

test('status earns only the semantic stopping specification', async () => {
  const status = JSON.parse(
    await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  );
  for (const field of [
    'leanResidualGainStoppingSpecificationFormalized',
    'leanResidualGainStoppingAxiomAuditPassed',
    'leanResidualGainReferenceMinimumWitnessFormalized',
    'leanResidualGainPositiveIffGlobalStrictGainFormalized',
    'leanResidualGainZeroIffGlobalNoStrictGainFormalized',
    'leanResidualGainSemanticMinimumIffGlobalNoStrictGainFormalized',
    'leanResidualGainChainGlobalStoppingConsequenceFormalized',
    'leanResidualGainChainExactMinimumPackagingFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualGainStoppingScope,
    'all-finite-direct-wire-implementations-with-global-strict-equivalent-gain-quantification-and-proof-supplied-chain-endpoint-stopping',
  );
  for (const field of [
    'leanResidualRoutesCandidateListCompletenessFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanResidualGainChainPolynomialRuntimeFormalized',
    'leanZeroSlackPositiveSlackContradictionFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
    'leanResidualBandMinimizerFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-gain-stopping-specification',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation records the legacy stopping edge and exact non-claims', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§16',
    'positive residual slack',
    'strict equivalent gain',
    'global absence',
    'semantic minimality',
    'finite candidate list',
    'route completeness',
    'polynomial runtime',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-gain-stopping0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualGainStoppingAxiomAudit\.lean[\s\S]{0,1200}does not depend on any axioms[\s\S]{0,300}-eq 12/u);
  assert.match(workflow, /lean-regression\/PNPResidualGainStopping\.lean/u);
});

test('hostile mutations revoke global quantification, strictness, closure, and scope credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateStoppingSource0(source.replace(
    '∃ next : Implementation inputs outputs,',
    '∃ next : Implementation 1 outputs,',
  )).includes('positive-global-existence'), true);
  assert.equal(validateStoppingSource0(source.replace(
    '∀ next : Implementation inputs outputs,\n        ¬StrictEquivalentGain current next',
    '∀ next : Implementation inputs outputs,\n        True',
  )).includes('zero-global-absence'), true);
  assert.equal(validateStoppingSource0(source.replace(
    'StrictEquivalentGain current (referenceMinimumImplementation current)',
    'True',
  )).includes('reference-minimum-witness'), true);
  assert.equal(validateStoppingSource0(source.replace(
    '¬StrictEquivalentGain (gainChainEnd current chain) next',
    'True',
  )).includes('endpoint-global-premise'), true);
  assert.equal(validateStoppingSource0(`import PNP.ZeroSlack\n${source}`)
    .includes('closed-import'), true);
  assert.equal(validateStoppingSource0(`${source}\naxiom hidden : True\n`)
    .includes('assumption-declaration'), true);
  assert.equal(validateStoppingSource0(`${source}\nprivate theorem hidden : True := True.intro\n`)
    .includes('private-declaration'), true);
  assert.equal(validateStoppingSource0(`${source}\nexample : True := True.intro\n`)
    .includes('unaudited-declaration-form'), true);
  assert.equal(validateStoppingSource0(`${source}\ntheorem hidden : True := by native_decide\n`)
    .includes('forbidden-shortcut'), true);
  assert.equal(validateStoppingSource0(`${source}\ndef hostLookup := true\n`)
    .includes('caller-or-host-certificate'), true);
  assert.equal(validateStoppingSource0(`${source}\naxiom useProject : PNP.LockedNANDThreshold\n`)
    .includes('project-axiom'), true);
  assert.equal(validateStoppingSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`)
    .includes('overclaim'), true);
  assert.equal(validateStoppingSource0(`${source}\ndef firstListedGain := true\n`)
    .includes('finite-list-stopping'), true);
  assert.notDeepEqual(
    printed0(await text0(AUDIT_PATH)).slice(0, -1),
    PUBLIC_DECLARATIONS,
  );
  assert.notDeepEqual(
    declarations0(`${source}\ntheorem extra : True := True.intro\n`),
    PUBLIC_DECLARATIONS,
  );
});
