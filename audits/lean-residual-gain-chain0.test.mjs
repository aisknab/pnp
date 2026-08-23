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
const CHAIN_SOURCE_PATH = 'lean/PNP/ResidualGainChain.lean';
const LOCKED_SOURCE_PATH = 'lean/PNP/LockedNANDResidualGainBound.lean';
const CHAIN_AUDIT_PATH = 'lean-audit/PNPResidualGainChainAxiomAudit.lean';
const LOCKED_AUDIT_PATH =
  'lean-audit/PNPLockedNANDResidualGainBoundAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualGainChain.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_gain_chain.md';
const CHAIN_NAMESPACE = 'PNP.DirectWire';
const LOCKED_NAMESPACE =
  'PNP.DirectWire.LockedNANDGlobalCandidates';

const CHAIN_DECLARATIONS = Object.freeze([
  `${CHAIN_NAMESPACE}.StrictGainChain`,
  `${CHAIN_NAMESPACE}.strictGainChainBool`,
  `${CHAIN_NAMESPACE}.gainChainEnd`,
  `${CHAIN_NAMESPACE}.strictGainChainBool_eq_true_iff`,
  `${CHAIN_NAMESPACE}.StrictGainChain.end_equivalent`,
  `${CHAIN_NAMESPACE}.StrictGainChain.end_referenceMinimum_eq`,
  `${CHAIN_NAMESPACE}.StrictGainChain.end_residualSlack_add_length_le`,
  `${CHAIN_NAMESPACE}.StrictGainChain.length_le_residualSlack`,
  `${CHAIN_NAMESPACE}.strictGainChainBool_length_le_residualSlack`,
  `${CHAIN_NAMESPACE}.strictGainChainBool_length_le_of_residualSlack_le`,
  `${CHAIN_NAMESPACE}.StrictGainChain.eq_nil_of_residualSlack_eq_zero`,
  `${CHAIN_NAMESPACE}.strictGainChainBool_eq_nil_of_residualSlack_eq_zero`,
]);

const LOCKED_DECLARATIONS = Object.freeze([
  `${LOCKED_NAMESPACE}.fullCandidateImplementation`,
  `${LOCKED_NAMESPACE}.fullCandidateImplementation_residualSlack_le_four`,
  `${LOCKED_NAMESPACE}.fullCandidate_strictGainChain_length_le_four`,
  `${LOCKED_NAMESPACE}.fullCandidate_strictGainChainBool_length_le_four`,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${CHAIN_NAMESPACE}.StrictEquivalentGain.strictResidualDescent`,
  ...CHAIN_DECLARATIONS.slice(3),
  `${LOCKED_NAMESPACE}.fullCandidate_residualSlack_le_four`,
  ...LOCKED_DECLARATIONS.slice(1),
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source, namespace) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => `${namespace}.${head.name}`);
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
  if (/(?:def|theorem)\s+(?:p_eq_np|polynomialGainGenerator|completeGainRoute|pccminPolynomialExact)\b/u.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateChainSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(['PNP.ResidualRoutes'])) {
    failures.push('closed-import');
  }
  if (JSON.stringify(declarations0(source, CHAIN_NAMESPACE)) !==
      JSON.stringify(CHAIN_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const predicate = declarationBlock0(source, 'StrictGainChain');
  const checker = declarationBlock0(source, 'strictGainChainBool');
  const end = declarationBlock0(source, 'gainChainEnd');
  const aggregate = declarationBlock0(
    source, 'StrictGainChain.end_residualSlack_add_length_le',
  );
  if (!/StrictEquivalentGain current next ∧ StrictGainChain next remaining/u.test(predicate)) {
    failures.push('predicate-adjacency');
  }
  if (!/strictEquivalentGainBool current next &&[\s\S]*strictGainChainBool next remaining/u.test(checker)) {
    failures.push('checker-adjacency');
  }
  if (!/\| _current, next :: remaining => gainChainEnd next remaining/u.test(end)) {
    failures.push('endpoint-threading');
  }
  if (!/residualSlack \(gainChainEnd current chain\) \+ chain\.length ≤[\s\S]*residualSlack current/u.test(aggregate)) {
    failures.push('aggregate-residual-bound');
  }
  if (/\b(?:scanEquivalentSizes|referenceMinimumImplementation|firstEquivalentAt|ZeroSlackResult)\b/u.test(stripLeanCommentsAndStrings0(source))) {
    failures.push('exact-search-or-zeroslack');
  }
  if (/≤\s*4\b/u.test(stripLeanCommentsAndStrings0(source))) {
    failures.push('hard-coded-family-bound');
  }
  return failures;
}

function validateLockedSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualGainChain',
    'PNP.LockedNANDGlobalSemanticThreshold',
  ])) {
    failures.push('closed-import');
  }
  if (JSON.stringify(declarations0(source, LOCKED_NAMESPACE)) !==
      JSON.stringify(LOCKED_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const slack = declarationBlock0(
    source, 'fullCandidateImplementation_residualSlack_le_four',
  );
  const proofChain = declarationBlock0(
    source, 'fullCandidate_strictGainChain_length_le_four',
  );
  const checkedChain = declarationBlock0(
    source, 'fullCandidate_strictGainChainBool_length_le_four',
  );
  if (!/fullCandidate_residualSlack_le_four circuit/u.test(slack)) {
    failures.push('missing-global-slack-dependency');
  }
  for (const block of [slack, proofChain, checkedChain]) {
    if (!/≤\s*4/u.test(block)) failures.push('missing-four-step-bound');
  }
  if (!/strictGainChainBool_length_le_residualSlack checked/u.test(checkedChain)) {
    failures.push('missing-executable-bound-transport');
  }
  return failures;
}

test('gain-chain sources expose the exact bounded, fail-closed interface', async () => {
  assert.deepEqual(validateChainSource0(await text0(CHAIN_SOURCE_PATH)), []);
  assert.deepEqual(validateLockedSource0(await text0(LOCKED_SOURCE_PATH)), []);
});

test('axiom transcripts cover every public declaration exactly once', async () => {
  assert.deepEqual(
    printed0(await text0(CHAIN_AUDIT_PATH)), CHAIN_DECLARATIONS,
  );
  assert.deepEqual(
    printed0(await text0(LOCKED_AUDIT_PATH)), LOCKED_DECLARATIONS,
  );
  assert.equal(new Set(CHAIN_DECLARATIONS).size, 12);
  assert.equal(new Set(LOCKED_DECLARATIONS).size, 4);
  const root = await text0('lean/PNP.lean');
  assert.match(root, /^import PNP\.ResidualGainChain$/mu);
  assert.match(root, /^import PNP\.LockedNANDResidualGainBound$/mu);
});

test('compiled closures are empty generically and Lean-standard for locked candidates', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(
    inventory.declarations.map((entry) => [entry.name, entry]),
  );
  for (const name of CHAIN_DECLARATIONS) {
    assert.deepEqual(rows.get(name)?.axioms, [], name);
  }
  for (const name of LOCKED_DECLARATIONS) {
    assert.deepEqual(rows.get(name)?.axioms, ['Quot.sound', 'propext'], name);
  }
});

test('regression covers accepted, rejected, endpoint, zero-slack, and locked cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'redundantOneStepChain',
    'strictGainChainBool_eq_true_iff',
    'gainChainEnd',
    'strictGainChainBool redundantIdentityImplementation',
    'strictGainChainBool zeroGateIdentityImplementation',
    'strictGainChainBool notImplementation',
    '¬StrictGainChain redundantIdentityImplementation [middle, finish]',
    'fullCandidate_strictGainChainBool_length_le_four',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(
    stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|sorry|admit)\b/u,
  );
});

test('status earns only the universal verified iteration bound', async () => {
  const status = JSON.parse(
    await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  );
  for (const field of [
    'leanResidualGainChainVerifierFormalized',
    'leanResidualGainChainAxiomAuditPassed',
    'leanResidualGainChainSemanticInvariantFormalized',
    'leanResidualGainChainSlackIterationBoundFormalized',
    'leanLockedNANDGainIterationsAtMostFourFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualGainChainScope,
    'all-finite-proof-bearing-or-executably-verified-strict-equivalent-gain-chains-with-locked-family-four-step-specialization',
  );
  for (const field of [
    'leanResidualGainChainPolynomialRuntimeFormalized',
    'leanResidualRoutesCandidateListCompletenessFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackPositiveSlackContradictionFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
    'leanResidualBandMinimizerFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length > 0, status.projectSpecificAxiomsRemaining);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-gain-chain-bound',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation records the legacy anchor and exact non-claims', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§16',
    '§17',
    'strict equivalent gain',
    'residual slack',
    'at most four',
    'does not find',
    'route completeness',
    'polynomial runtime',
    'ZeroSlack',
    'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs both transcripts, the regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-gain-chain0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualGainChainAxiomAudit\.lean[\s\S]{0,1200}does not depend on any axioms[\s\S]{0,300}-eq 12/u);
  assert.match(workflow, /PNPLockedNANDResidualGainBoundAxiomAudit\.lean[\s\S]{0,1500}-eq 4/u);
  assert.match(workflow, /lean-regression\/PNPResidualGainChain\.lean/u);
});

test('hostile mutations revoke adjacency, descent, boundary, and closure credit', async () => {
  const source = await text0(CHAIN_SOURCE_PATH);
  const locked = await text0(LOCKED_SOURCE_PATH);
  assert.equal(validateChainSource0(source.replace(
    'StrictEquivalentGain current next ∧ StrictGainChain next remaining',
    'True ∧ StrictGainChain next remaining',
  )).includes('predicate-adjacency'), true);
  assert.equal(validateChainSource0(source.replace(
    'strictEquivalentGainBool current next &&',
    'strictEquivalentGainBool current next ||',
  )).includes('checker-adjacency'), true);
  assert.equal(validateChainSource0(source.replace(
    'strictGainChainBool next remaining',
    'strictGainChainBool current remaining',
  )).includes('checker-adjacency'), true);
  assert.equal(validateChainSource0(source.replace(
    'gainChainEnd next remaining',
    'gainChainEnd current remaining',
  )).includes('endpoint-threading'), true);
  assert.equal(validateChainSource0(`import PNP.ZeroSlack\n${source}`)
    .includes('closed-import'), true);
  assert.equal(validateChainSource0(`${source}\naxiom hidden : True\n`)
    .includes('assumption-declaration'), true);
  assert.equal(validateChainSource0(`${source}\nprivate theorem hidden : True := True.intro\n`)
    .includes('private-declaration'), true);
  assert.equal(validateChainSource0(`${source}\nexample : True := True.intro\n`)
    .includes('unaudited-declaration-form'), true);
  assert.equal(validateChainSource0(`${source}\ntheorem hidden : True := by native_decide\n`)
    .includes('forbidden-shortcut'), true);
  assert.equal(validateChainSource0(`${source}\ndef hostLookup := true\n`)
    .includes('caller-or-host-certificate'), true);
  assert.equal(validateChainSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`)
    .includes('overclaim'), true);
  assert.equal(validateChainSource0(`${source}\ndef scanEquivalentSizes := true\n`)
    .includes('exact-search-or-zeroslack'), true);
  assert.equal(validateLockedSource0(locked.replaceAll('≤ 4', '≤ 5'))
    .includes('missing-four-step-bound'), true);
  assert.equal(validateLockedSource0(locked.replace(
    'fullCandidate_residualSlack_le_four circuit',
    'by omega',
  )).includes('missing-global-slack-dependency'), true);
  assert.notDeepEqual(
    printed0(await text0(CHAIN_AUDIT_PATH)).slice(0, -1),
    CHAIN_DECLARATIONS,
  );
  assert.notDeepEqual(
    declarations0(`${locked}\ntheorem extra : True := True.intro\n`,
      LOCKED_NAMESPACE),
    LOCKED_DECLARATIONS,
  );
});
