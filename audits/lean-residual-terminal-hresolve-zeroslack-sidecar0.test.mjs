import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH =
  'lean/PNP/ResidualTerminalHResolveZeroSlackSidecar.lean';
const ZEROSLACK_PATH = 'lean/PNP/ZeroSlack.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalHResolveZeroSlackSidecarAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalHResolveZeroSlackSidecar.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_hresolve_zeroslack_sidecar.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.HResolveSidecarCertificate.accepted`,
  `${NAMESPACE}.HResolveSidecarCertificate.not_exact`,
  `${NAMESPACE}.HResolveSidecarCertificate.not_gain`,
  `${NAMESPACE}.HResolveSidecarCertificate.blocked_of_mem`,
  `${NAMESPACE}.HResolveSidecarCertificate.exact_route_sound`,
  `${NAMESPACE}.HResolveSidecarCertificate.gain_route_sound`,
  `${NAMESPACE}.hresolve_zeroslack_sidecar_checked_complete`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function semanticText0(source) {
  return source.replace(/\s+/gu, ' ').trim();
}

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function requireTokens0(failures, block, category, tokens) {
  for (const token of tokens) {
    if (!block.includes(token)) failures.push(category);
  }
}

function validateSource0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit|noncomputable|unsafe)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) {
    failures.push('host-evaluation');
  }
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('unaudited-declaration-form');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/\bFin\s+[0-9]+\b/u.test(stripped)) failures.push('fixed-bound');
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|hresolve_global_complete|no_lower_ledger_complete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports,
    ['PNP.ResidualTerminalHResolveCoverageLedger']);

  const certificate = declarationBlock0(source,
    'HResolveSidecarCertificate');
  requireTokens0(failures, certificate, 'proof-bearing-certificate', [
    'Candidate : Type',
    'candidateDecidableEq : DecidableEq Candidate',
    'family : DirectWire.TerminalHResolveFamily Candidate',
    'implementation : Candidate → DirectWire.Implementation inputs outputs',
    'exact : Candidate → Prop',
    'gain : Candidate → Prop',
    'blocked : Candidate → Prop',
    'exactDecidable : DecidablePred exact',
    'gainDecidable : DecidablePred gain',
    'blockedDecidable : DecidablePred blocked',
    'checkNoHereditarySidecar',
    'exactMinimumRouteSound',
    'DirectWire.IsSemanticallyMinimum',
    'gainRouteSound',
    'DirectWire.StrictEquivalentGain',
  ]);
  if (/\bString\b/u.test(certificate)) failures.push('retained-string-handle');
  if (/\b[A-Za-z0-9_]*(?:accepted|success)[A-Za-z0-9_]*\s*:\s*Bool\b/iu.test(certificate)) {
    failures.push('caller-success-flag');
  }
  if (/noHereditarySidecar\s*:\s*Bool/u.test(certificate)) {
    failures.push('caller-success-flag');
  }
  if (!/checkNoHereditarySidecar[\s\S]*= true/u.test(certificate)) {
    failures.push('missing-checker-equation');
  }

  const accepted = declarationBlock0(source,
    'HResolveSidecarCertificate.accepted');
  requireTokens0(failures, accepted, 'accepted-reflection', [
    'NoHereditarySidecarAccepted',
    'checkNoHereditarySidecar_eq_true_iff',
    'certificate.noHereditarySidecar',
  ]);

  const exactSound = declarationBlock0(source,
    'HResolveSidecarCertificate.exact_route_sound');
  requireTokens0(failures, exactSound, 'exact-semantics', [
    'certificate.exact candidate',
    'DirectWire.IsSemanticallyMinimum',
    'certificate.exactMinimumRouteSound',
  ]);

  const gainSound = declarationBlock0(source,
    'HResolveSidecarCertificate.gain_route_sound');
  requireTokens0(failures, gainSound, 'gain-semantics', [
    'certificate.gain candidate',
    'DirectWire.StrictEquivalentGain',
    'certificate.gainRouteSound',
  ]);

  const endpoint = declarationBlock0(source,
    'hresolve_zeroslack_sidecar_checked_complete');
  requireTokens0(failures, endpoint, 'checked-endpoint', [
    'certificate.family.candidates.Nodup',
    '¬certificate.exact candidate',
    '¬certificate.gain candidate',
    'certificate.blocked candidate',
    'certificate.exact_route_sound',
    'certificate.gain_route_sound',
  ]);

  return [...new Set(failures)];
}

test('HResolve ZeroSlack sidecar is checked and proof-bearing', async () => {
  const [source, zeroSlack] = await Promise.all([
    text0(SOURCE_PATH), text0(ZEROSLACK_PATH),
  ]);
  assert.deepEqual(validateSource0(source), []);
  assert.match(zeroSlack,
    /^import PNP\.ResidualTerminalHResolveZeroSlackSidecar$/mu);
  assert.doesNotMatch(zeroSlack,
    /structure\s+HResolveSidecarCertificate[\s\S]{0,300}?String/u);
  assert.match(zeroSlack, /hResolve\s*:\s*HResolveSidecarCertificate/u);
});

test('axiom transcript follows every public declaration in source order', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
  assert.equal(expected.length, 8);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalHResolveZeroSlackSidecar\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalHResolveZeroSlackSidecar$/mu);
});

test('compiled inventory pins every reviewed HResolve ZeroSlack theorem', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const candidates = new Map(inventory.milestoneCandidates
    .map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of MILESTONE_THEOREMS) {
    const row = rows.get(name);
    assert.equal(row?.kind, 'theorem', name);
    for (const axiom of row.axioms) {
      assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    }
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
    assert.equal(row.axioms.includes('sorryAx'), false, name);
    assert.equal(typeof candidates.get(name)?.kernelType, 'string', name);
  }
});

test('regression covers checked evidence, semantic bindings, and rejection cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'checkedSidecar', 'blockedFamily', 'duplicateFamily', 'exactFamily',
    'gainFamily', 'unresolvedFamily', 'noHereditarySidecar := by decide',
    'fixtureMinimum_isSemanticallyMinimum', 'fixtureRedundantGain',
    'exact_route_sound', 'gain_route_sound', 'not_exact', 'not_gain',
    'blocked_of_mem', 'hresolve_zeroslack_sidecar_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the proof-bearing finite HResolve sidecar', async () => {
  const [publication, status, docs, readme, reconstruction, report,
    pipeline, auditQuestions, bridge, terminology] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH), text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'), text0('docs/audit_questions.md'),
    text0('docs/lean_bridge.md'), text0('docs/terminology_crosswalk.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-hresolve-zeroslack-sidecar');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-hresolve-zeroslack-sidecar');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /proof-bearing|checked.*NoHereditary|NoHereditary.*checked/iu);
  assert.match(milestone.scope,
    /semantic.*minimum|strict.*equivalent.*gain/iu);
  assert.match(milestone.nonClaim,
    /supplied.*family|supplied.*predicate|blocker semantics/iu);
  assert.match(milestone.nonClaim,
    /full.*HResolve|ZeroSlack|PCCMin|P = NP/iu);
  assert.equal(status.leanResidualTerminalHResolveZeroSlackSidecarFormalized,
    true);
  assert.equal(status.leanResidualTerminalHResolveZeroSlackSidecarAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalHResolveZeroSlackSidecarScope,
    /proof-bearing.*NoHereditary|NoHereditary.*proof-bearing/iu);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  for (const [name, text] of [
    ['docs', docs], ['README', readme], ['reconstruction', reconstruction],
    ['report', report], ['pipeline', pipeline],
    ['audit questions', auditQuestions], ['bridge', bridge],
    ['terminology', terminology],
  ]) {
    assert.match(semanticText0(text),
      /HResolve.*ZeroSlack|ZeroSlack.*HResolve|proof-bearing.*NoHereditary/iu,
      name);
    assert.match(semanticText0(text),
      /supplied.*family|not.*full.*HResolve|ZeroSlack.*remain/iu, name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalHResolveZeroSlackSidecarAxiomAudit\.lean[\s\S]{0,4500}?run: node --test audits\/lean-residual-terminal-hresolve-zeroslack-sidecar0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalHResolveZeroSlackSidecarAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalHResolveZeroSlackSidecar\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    ['string-handle', source.replace(
      'noHereditarySidecar :\n    @DirectWire.TerminalHResolveFamily.checkNoHereditarySidecar',
      'noHereditarySidecar : String\n  ignored :\n    @DirectWire.TerminalHResolveFamily.checkNoHereditarySidecar')],
    ['caller-success', source.replace(
      'noHereditarySidecar :\n    @DirectWire.TerminalHResolveFamily.checkNoHereditarySidecar',
      'sidecarAccepted : Bool\n  noHereditarySidecar :\n    @DirectWire.TerminalHResolveFamily.checkNoHereditarySidecar')],
    ['missing-checker', source.replaceAll(
      'checkNoHereditarySidecar', 'missingNoHereditaryCheck')],
    ['missing-exact-semantics', source.replaceAll(
      'DirectWire.IsSemanticallyMinimum', 'True')],
    ['missing-gain-semantics', source.replaceAll(
      'DirectWire.StrictEquivalentGain', 'And')],
    ['assumption', `${source}\naxiom hostileAssumption : False\n`],
    ['classical', source.replace('namespace PNP',
      'namespace PNP\nopen Classical')],
    ['fixed-bound', source.replace('inputs : Nat', 'inputs : Fin 7')],
    ['overclaim', `${source}\ntheorem zero_slack_complete : True := True.intro\n`],
  ];
  for (const [name, mutated] of mutations) {
    assert.notDeepEqual(validateSource0(mutated), [], name);
  }
});
