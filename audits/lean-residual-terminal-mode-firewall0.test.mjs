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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalModeFirewall.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalModeFirewallAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalModeFirewall.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_terminal_mode_firewall.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalProfileRole`,
  `${NAMESPACE}.TerminalProfile`,
  `${NAMESPACE}.TerminalProfileSystem`,
  `${NAMESPACE}.TerminalProfileProjection`,
  `${NAMESPACE}.TerminalProfileProjection.Keeps`,
  `${NAMESPACE}.TerminalProfileProjection.Forgets`,
  `${NAMESPACE}.TerminalProfileProjection.KeepsAll`,
  `${NAMESPACE}.TerminalProfileSystem.ObligationsDischarged`,
  `${NAMESPACE}.TerminalFullCarrierRealization`,
  `${NAMESPACE}.TerminalQuotientComparison`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project_realization`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project_implementation`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project_gateCount`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project_equivalent`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project_semantics`,
  `${NAMESPACE}.TerminalQuotientComparison.LostProfileAgreement`,
  `${NAMESPACE}.TerminalCheckedFullLift`,
  `${NAMESPACE}.TerminalCheckedFullLift.fullRealization`,
  `${NAMESPACE}.TerminalCheckedFullLift.fullRealization_realization`,
  `${NAMESPACE}.TerminalCheckedFullLift.fullRealization_profileEqual`,
  `${NAMESPACE}.TerminalFullCarrierRealization.checkedFullLift`,
  `${NAMESPACE}.TerminalQuotientComparison.FullProfileEqual`,
  `${NAMESPACE}.terminalCheckedFullLift_iff_fullProfileEqual`,
  `${NAMESPACE}.TerminalQuotientComparison.checkedFullLift_of_keepsAll`,
  `${NAMESPACE}.TerminalFullCarrierRealization.obligationsDischarged`,
  `${NAMESPACE}.TerminalCheckedFullLift.obligationsDischarged`,
  `${NAMESPACE}.TerminalQuotientComparison.ForgottenMismatch`,
  `${NAMESPACE}.terminalQuotientEqualityNotConstructive`,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalFullCarrierRealization.project_realization`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project_implementation`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project_gateCount`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project_equivalent`,
  `${NAMESPACE}.TerminalFullCarrierRealization.project_semantics`,
  `${NAMESPACE}.TerminalCheckedFullLift.fullRealization_realization`,
  `${NAMESPACE}.TerminalCheckedFullLift.fullRealization_profileEqual`,
  `${NAMESPACE}.terminalCheckedFullLift_iff_fullProfileEqual`,
  `${NAMESPACE}.TerminalQuotientComparison.checkedFullLift_of_keepsAll`,
  `${NAMESPACE}.TerminalFullCarrierRealization.obligationsDischarged`,
  `${NAMESPACE}.TerminalCheckedFullLift.obligationsDischarged`,
  `${NAMESPACE}.terminalQuotientEqualityNotConstructive`,
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
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasPrivateLeanDeclaration0(source)) failures.push('private-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag|projectionSound|fullLiftComplete)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|projectionDefectMinimum|saturatePositive|completeGainRoute|zeroSlackComplete)\b/u.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateFirewallSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(['PNP.ResidualTerminalFullBridge'])) {
    failures.push('closed-import');
  }
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }

  const roles = declarationBlock0(source, 'TerminalProfileRole');
  const system = declarationBlock0(source, 'TerminalProfileSystem');
  const full = declarationBlock0(source, 'TerminalFullCarrierRealization');
  const quotient = declarationBlock0(source, 'TerminalQuotientComparison');
  const project = declarationBlock0(source, 'TerminalFullCarrierRealization.project');
  const lift = declarationBlock0(source, 'TerminalCheckedFullLift');
  const liftRealization = declarationBlock0(source, 'TerminalCheckedFullLift.fullRealization');
  const liftIff = declarationBlock0(source, 'terminalCheckedFullLift_iff_fullProfileEqual');
  const obligationDefinition = declarationBlock0(
    source, 'TerminalProfileSystem.ObligationsDischarged',
  );
  const obligations = declarationBlock0(source, 'TerminalCheckedFullLift.obligationsDischarged');
  const mismatch = declarationBlock0(source, 'TerminalQuotientComparison.ForgottenMismatch');
  const firewall = declarationBlock0(source, 'terminalQuotientEqualityNotConstructive');

  for (const role of [
    'carrier', 'origin', 'kernel', 'obligation', 'prefix', 'direction',
    'saturation', 'budget', 'charge', 'frontier',
  ]) if (!new RegExp(`\\| ${role}\\b`, 'u').test(roles)) failures.push(`role-${role}`);
  if (!/role\s*:\s*Fin profileWidth → TerminalProfileRole[\s\S]*observe\s*:\s*Implementation inputs outputs → TerminalProfile profileWidth/u.test(system)) {
    failures.push('computed-profile-system');
  }
  if (!/realization\s*:\s*TerminalFullRealization current[\s\S]*profileEqual\s*:\s*∀ coordinate,[\s\S]*system\.observe realization\.implementation coordinate =[\s\S]*system\.observe current coordinate/u.test(full)) {
    failures.push('complete-full-profile');
  }
  if (!/realization\s*:\s*TerminalFullRealization current[\s\S]*keptProfileEqual\s*:\s*∀ coordinate,[\s\S]*projection\.Keeps coordinate/u.test(quotient)) {
    failures.push('comparison-only-quotient');
  }
  if (!/realization := full\.realization[\s\S]*full\.profileEqual coordinate/u.test(project)) {
    failures.push('exact-projection');
  }
  if (!/lostProfileAgreement\s*:\s*comparison\.LostProfileAgreement/u.test(lift)) {
    failures.push('explicit-lost-profile');
  }
  if (!/cases kept : projection\.keep coordinate[\s\S]*lift\.lostProfileAgreement coordinate kept[\s\S]*comparison\.keptProfileEqual coordinate kept/u.test(liftRealization)) {
    failures.push('full-lift-covers-both-modes');
  }
  if (!/TerminalCheckedFullLift comparison ↔ comparison\.FullProfileEqual[\s\S]*lift\.fullRealization\.profileEqual/u.test(liftIff)) {
    failures.push('lift-iff-full-profile');
  }
  if (!/system\.role coordinate = \.obligation →[\s\S]*system\.observe implementation coordinate = false/u.test(obligationDefinition) ||
      !/system\.ObligationsDischarged comparison\.realization\.implementation[\s\S]*fullRealization\.obligationsDischarged/u.test(obligations)) {
    failures.push('obligation-discharge');
  }
  if (!/∃ coordinate,[\s\S]*projection\.Forgets coordinate[\s\S]*system\.observe comparison\.realization\.implementation coordinate ≠/u.test(mismatch)) {
    failures.push('forgotten-mismatch');
  }
  if (!/¬TerminalCheckedFullLift comparison[\s\S]*lift\.lostProfileAgreement coordinate forgotten/u.test(firewall)) {
    failures.push('quotient-not-constructive');
  }
  return failures;
}

test('terminal mode firewall exposes the exact finite-profile interface', async () => {
  assert.deepEqual(validateFirewallSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all public declarations exactly once', async () => {
  assert.deepEqual(printed0(await text0(AUDIT_PATH)), PUBLIC_DECLARATIONS);
  assert.equal(new Set(PUBLIC_DECLARATIONS).size, PUBLIC_DECLARATIONS.length);
  assert.equal(PUBLIC_DECLARATIONS.length, 29);
  assert.match(await text0('lean/PNP.lean'), /^import PNP\.ResidualTerminalModeFirewall$/mu);
});

test('compiled closure is approved for every terminal firewall declaration', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of PUBLIC_DECLARATIONS) {
    const row = rows.get(name);
    assert.ok(row, name);
    for (const axiom of row.axioms) assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
  }
});

test('regression covers dropped, lossless, empty, obligation, and semantic cases', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'terminalModeDroppedComparison_mismatch',
    'terminalQuotientEqualityNotConstructive',
    'terminalModeRedundantFullRealization',
    'project_gateCount',
    'project_semantics',
    'checkedFullLift_of_keepsAll',
    'terminalModeObligationSystem',
    'terminalModeCurrentObligationsDischarged',
    'terminalModeEmptyProfileSystem',
    'terminalCheckedFullLift_iff_fullProfileEqual',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression), /\b(?:Classical(?:\.choice)?|native_decide|sorry|admit)\b/u);
});

test('status retains the terminal quotient/full mode firewall beneath its earned successor', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanResidualTerminalQuotientCarrierFormalized',
    'leanResidualTerminalModeFirewallFormalized',
    'leanResidualTerminalModeFirewallAxiomAuditPassed',
    'leanResidualTerminalProfileProjectionExactFormalized',
    'leanResidualTerminalCheckedFullLiftFormalized',
    'leanResidualTerminalQuotientEqualityNotConstructiveFormalized',
    'leanResidualTerminalObligationDischargePreservedFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanResidualTerminalModeFirewallScope,
    'all-finite-direct-wire-implementations-with-computed-finite-profile-observers-and-explicit-forgetful-projections');
  assert.equal(status.leanResidualProjectionMinimumFormalized, true);
  assert.equal(status.leanResidualTerminalSaturationFormalized, true);
  for (const field of [
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalProperSupportSearchCompleteFormalized',
    'leanResidualTerminalProperSupportExactLocalGainFormalized',
    'leanResidualTerminalProperSupportAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  for (const field of [
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-terminal-mode-firewall',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation records the legacy anchor and exact downstream boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§§5.1–5.2', 'quotientEqualityNotConstructive', 'ten roles',
    'complete multi-output semantics', 'forgotten coordinate', 'checked full lift',
    'proper or governed support', 'SaturatePositive', 'ZeroSlack', 'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-terminal-mode-firewall0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualTerminalModeFirewallAxiomAudit\.lean[\s\S]{0,1200}does not depend on any axioms[\s\S]{0,300}-eq 29/u);
  assert.match(workflow, /lean-regression\/PNPResidualTerminalModeFirewall\.lean/u);
});

test('hostile mutations revoke projection, lifting, obligation, and firewall credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateFirewallSource0(source.replace(
    'realization := full.realization',
    'realization := terminalize current',
  )).includes('exact-projection'), true);
  assert.equal(validateFirewallSource0(source.replace(
    'lostProfileAgreement : comparison.LostProfileAgreement',
    'lostProfileAgreement : True',
  )).includes('explicit-lost-profile'), true);
  assert.equal(validateFirewallSource0(source.replace(
    'lift.lostProfileAgreement coordinate kept',
    'comparison.keptProfileEqual coordinate kept',
  )).includes('full-lift-covers-both-modes'), true);
  assert.equal(validateFirewallSource0(source.replace(
    'system.observe implementation coordinate = false',
    'system.observe implementation coordinate = true',
  )).includes('obligation-discharge'), true);
  assert.equal(validateFirewallSource0(source.replace(
    'lift.lostProfileAgreement coordinate forgotten',
    'comparison.keptProfileEqual coordinate forgotten',
  )).includes('quotient-not-constructive'), true);
  assert.equal(validateFirewallSource0(`import PNP.ZeroSlack\n${source}`).includes('closed-import'), true);
  assert.equal(validateFirewallSource0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateFirewallSource0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-declaration'), true);
  assert.equal(validateFirewallSource0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateFirewallSource0(`${source}\ntheorem hidden : True := by native_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateFirewallSource0(`${source}\ndef callerCertificate := true\n`).includes('caller-or-host-certificate'), true);
  assert.equal(validateFirewallSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`).includes('overclaim'), true);
});
