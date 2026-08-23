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
  'lean/PNP/ResidualTerminalZeroSlackPacketSelectorHBCoherence.lean';
const ZEROSLACK_PATH = 'lean/PNP/ZeroSlack.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalZeroSlackPacketSelectorHBCoherenceAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalZeroSlackPacketSelectorHBCoherence.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_zeroslack_packet_selector_hb_coherence.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.selector_silence_accepted`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.hb_closure_accepted`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_family`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_realizerTable`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_dependencyTable`,
  `${NAMESPACE}.packet_selector_hb_bcel_coherent_checked_complete`,
  `${NAMESPACE}.zeroslack_packet_selector_hb_bcel_coherent_checked_complete`,
]);

const AXIOM_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.computedSelectorHBTable`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.selector_silence_accepted`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.hb_closure_accepted`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_family`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_realizerTable`,
  `${NAMESPACE}.PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_dependencyTable`,
  `${NAMESPACE}.packet_selector_hb_bcel_coherent_checked_complete`,
  `${NAMESPACE}.ZeroSlackCertificate.selectorHBClosure`,
  `${NAMESPACE}.PCCOracleCertificate.selectorHBClosure`,
  `${NAMESPACE}.zeroslack_packet_selector_hb_bcel_coherent_checked_complete`,
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|positive_residual_yields_bcelready)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }

  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalSelectorHBZeroSlackSidecar',
    'PNP.ResidualTerminalBCELPacketNoLowerZeroSlackSidecar',
  ]);

  const computed = declarationBlock0(source,
    'PacketBudgetNoLowerZeroSlackSidecarCertificate.computedSelectorHBTable');
  requireTokens0(failures, computed, 'exact-computed-table', [
    'certificate.table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness',
    'certificate.beforeRank certificate.afterRank',
  ]);

  const silence = declarationBlock0(source,
    'PacketBudgetNoLowerZeroSlackSidecarCertificate.selector_silence_accepted');
  requireTokens0(failures, silence, 'derived-selector-silence', [
    'certificate.computedSelectorHBTable.checkSelectorSilent = true',
    'certificate.accepted.2.2.2.1',
  ]);

  const closure = declarationBlock0(source,
    'PacketBudgetNoLowerZeroSlackSidecarCertificate.hb_closure_accepted');
  requireTokens0(failures, closure, 'derived-hb-closure', [
    'certificate.dependencyTable.checkNoOutcomeActiveClosure',
    'certificate.computedSelectorHBTable.environment = true',
    'certificate.accepted.2.2.2.2.1',
  ]);

  const selectorHB = declarationBlock0(source,
    'PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB');
  requireTokens0(failures, selectorHB, 'structural-coherence', [
    'Atom := certificate.Anchor',
    'family := certificate.family',
    'realizerTable := certificate.computedSelectorHBTable',
    'dependencyTable := certificate.dependencyTable',
    'selectorSilenceAccepted := certificate.selector_silence_accepted',
    'hbClosureAccepted := certificate.hb_closure_accepted',
  ]);
  if (/\b(?:coherence|sameFamily|sameTable|sameDependency|digest|hash)\w*\s*:/iu.test(selectorHB)) {
    failures.push('caller-coherence-proof');
  }
  if (/\b(?:accepted|success)\w*\s*:\s*Bool\b/iu.test(selectorHB)) {
    failures.push('caller-success-flag');
  }

  for (const [name, target] of [
    ['PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_family',
      'certificate.selectorHB.family = certificate.family'],
    ['PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_realizerTable',
      'certificate.selectorHB.realizerTable ='],
    ['PacketBudgetNoLowerZeroSlackSidecarCertificate.selectorHB_dependencyTable',
      'certificate.selectorHB.dependencyTable = certificate.dependencyTable'],
  ]) {
    const block = declarationBlock0(source, name);
    requireTokens0(failures, block, 'definitional-identity', [target, 'rfl']);
  }

  const endpoint = declarationBlock0(source,
    'packet_selector_hb_bcel_coherent_checked_complete');
  requireTokens0(failures, endpoint, 'coherent-endpoint', [
    'packetBudgetNoLower.selectorHB.realizerTable.environment.faithful',
    'NoOutcomeActiveClosureValid',
    'environment.hbActive',
    '¬DirectWire.TerminalBN6PacketConclusion',
    '¬packetBudgetNoLower.family.ConstantActivation',
    'packetBudgetNoLower.selectorHB.no_faithful',
    'packetBudgetNoLower.selectorHB.hb_closure_valid',
    'packetBudgetNoLower.selectorHB.no_hb_active',
    'packetBudgetNoLower.no_positive_packet',
    'bcel.not_constant_activation',
  ]);

  return [...new Set(failures)];
}

function validateZeroSlack0(source) {
  const failures = [];
  const zeroSlack = declarationBlock0(source, 'ZeroSlackCertificate');
  const oracle = declarationBlock0(source, 'PCCOracleCertificate');
  for (const block of [zeroSlack, oracle]) {
    if (/selectorHBClosure\s*:\s*SelectorHBZeroSlackSidecarCertificate/u.test(block)) {
      failures.push('detached-selector-hb-field');
    }
    if (/\b(?:coherence|sameFamily|sameTable|sameDependency|digest|hash)\w*\s*:/iu.test(block)) {
      failures.push('caller-coherence-field');
    }
  }
  requireTokens0(failures,
    declarationBlock0(source, 'ZeroSlackCertificate.selectorHBClosure'),
    'derived-zeroslack-accessor', [
      'z.packetBudgetNoLower.selectorHB',
    ]);
  requireTokens0(failures,
    declarationBlock0(source, 'PCCOracleCertificate.selectorHBClosure'),
    'derived-oracle-accessor', [
      'certificate.zeroSlack.selectorHBClosure',
    ]);
  requireTokens0(failures,
    declarationBlock0(source,
      'zeroslack_packet_selector_hb_bcel_coherent_checked_complete'),
    'report-facing-endpoint', [
      'z.selectorHBClosure.realizerTable.environment.faithful',
      'NoOutcomeActiveClosureValid',
      '¬DirectWire.TerminalBN6PacketConclusion',
      '¬z.packetBudgetNoLower.family.ConstantActivation',
      'z.bcelCarrierCoherence.no_positive_packet',
      'z.bcelCarrierCoherence.not_constant_activation',
    ]);
  return [...new Set(failures)];
}

test('ZeroSlack derives Selector/HB evidence from the exact M180 certificate', async () => {
  const [source, zeroSlack] = await Promise.all([
    text0(SOURCE_PATH), text0(ZEROSLACK_PATH),
  ]);
  assert.deepEqual(validateSource0(source), []);
  assert.deepEqual(validateZeroSlack0(zeroSlack), []);
  assert.match(zeroSlack,
    /^import PNP\.ResidualTerminalFiniteBCELPacketActivationObstruction$/mu);
  assert.match(zeroSlack,
    /bcelCarrierCoherence\s*:\s*TerminalFiniteBCELPacketCarrierCoherenceCertificate packetBudgetNoLower/u);
});

test('axiom transcript follows all M182 public declarations', async () => {
  const [audit, root] = await Promise.all([
    text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  assert.deepEqual(printed0(audit), AXIOM_DECLARATIONS);
  assert.equal(new Set(AXIOM_DECLARATIONS).size, AXIOM_DECLARATIONS.length);
  assert.equal(audit.startsWith('import PNP.ZeroSlack\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalZeroSlackPacketSelectorHBCoherence$/mu);
});

test('compiled inventory pins every reviewed M182 theorem', async () => {
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

test('regression retains exact family, table, dependency, and endpoint identities', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'selectorHB.family =',
    'selectorHB.realizerTable =',
    'selectorHB.dependencyTable =',
    'computedSelectorHBTable',
    'NoOutcomeActiveClosureValid',
    'TerminalBN6PacketConclusion',
    'ConstantActivation',
    'packet_selector_hb_bcel_coherent_checked_complete',
    'zeroslack_packet_selector_hb_bcel_coherent_checked_complete',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the same-family ZeroSlack coherence edge', async () => {
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
    ({ id }) => id ===
      'residual-terminal-zeroslack-packet-selector-hb-coherence');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-zeroslack-packet-selector-hb-coherence');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope,
    /same-family|exact.*family|family.*exact/iu);
  assert.match(milestone.scope,
    /Selector.*HB.*Packet.*BCEL|Packet.*Selector.*HB.*BCEL/iu);
  assert.match(milestone.nonClaim,
    /remain supplied|supplied.*data/iu);
  assert.match(milestone.nonClaim,
    /does not derive.*positive residual|not.*unconditional ZeroSlack/iu);
  assert.equal(
    status.leanResidualTerminalZeroSlackPacketSelectorHBCoherenceFormalized,
    true,
  );
  assert.equal(
    status.leanResidualTerminalZeroSlackPacketSelectorHBCoherenceAxiomAuditPassed,
    true,
  );
  assert.match(
    status.leanResidualTerminalZeroSlackPacketSelectorHBCoherenceScope,
    /same-family.*Selector.*HB.*Packet.*BCEL/iu,
  );
  assert.equal(status.leanZeroSlackPositiveSlackContradictionFormalized, false);
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
      /same-family.*Selector.*HB.*Packet.*BCEL|Selector.*HB.*same-family.*BCEL/iu,
      name);
    assert.match(semanticText0(text),
      /remain.*supplied|does not derive.*positive residual|unconditional ZeroSlack.*remain/iu,
      name);
  }
});

test('durable workflow derives transcript count and runs focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalZeroSlackPacketSelectorHBCoherenceAxiomAudit\.lean[\s\S]{0,5000}?run: node --test audits\/lean-residual-terminal-zeroslack-packet-selector-hb-coherence0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalZeroSlackPacketSelectorHBCoherenceAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalZeroSlackPacketSelectorHBCoherence\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile same-family coherence mutations fail closed', async () => {
  const [source, zeroSlack] = await Promise.all([
    text0(SOURCE_PATH), text0(ZEROSLACK_PATH),
  ]);
  const sourceMutations = [
    [source.replace(
      'certificate.table.withComputedPacketSelectorBN5FrontierObligationActivationDirectionBudgetFaithfulness',
      'certificate.table'), 'exact-computed-table'],
    [source.replace('certificate.accepted.2.2.2.1', 'by decide'),
      'derived-selector-silence'],
    [source.replace('certificate.accepted.2.2.2.2.1', 'by decide'),
      'derived-hb-closure'],
    [source.replace('family := certificate.family',
      'coherenceDigest : String := "detached"\n  family := certificate.family'),
    'caller-coherence-proof'],
    [source.replace('family := certificate.family',
      'accepted : Bool := true\n  family := certificate.family'),
    'caller-success-flag'],
    [source.replace('realizerTable := certificate.computedSelectorHBTable',
      'realizerTable := certificate.table'), 'structural-coherence'],
    [source.replace('dependencyTable := certificate.dependencyTable',
      'dependencyTable := certificate.selectorHB.dependencyTable'),
    'structural-coherence'],
    [source.replace('certificate.selectorHB.family = certificate.family',
      'True'), 'definitional-identity'],
    [source.replace('packetBudgetNoLower.no_positive_packet',
      'packetBudgetNoLower.selectorHB.no_faithful'), 'coherent-endpoint'],
    [`${source}\naxiom selectorHBCoherenceShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedSelectorHBCoherence : Type := Fin 4\n`,
      'fixed-bound'],
    [`${source}\ntheorem zero_slack_complete : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of sourceMutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }

  const zeroSlackMutations = [
    [zeroSlack.replace('packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate',
      'selectorHBClosure : SelectorHBZeroSlackSidecarCertificate\n  packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate'),
    'detached-selector-hb-field'],
    [zeroSlack.replace('packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate',
      'sameFamilyDigest : String\n  packetBudgetNoLower : PacketBudgetNoLowerZeroSlackSidecarCertificate'),
    'caller-coherence-field'],
    [zeroSlack.replace('z.packetBudgetNoLower.selectorHB',
      'detachedSelectorHB'),
    'derived-zeroslack-accessor'],
    [zeroSlack.replace('certificate.zeroSlack.selectorHBClosure',
      'certificate.zeroSlack.packetBudgetNoLower.selectorHB'),
    'derived-oracle-accessor'],
  ];
  for (const [mutated, expected] of zeroSlackMutations) {
    assert.equal(validateZeroSlack0(mutated).includes(expected), true, expected);
  }
});
