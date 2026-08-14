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
  'lean/PNP/ResidualTerminalPacketUnitChargeBlueprintRealizer.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalPacketUnitChargeBlueprintRealizerAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalPacketUnitChargeBlueprintRealizer.lean';
const DOCS_PATH =
  'docs/lean_residual_terminal_packet_unit_charge_blueprint_realizer.md';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const NAMESPACE = 'PNP.DirectWire';

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.eraseFirstNat_sound`,
  `${NAMESPACE}.natOccurrencePermBool_sound`,
  `${NAMESPACE}.natOccurrencePermBool_complete`,
  `${NAMESPACE}.natOccurrencePermBool_eq_true_iff`,
  `${NAMESPACE}.TerminalPacketUnitChargeBlueprint.check_eq_true_iff`,
  `${NAMESPACE}.unitChargeRange_sum`,
  `${NAMESPACE}.TerminalPacketUnitChargeBlueprint.strictEquivalentGain_of_check`,
  `${NAMESPACE}.TerminalPacketUnitChargeBlueprint.strictResidualDescent_of_check`,
  `${NAMESPACE}.TerminalPacketUnitChargeBlueprintAtomOutcome.sound`,
  `${NAMESPACE}.TerminalPacketUnitChargeBlueprintRealizerOutcome.sound`,
  `${NAMESPACE}.TerminalPacketUnitChargeBlueprintRealizerOutcome.gain_descent`,
  `${NAMESPACE}.TerminalPacketEncodedSelectorConclusion.unitChargeBlueprintRealizer_packet`,
  `${NAMESPACE}.terminalBN6_packet_unit_charge_blueprint_realizer_sound`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarationNames0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ name }) => name);
}

function auditedDeclarations0(source) {
  return declarationNames0(source).map((name) => `${NAMESPACE}.${name}`);
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zero_slack_complete|pccmin_polynomial_exact|unitChargeRealizerComplete|unconditionalZeroSlack)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\b(?:ZeroSlackResult|BotHN|BotBUD|BotSeed)\b/u.test(stripped)) {
    failures.push('typed-blocker-overclaim');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  assert.deepEqual(imports, [
    'PNP.ResidualTerminalPacketChargeSurplus',
  ]);

  const erase = declarationBlock0(source, 'eraseFirstNat');
  requireTokens0(failures, erase, 'constructive-occurrence-removal', [
    'def eraseFirstNat (needle : Nat)',
    'if head = needle then',
    '(eraseFirstNat needle tail).map',
  ]);

  const eraseSound = declarationBlock0(source, 'eraseFirstNat_sound');
  requireTokens0(failures, eraseSound, 'constructive-occurrence-soundness', [
    '(needle :: remaining).Perm source',
    'List.Perm.swap head needle rest',
    'inductionHypothesis recursiveEquation',
  ]);

  const permBool = declarationBlock0(source, 'natOccurrencePermBool');
  requireTokens0(failures, permBool, 'exact-constructive-permutation', [
    'def natOccurrencePermBool : List Nat → List Nat → Bool',
    'eraseFirstNat head right',
    'natOccurrencePermBool tail remaining',
  ]);
  if (/decide\s*\([^)]*\.Perm/u.test(permBool)) {
    failures.push('classical-permutation-decider');
  }

  const permIff = declarationBlock0(source,
    'natOccurrencePermBool_eq_true_iff');
  requireTokens0(failures, permIff, 'exact-constructive-permutation', [
    'natOccurrencePermBool left right = true ↔ left.Perm right',
    'natOccurrencePermBool_sound',
    'natOccurrencePermBool_complete',
  ]);

  const blueprint = declarationBlock0(source,
    'TerminalPacketUnitChargeBlueprint');
  requireTokens0(failures, blueprint, 'data-only-blueprint', [
    'next : Implementation inputs outputs',
    'pairing : List (Nat × Nat)',
    'unmatched : List Nat',
  ]);
  if (/\b(?:smaller|Valid|Equivalent|StrictEquivalentGain|supportExact|replacementExact)\s*:/u.test(
    stripLeanCommentsAndStrings0(blueprint))) {
    failures.push('assumed-blueprint-proof');
  }

  const valid = declarationBlock0(source,
    'TerminalPacketUnitChargeBlueprint.Valid');
  requireTokens0(failures, valid, 'canonical-unit-charge-validity', [
    '(List.range current.gateCount).Perm',
    'blueprint.pairing.map Prod.fst ++ blueprint.unmatched',
    '(List.range blueprint.next.gateCount).Perm',
    'blueprint.pairing.map Prod.snd',
    'blueprint.unmatched ≠ []',
    'Equivalent blueprint.next.candidate.program',
  ]);

  const check = declarationBlock0(source,
    'TerminalPacketUnitChargeBlueprint.check');
  requireTokens0(failures, check, 'executable-fail-closed-check', [
    'natOccurrencePermBool (List.range current.gateCount)',
    'natOccurrencePermBool (List.range blueprint.next.gateCount)',
    'decide (blueprint.unmatched ≠ [])',
    'equivalentBool blueprint.next.candidate current.candidate',
  ]);
  if (/strictEquivalentGainBool|gateCount\s*</u.test(check)) {
    failures.push('assumed-gate-decrease');
  }

  const surplus = declarationBlock0(source,
    'TerminalPacketUnitChargeBlueprint.Valid.chargeSurplus');
  requireTokens0(failures, surplus, 'derived-unit-charge-surplus', [
    'TerminalPacketChargeSurplus',
    '(List.range current.gateCount)',
    '(List.range blueprint.next.gateCount)',
    '(fun _ : Nat => 1)',
    'supportExact := valid.1',
    'replacementExact := valid.2.1',
    'positiveUnmatched := by',
  ]);

  const realization = declarationBlock0(source,
    'TerminalPacketUnitChargeBlueprint.Valid.chargeSurplusRealization');
  requireTokens0(failures, realization, 'mechanical-gate-accounting', [
    'surplus := valid.chargeSurplus',
    'supportAccountsCurrent := unitChargeRange_sum current.gateCount',
    'replacementAccountsNext := unitChargeRange_sum blueprint.next.gateCount',
    'semanticsPreserved := valid.2.2.2',
  ]);

  const gain = declarationBlock0(source,
    'TerminalPacketUnitChargeBlueprint.strictEquivalentGain_of_check');
  requireTokens0(failures, gain, 'derived-blueprint-gain', [
    '(blueprint.check_eq_true_iff).1 checked',
    '.chargeSurplusRealization',
    '.strictEquivalentGain',
    'StrictEquivalentGain current blueprint.next',
  ]);
  if (/strictEquivalentGainBool/u.test(gain)) {
    failures.push('assumed-gate-decrease');
  }

  const atomScan = declarationBlock0(source,
    'scanTerminalPacketUnitChargeBlueprintAtoms');
  requireTokens0(failures, atomScan, 'complete-source-atom-scan', [
    'head.payload.check = true',
    'scanTerminalPacketUnitChargeBlueprintAtoms current tail',
    'noTailValid',
  ]);

  const handleScan = declarationBlock0(source,
    'scanTerminalPacketUnitChargeBlueprintHandles');
  requireTokens0(failures, handleScan, 'complete-handle-scan', [
    '(family.packetSelectorCell head).atoms',
    'scanTerminalPacketUnitChargeBlueprintHandles current family',
    'noHeadValid',
    'noTailValid',
  ]);

  const universe = declarationBlock0(source,
    'TerminalBN6GroupedFamily.realizeUnitChargeBlueprints');
  requireTokens0(failures, universe, 'exhaustive-selector-family-scan', [
    'family.packetSelectorHandles',
    'family.mem_packetSelectorHandles handle',
    'TerminalPacketUnitChargeBlueprintRealizerOutcome current family',
  ]);

  const outcome = declarationBlock0(source,
    'TerminalPacketUnitChargeBlueprintRealizerOutcome');
  requireTokens0(failures, outcome, 'fail-closed-local-outcome', [
    'atomMember : atom ∈ (family.packetSelectorCell handle).atoms',
    'valid : atom.payload.Valid',
    'noValid : ∀ handle',
    '¬atom.payload.Valid',
  ]);
  if (/ZeroSlack|BotHN|BotBUD|BotSeed/u.test(
    stripLeanCommentsAndStrings0(outcome))) {
    failures.push('typed-blocker-overclaim');
  }

  const packet = declarationBlock0(source,
    'TerminalPacketEncodedSelectorConclusion.unitChargeBlueprintRealizer_packet');
  requireTokens0(failures, packet, 'packet-preservation', [
    'conclusion.unitChargeBlueprintRealizer.packet = conclusion',
    'rfl',
  ]);

  const composed = declarationBlock0(source,
    'terminalBN6_packet_unit_charge_blueprint_realizer_sound');
  requireTokens0(failures, composed, 'bounded-composed-interface', [
    'TerminalPacketEncodedSelectorConclusion family ∧',
    'StrictEquivalentGain current atom.payload.next',
    '¬atom.payload.Valid',
    '(family.realizeUnitChargeBlueprints current).sound',
  ]);

  return [...new Set(failures)];
}

test('unit-charge blueprint validator derives gains constructively', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript derives its exact declaration surface from source', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH), text0(AUDIT_PATH), text0('lean/PNP.lean'),
  ]);
  const expected = auditedDeclarations0(source);
  assert.ok(expected.length > MILESTONE_THEOREMS.length);
  assert.deepEqual(printed0(audit), expected);
  assert.equal(new Set(expected).size, expected.length);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalPacketUnitChargeBlueprintRealizer\n'), true);
  assert.match(root,
    /^import PNP\.ResidualTerminalPacketUnitChargeBlueprintRealizer$/mu);
});

test('compiled inventory pins every reviewed unit-charge realizer theorem', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of MILESTONE_THEOREMS) {
    const row = rows.get(name);
    assert.equal(row?.kind, 'theorem', name);
    for (const axiom of row.axioms) {
      assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    }
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
    assert.equal(row.axioms.includes('sorryAx'), false, name);
    assert.ok(inventory.milestoneCandidates.some(
      (entry) => entry.name === name && typeof entry.kernelType === 'string'));
  }
});

test('regression covers acceptance, rejection, scanning, gain, and descent', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'acceptedUnitChargeBlueprint.check = true',
    'duplicateSupportUnitChargeBlueprint.check = false',
    'emptyUnmatchedUnitChargeBlueprint.check = false',
    'semanticMismatchUnitChargeBlueprint.check = false',
    'acceptedUnitChargeBlueprintValid.chargeSurplus',
    'acceptedUnitChargeBlueprint.strictEquivalentGain_of_check',
    'acceptedUnitChargeBlueprint.strictResidualDescent_of_check',
    'unitChargeBlueprintAtomScan_findsAccepted',
    'family.realizeUnitChargeBlueprints current',
    'terminalBN6_packet_unit_charge_blueprint_realizer_sound',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the supplied-family unit-charge blueprint realizer', async () => {
  const [publication, status, docs, readme, reconstruction, report, pipeline,
    auditQuestions] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
    text0('README.md'),
    text0('docs/FORMAL_RECONSTRUCTION.md'),
    text0('publication/canonical_proof_report.template.tex'),
    text0('docs/proof_pipeline.md'),
    text0('docs/audit_questions.md'),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id ===
      'residual-terminal-packet-unit-charge-blueprint-realizer');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-packet-unit-charge-blueprint-realizer');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /canonical unit-charge gate-occurrence ledgers/u);
  assert.match(milestone.scope, /every canonical handle/u);
  assert.match(milestone.nonClaim, /blueprints.*remain explicit inputs/iu);
  assert.match(milestone.nonClaim, /not.*BotHN.*BotBUD.*BotSeed/iu);
  assert.equal(status.leanResidualTerminalPacketUnitChargeBlueprintRealizerFormalized,
    true);
  assert.equal(status.leanResidualTerminalPacketUnitChargeBlueprintRealizerAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalPacketUnitChargeBlueprintRealizerScope,
    /constructive-exact-occurrence-checker/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ZeroSlack'));
  assert.match(docs, /unit-charge/u);
  assert.match(docs, /Classical\.choice/u);
  for (const surface of [readme, reconstruction, report, pipeline,
    auditQuestions].map(semanticText0)) {
    assert.match(surface, /unit-charge blueprint/iu);
    assert.match(surface, /supplied.*family/iu);
  }
});

test('durable workflow derives transcript count and runs all focused checks', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  const block = workflow.match(
    /PNPResidualTerminalPacketUnitChargeBlueprintRealizerAxiomAudit\.lean[\s\S]{0,3200}?run: node --test audits\/lean-residual-terminal-packet-unit-charge-blueprint-realizer0\.test\.mjs/u)?.[0] ?? '';
  assert.match(block,
    /expected_count="\$\(grep -Ec '\^#print axioms ' lean-audit\/PNPResidualTerminalPacketUnitChargeBlueprintRealizerAxiomAudit\.lean\)"/u);
  assert.match(block, /-eq "\$expected_count"/u);
  assert.match(block,
    /lean-regression\/PNPResidualTerminalPacketUnitChargeBlueprintRealizer\.lean/u);
  assert.match(block, /Classical\\\.choice/u);
});

test('hostile blueprint-realizer mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('eraseFirstNat head right', 'some right'),
      'exact-constructive-permutation'],
    [source.replace('natOccurrencePermBool_sound, natOccurrencePermBool_complete',
      'natOccurrencePermBool_sound, natOccurrencePermBool_sound'),
      'exact-constructive-permutation'],
    [source.replace('pairing : List (Nat × Nat)',
      'smaller : next.gateCount < current.gateCount\n  pairing : List (Nat × Nat)'),
      'assumed-blueprint-proof'],
    [source.replace('blueprint.unmatched ≠ [] ∧', 'True ∧'),
      'canonical-unit-charge-validity'],
    [source.replace(
      'natOccurrencePermBool (List.range blueprint.next.gateCount)\n      (blueprint.pairing.map Prod.snd)',
      'true'),
      'executable-fail-closed-check'],
    [source.replace('equivalentBool blueprint.next.candidate current.candidate',
      'true'), 'executable-fail-closed-check'],
    [source.replace('supportExact := valid.1', 'supportExact := by simp'),
      'derived-unit-charge-surplus'],
    [source.replace(
      'replacementAccountsNext := unitChargeRange_sum blueprint.next.gateCount',
      'replacementAccountsNext := by simp'), 'mechanical-gate-accounting'],
    [source.replace('.chargeSurplusRealization\n    |>.strictEquivalentGain',
      '.chargeSurplusRealization\n    |>.strictEquivalentGainBool'),
      'assumed-gate-decrease'],
    [source.replace('family.packetSelectorHandles with', '[] with'),
      'exhaustive-selector-family-scan'],
    [source.replace('¬atom.payload.Valid', 'ZeroSlackResult current'),
      'typed-blocker-overclaim'],
    [`${source}\naxiom unitChargeShortcut : True\n`,
      'assumption-declaration'],
    [`${source}\ndef fixedUnitChargeCarrier : Type := Fin 7\n`,
      'fixed-bound'],
    [`${source}\ntheorem unconditionalZeroSlack : True := by trivial\n`,
      'overclaim'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
