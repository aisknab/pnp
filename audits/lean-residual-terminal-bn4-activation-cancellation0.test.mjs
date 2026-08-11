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
  'lean/PNP/ResidualTerminalBN4ActivationCancellation.lean';
const AUDIT_PATH =
  'lean-audit/PNPResidualTerminalBN4ActivationCancellationAxiomAudit.lean';
const REGRESSION_PATH =
  'lean-regression/PNPResidualTerminalBN4ActivationCancellation.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH =
  'docs/lean_residual_terminal_bn4_activation_cancellation.md';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'terminalBN4ActivationCode',
  'TerminalBN4CodeActive',
  'terminalBN4ActivationCode_active_iff',
  'terminalBN4ActivationCode_eq_iff',
  'terminalBN4ActivationCode_eq_iff_activation',
  'TerminalBN4ActivationKey',
  'terminalBN4ActivationKey_eq_iff',
  'TerminalBN4CellSign',
  'TerminalBN4ActivationCell',
  'TerminalBN4ActivationCell.signedContribution',
  'terminalBN4PositiveMass',
  'terminalBN4NegativeMass',
  'terminalBN4InputSignedMass',
  'terminalBN4IntegerMassLedger_exact',
  'TerminalBN4KeyCancellation',
  'classifyTerminalBN4KeyCancellation',
  'terminalBN4CancelAtKey',
  'TerminalBN4KeyCancellation.residualCells',
  'TerminalBN4KeyCancellation.residual_key_eq',
  'TerminalBN4KeyCancellation.residual_mass_positive',
  'TerminalBN4KeyCancellation.no_opposite_sign_residual',
  'TerminalBN4KeyCancellation.residual_signedContribution_exact',
  'terminalBN4CancelAtKey_signedContribution_exact',
  'terminalBN4CanonicalKeys',
  'terminalBN4CanonicalKeys_nodup',
  'mem_terminalBN4CanonicalKeys_iff',
  'TerminalBN4CellsUseCanonicalAtoms',
  'terminalBN4CellsUseCanonicalAtoms_iff',
  'TerminalComputedBN4ActivationCancellation',
  'TerminalComputedBCELAnchorNucleus.computedBN4ActivationCancellation',
  'TerminalBN4ActivationCancellationOutcome',
  'classifyTerminalBN4ActivationCancellation',
  'classifyTerminalBN4ActivationCancellation_exhaustive',
]);

const AUDITED_DECLARATIONS = Object.freeze(
  LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.terminalBN4ActivationCode_active_iff`,
  `${NAMESPACE}.terminalBN4ActivationCode_eq_iff_activation`,
  `${NAMESPACE}.terminalBN4ActivationKey_eq_iff`,
  `${NAMESPACE}.terminalBN4IntegerMassLedger_exact`,
  `${NAMESPACE}.TerminalBN4KeyCancellation.residual_key_eq`,
  `${NAMESPACE}.TerminalBN4KeyCancellation.residual_mass_positive`,
  `${NAMESPACE}.TerminalBN4KeyCancellation.no_opposite_sign_residual`,
  `${NAMESPACE}.TerminalBN4KeyCancellation.residual_signedContribution_exact`,
  `${NAMESPACE}.terminalBN4CancelAtKey_signedContribution_exact`,
  `${NAMESPACE}.terminalBN4CanonicalKeys_nodup`,
  `${NAMESPACE}.terminalBN4CellsUseCanonicalAtoms_iff`,
  `${NAMESPACE}.TerminalComputedBCELAnchorNucleus.computedBN4ActivationCancellation`,
  `${NAMESPACE}.classifyTerminalBN4ActivationCancellation_exhaustive`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarationNames0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ name }) => name);
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

function validateSource0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|sorry|admit|noncomputable|unsafe)\b/u.test(stripped)) {
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
  if (/(?:def|theorem)\s+(?:p_eq_np|zeroSlack|pccmin|bcelReady|routeComplete|fullBN4)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  if (/\b(?:callerCancellation|callerResidual|trustFlag|activationExact\s*:\s*Bool)\b/u.test(stripped)) {
    failures.push('caller-certificate');
  }
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalBN3RequestEnvelope',
  ])) failures.push('closed-import');

  const code = declarationBlock0(source, 'terminalBN4ActivationCode');
  if (!code.includes('[terminalBN3MinimalConsumer atom]')) {
    failures.push('canonical-singleton-code');
  }
  const active = declarationBlock0(source,
    'terminalBN4ActivationCode_active_iff');
  for (const token of [
    'TerminalBN4CodeActive', 'terminalBN4ActivationCode',
    'TerminalBN3RequestPredicate',
  ]) if (!active.includes(token)) failures.push('activation-by-antichain');
  const equality = declarationBlock0(source,
    'terminalBN4ActivationCode_eq_iff_activation');
  for (const token of [
    '∀ cut', 'activationEqual [left]', 'leftActive', 'rightActive',
  ]) if (!equality.includes(token)) failures.push('activation-equality-no-cut-scan');
  if (/terminalListSubsets|allTerminalBCELProperCutSeeds/u.test(equality)) {
    failures.push('activation-equality-cut-scan');
  }

  const key = declarationBlock0(source, 'TerminalBN4ActivationKey');
  for (const field of ['atom', 'semanticSignature', 'transportType']) {
    if (!key.includes(field)) failures.push('complete-typed-key');
  }
  const keyExact = declarationBlock0(source,
    'terminalBN4ActivationKey_eq_iff');
  for (const token of [
    'activationEqual', 'semanticEqual', 'transportEqual',
    'terminalBN4ActivationCode_eq_iff_activation',
  ]) if (!keyExact.includes(token)) failures.push('typed-key-exactness');

  const positive = declarationBlock0(source, 'terminalBN4PositiveMass');
  const negative = declarationBlock0(source, 'terminalBN4NegativeMass');
  for (const block of [positive, negative]) {
    if (!block.includes('if cell.key = key then')) {
      failures.push('same-key-only-total');
    }
  }
  if (!positive.includes('| .positive => cell.mass')
      || !negative.includes('| .negative => cell.mass')) {
    failures.push('signed-natural-totals');
  }

  const classifier = declarationBlock0(source,
    'classifyTerminalBN4KeyCancellation');
  for (const token of [
    'positiveMass = negativeMass', 'negativeMass < positiveMass',
    '.positive (positiveMass - negativeMass)',
    '.negative (negativeMass - positiveMass)',
  ]) if (!classifier.includes(token)) failures.push('exact-mass-trichotomy');

  const residual = declarationBlock0(source,
    'TerminalBN4KeyCancellation.residualCells');
  for (const token of [
    '| .balanced _ => []', 'sign := .positive', 'sign := .negative',
  ]) if (!residual.includes(token)) failures.push('canonical-residual-sign');
  const signedExact = declarationBlock0(source,
    'TerminalBN4KeyCancellation.residual_signedContribution_exact');
  if (!signedExact.includes('Int.ofNat positiveMass - Int.ofNat negativeMass')) {
    failures.push('same-key-cancellation-exact');
  }
  const noOpposite = declarationBlock0(source,
    'TerminalBN4KeyCancellation.no_opposite_sign_residual');
  if (!noOpposite.includes('left.sign = right.sign')) {
    failures.push('no-opposite-sign-residual');
  }
  const preserve = declarationBlock0(source,
    'TerminalBN4KeyCancellation.residual_key_eq');
  if (!preserve.includes('cell.key = key')) {
    failures.push('complete-key-preservation');
  }

  const canonicalKeys = declarationBlock0(source, 'terminalBN4CanonicalKeys');
  for (const token of [
    'terminalBN4CanonicalKeys tail',
    'if cell.key ∈ tailKeys then tailKeys else cell.key :: tailKeys',
  ]) if (!canonicalKeys.includes(token)) failures.push('canonical-key-universe');

  const atomCheck = declarationBlock0(source,
    'TerminalBN4CellsUseCanonicalAtoms');
  for (const token of [
    'cells.all', 'terminalBN3RequestPredicateBool', 'result.requestAtoms',
  ]) if (!atomCheck.includes(token)) failures.push('canonical-atom-check');

  const packageBlock = declarationBlock0(source,
    'TerminalComputedBN4ActivationCancellation');
  for (const field of [
    'activationByActiveAntichain',
    'activationEqualityWithoutCutEnumeration',
    'completeTypedKeyEquality',
    'sameKeyCancellationExact',
    'completeKeyPreserved',
    'noOppositeSignSameKeyResidual',
    'integerMassLedgerExact',
  ]) if (!packageBlock.includes(field)) failures.push('proof-bearing-package');

  const pipeline = declarationBlock0(source,
    'classifyTerminalBN4ActivationCancellation');
  for (const branch of [
    '.insufficient failure', '.algebraFailure nucleus first failure',
    '.cutDefectFailure nucleus first failure',
    '.cutRouteFailure nucleus first failure',
    '.invalidAtomLedger result envelope canonicalAtoms',
    'result.computedBN4ActivationCancellation cells canonicalAtoms',
  ]) if (!pipeline.includes(branch)) failures.push('total-failure-preservation');

  return [...new Set(failures)];
}

test('finite BN4 source closes activation-exact typed same-key cancellation', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 33-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 33);
  assert.equal(audit.startsWith(
    'import PNP.ResidualTerminalBN4ActivationCancellation\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalBN4ActivationCancellation$/mu);
});

test('compiled inventory pins every BN4 declaration to the standard allowlist', async () => {
  const inventory = JSON.parse(await text0(INVENTORY_PATH));
  const rows = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  const approved = new Set(['propext', 'Quot.sound']);
  for (const name of AUDITED_DECLARATIONS) {
    const row = rows.get(name);
    assert.ok(row, name);
    for (const axiom of row.axioms) {
      assert.equal(approved.has(axiom), true, `${name}: ${axiom}`);
    }
    assert.equal(row.axioms.includes('Classical.choice'), false, name);
    assert.equal(row.axioms.includes('sorryAx'), false, name);
  }
  for (const name of MILESTONE_THEOREMS) {
    assert.equal(rows.get(name)?.kind, 'theorem', name);
    assert.ok(inventory.milestoneCandidates.some(
      (entry) => entry.name === name && typeof entry.kernelType === 'string'));
  }
});

test('regression separates semantic and transport keys and rejects foreign atoms', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'bn4CancellationResidualSummary bn4CancellationKey0 = (4, 4)',
    'bn4CancellationResidualSummary bn4CancellationSemanticKey',
    '(-5, 5)',
    'bn4CancellationResidualSummary bn4CancellationTransportKey',
    'bn4CancellationReadyOutcome = (5, 4)',
    'bn4CancellationInvalidOutcome = 4',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication earns only the finite BN4 kernel and keeps global claims closed', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-bn4-activation-cancellation');
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-bn4-activation-cancellation');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /complete typed key/u);
  assert.match(milestone.scope, /integer mass/u);
  assert.match(milestone.nonClaim, /explicit typed cell ledger/u);
  assert.match(milestone.nonClaim, /not the full historical BN4/u);
  assert.equal(status.leanResidualTerminalBN4ActivationCancellationFormalized,
    true);
  assert.equal(
    status.leanResidualTerminalBN4ActivationCancellationAxiomAuditPassed,
    true);
  assert.match(status.leanResidualTerminalBN4ActivationCancellationScope,
    /activation-exact/u);
  assert.equal(status.leanZeroSlackCompletenessFormalized, false);
  assert.equal(status.leanPCCMinPolynomialRuntimeFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 5);
  assert.match(docs, /Finite BN4 activation-exact cancellation kernel/u);
  assert.match(docs, /not the full historical/u);
});

test('durable workflow runs the transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-bn4-activation-cancellation0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalBN4ActivationCancellationAxiomAudit\.lean[\s\S]{0,1800}-eq 33/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalBN4ActivationCancellation\.lean/u);
});

test('hostile BN4 mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('[terminalBN3MinimalConsumer atom]', '[]'),
      'canonical-singleton-code'],
    [source.replace('activationEqual [left]', 'activationEqual []'),
      'activation-equality-no-cut-scan'],
    [source.replace('semanticSignature : SemanticSignature',
      'erasedSemantic : SemanticSignature'), 'complete-typed-key'],
    [source.replace('if cell.key = key then', 'if True then'),
      'same-key-only-total'],
    [source.replace('| .balanced _ => []',
      '| .balanced _ => [{ key := key, sign := .positive, mass := 1 }]'),
      'canonical-residual-sign'],
    [source.replace('.invalidAtomLedger result envelope canonicalAtoms',
      '.ready result envelope callerCancellation'), 'caller-certificate'],
    [`${source}\naxiom bn4Shortcut : True\n`, 'assumption-declaration'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
