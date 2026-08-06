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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalSupportSquareClosure.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalSupportSquareClosureAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalSupportSquareClosure.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_support_square_closure.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_LOCAL_DECLARATIONS = Object.freeze([
  'TerminalSupportSquareCorner',
  'TerminalSaturatedSupportSquare',
  'terminalSaturatedSupportSquare',
  'TerminalSaturatedSupportSquare.leftRecords',
  'TerminalSaturatedSupportSquare.rightRecords',
  'TerminalSaturatedSupportSquare.meetRecords',
  'TerminalSaturatedSupportSquare.joinRecords',
  'TerminalSaturatedSupportSquare.records',
  'TerminalSaturatedSupportSquare.mem_meetRecords_iff',
  'TerminalSaturatedSupportSquare.leftRecords_closed',
  'TerminalSaturatedSupportSquare.rightRecords_closed',
  'TerminalSaturatedSupportSquare.meetRecords_closed',
  'TerminalSaturatedSupportSquare.mem_joinRecords_iff',
  'TerminalSaturatedSupportSquare.joinRecords_closed',
  'TerminalSaturatedSupportSquare.records_closed',
  'TerminalSaturatedSupportSquare.meetRecords_subset_left',
  'TerminalSaturatedSupportSquare.meetRecords_subset_right',
  'TerminalSaturatedSupportSquare.leftRecords_subset_join',
  'TerminalSaturatedSupportSquare.rightRecords_subset_join',
  'TerminalSaturatedSupportSquare.meetRecords_greatest',
  'TerminalSaturatedSupportSquare.joinRecords_least',
  'terminalSaturateRecords_mem_congr',
  'TerminalSaturatedSupportSquare.records_congr',
  'TerminalSaturatedSupportSquare.completed',
  'TerminalSaturatedSupportSquare.physically_compatible',
  'TerminalSaturatedSupportSquare.extracted',
  'TerminalSaturatedSupportSquare.extracted_gateCount',
  'TerminalSaturatedSupportSquare.extracted_semantics',
  'TerminalSaturatedSupportSquare.extracted_induced',
]);

const PUBLIC_DECLARATIONS = Object.freeze(
  PUBLIC_LOCAL_DECLARATIONS.map((name) => `${NAMESPACE}.${name}`),
);

const REUSED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.mem_allTerminalPrimitiveRecords`,
  `${NAMESPACE}.terminalSaturate_least`,
  `${NAMESPACE}.terminalSaturate_monotone`,
  `${NAMESPACE}.terminalSaturateRecords`,
  `${NAMESPACE}.terminalSaturateRecords_extensive`,
  `${NAMESPACE}.terminalSaturateRecords_closed`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.extractTerminalSupport_gateCount`,
  `${NAMESPACE}.extractTerminalSupport_semantics`,
  `${NAMESPACE}.extractTerminalSupport_induced`,
]);

const AUDITED_DECLARATIONS = Object.freeze([
  ...PUBLIC_DECLARATIONS,
  ...REUSED_DECLARATIONS,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalSaturatedSupportSquare.mem_meetRecords_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.leftRecords_closed`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.rightRecords_closed`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.meetRecords_closed`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.mem_joinRecords_iff`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.joinRecords_closed`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.records_closed`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.meetRecords_subset_left`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.meetRecords_subset_right`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.leftRecords_subset_join`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.rightRecords_subset_join`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.meetRecords_greatest`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.joinRecords_least`,
  `${NAMESPACE}.terminalSaturateRecords_mem_congr`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.records_congr`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.physically_compatible`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.extracted_gateCount`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.extracted_semantics`,
  `${NAMESPACE}.TerminalSaturatedSupportSquare.extracted_induced`,
  `${NAMESPACE}.mem_terminalSaturateRecords_iff`,
  `${NAMESPACE}.completeTerminalPhysicalSupport_compatible`,
  `${NAMESPACE}.extractTerminalSupport_semantics`,
  `${NAMESPACE}.extractTerminalSupport_induced`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map(({ name }) => `${NAMESPACE}.${name}`);
}

function privateHelpers0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  return [...stripped.matchAll(
    /^private\s+(?:noncomputable\s+)?(?:def|theorem|inductive|structure|abbrev)\s+([^\s({:]+)/gmu,
  )].map((match) => match[1]);
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

function commonFailures0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit|noncomputable)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|callerCertificate|closureCertificate|squareCertificate|compatibilityCertificate|frontierCertificate|projectionCertificate|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|frontierPushout|projectionCompatibleSquare|squareLegitimate|saturatePositive|bcelReady|zeroSlackComplete|pccMinExact|polynomialSupportSquare)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateSource0(source) {
  const failures = commonFailures0(source);
  const stripped = stripLeanCommentsAndStrings0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalProperSupport',
  ])) failures.push('closed-import');
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (JSON.stringify(privateHelpers0(source)) !== JSON.stringify(['sideUnion_closed'])) {
    failures.push('private-helper-surface');
  }

  const meet = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.meetRecords',
  );
  const join = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.joinRecords',
  );
  const meetSpec = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.mem_meetRecords_iff',
  );
  const joinSpec = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.mem_joinRecords_iff',
  );
  const allClosed = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.records_closed',
  );
  const meetGreatest = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.meetRecords_greatest',
  );
  const joinLeast = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.joinRecords_least',
  );
  const congr = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.records_congr',
  );
  const compatible = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.physically_compatible',
  );
  const extracted = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.extracted',
  );
  const semantics = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.extracted_semantics',
  );
  const induced = declarationBlock0(
    source,
    'TerminalSaturatedSupportSquare.extracted_induced',
  );

  if (!/allTerminalPrimitiveRecords[\s\S]*\.filter[\s\S]*record ∈ square\.leftRecords ∧ record ∈ square\.rightRecords/u.test(meet)) {
    failures.push('exact-saturated-meet');
  }
  if (!/terminalSaturateRecords system \(square\.leftRecords \+\+ square\.rightRecords\)/u.test(join)) {
    failures.push('saturated-union-join');
  }
  if (!/record ∈ square\.meetRecords ↔[\s\S]*record ∈ square\.leftRecords ∧ record ∈ square\.rightRecords/u.test(meetSpec)) {
    failures.push('meet-membership-specification');
  }
  if (!/record ∈ square\.joinRecords ↔[\s\S]*record ∈ square\.leftRecords ∨ record ∈ square\.rightRecords/u.test(joinSpec)
      || !/terminalSaturate_least/u.test(joinSpec)
      || !/sideUnion_closed square/u.test(joinSpec)
      || !/terminalSaturateRecords_extensive/u.test(joinSpec)) {
    failures.push('join-membership-specification');
  }
  for (const corner of ['meet', 'left', 'right', 'join']) {
    if (!new RegExp(`\\| ${corner} => exact square\\.${corner}Records_closed`, 'u').test(allClosed)) {
      failures.push(`closed-${corner}-corner`);
    }
  }
  if (!/mem_meetRecords_iff[\s\S]*withinLeft record member[\s\S]*withinRight record member/u.test(meetGreatest)) {
    failures.push('greatest-lower-bound');
  }
  if (!/mem_joinRecords_iff[\s\S]*containsLeft record leftMember[\s\S]*containsRight record rightMember/u.test(joinLeast)) {
    failures.push('least-upper-bound');
  }
  if (!/terminalSaturateRecords_mem_congr[\s\S]*cases corner/u.test(congr)) {
    failures.push('seed-extensionality');
  }
  if (!/completeTerminalPhysicalSupport_compatible candidate \(square\.records corner\)/u.test(compatible)) {
    failures.push('computed-physical-compatibility');
  }
  if (!/extractTerminalSupport candidate \(square\.records corner\)/u.test(extracted)
      || !/extractTerminalSupport_semantics candidate \(square\.records corner\)/u.test(semantics)
      || !/extractTerminalSupport_induced candidate \(square\.records corner\)/u.test(induced)) {
    failures.push('exact-corner-extraction');
  }
  if (/\b(?:startGate|endGate|gateOffset|fixedSeedTable|coordinateTable|fixedSquareTable)\b/u.test(stripped)) {
    failures.push('hard-coded-support-family');
  }
  return [...new Set(failures)];
}

test('terminal support square has one closed all-finite interface', async () => {
  const source = await text0(SOURCE_PATH);
  assert.deepEqual(validateSource0(source), []);
});

test('axiom transcript covers every new and reused declaration exactly once', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(audit.startsWith('import PNP.ResidualTerminalSupportSquareClosure\n'), true);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 40);
  assert.equal(PUBLIC_DECLARATIONS.length, 29);
  assert.equal(REUSED_DECLARATIONS.length, 11);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalSupportSquareClosure$/mu);
});

test('compiled closure is approved for every support-square declaration', async () => {
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
});

test('regression exercises nontrivial square algebra and every physical corner', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'squareGate0Record',
    'squareGate1Record',
    'squareGate2Record',
    'squareProfile0Record',
    'squareProfile1Record',
    '.gateSource',
    '.origin',
    '.charge',
    '.direction',
    'square.meetRecords',
    'square.joinRecords',
    'square.meetRecords_greatest',
    'square.joinRecords_least',
    'emptySquare',
    'identicalSquare',
    'duplicateReorderedSquare',
    'reorderedSquare',
    'duplicateReorderedSquare.records_congr',
    'square.completed squareCandidate .meet',
    'square.completed squareCandidate .left',
    'square.completed squareCandidate .right',
    'square.completed squareCandidate .join',
    'square.extracted_semantics',
    'square.extracted_induced',
  ]) assert.match(regression, new RegExp(token.replaceAll('.', '\\.'), 'u'));
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('compiled inventory and publication pin the exact support-square theorem boundary', async () => {
  const [inventory, publication, docs] = await Promise.all([
    text0(INVENTORY_PATH).then(JSON.parse),
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const byName = new Map(inventory.declarations.map((entry) => [entry.name, entry]));
  for (const name of PUBLIC_DECLARATIONS) assert.equal(byName.has(name), true, name);
  for (const name of MILESTONE_THEOREMS) {
    const entry = byName.get(name);
    assert.equal(entry?.kind, 'theorem', name);
    assert.equal(entry.axioms.some((axiom) => axiom.startsWith('PNP.')), false, name);
    assert.equal(entry.axioms.includes('Classical.choice'), false, name);
    assert.equal(entry.axioms.includes('sorryAx'), false, name);
  }
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-saturated-support-square-closure',
  );
  assert.equal(milestone?.classification,
    'formalized-terminal-saturated-support-square-closure');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /every finite direct-wire candidate/u);
  assert.match(milestone.scope, /pair of finite terminal seeds/u);
  assert.match(milestone.nonClaim, /explicit input/u);
  assert.match(milestone.nonClaim, /projection-compatible/u);
  assert.match(docs, /Saturated support square closure/u);
  assert.match(docs, /not.*SaturatePositive/isu);
});

test('status earns only the bounded support-square closure', async () => {
  const status = JSON.parse(await text0(STATUS_PATH));
  for (const field of [
    'leanResidualTerminalSupportSquareClosureFormalized',
    'leanResidualTerminalSupportSquareMeetJoinExactFormalized',
    'leanResidualTerminalSupportSquarePhysicalCompatibilityFormalized',
    'leanResidualTerminalSupportSquareSemanticExtractionFormalized',
    'leanResidualTerminalSupportSquareClosureAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  assert.equal(
    status.leanResidualTerminalSupportSquareClosureScope,
    'all-finite-direct-wire-candidates-explicit-terminal-dependency-systems-and-pairs-of-finite-terminal-seeds',
  );
  for (const field of [
    'leanResidualTerminalSquareLegitimacyFormalized',
    'leanResidualTerminalProjectionSquareFormalized',
    'leanSaturatePositiveFormalized',
    'leanBCELReadyFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 6);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-terminal-saturated-support-square-closure',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation names the legacy anchor and exact remaining boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§3', 'Saturated support square closure',
    'every pair of finite seeds', 'greatest lower bound',
    'least upper bound', 'explicit caller data', 'frontier pushout',
    'projection-compatible square', 'BN2 square legitimacy',
    'SaturatePositive', 'ZeroSlack', 'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-support-square-closure0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalSupportSquareClosureAxiomAudit\.lean[\s\S]{0,1800}-eq 40/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalSupportSquareClosure\.lean/u);
});

test('hostile source mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [
      source.replace(
        'record ∈ square.leftRecords ∧ record ∈ square.rightRecords))',
        'record ∈ square.leftRecords ∨ record ∈ square.rightRecords))',
      ),
      'exact-saturated-meet',
    ],
    [
      source.replace(
        'terminalSaturateRecords system (square.leftRecords ++ square.rightRecords)',
        'square.leftRecords ++ square.rightRecords',
      ),
      'saturated-union-join',
    ],
    [source.replace('(sideUnion_closed square)', '(by sorry)'), 'forbidden-shortcut'],
    [
      source.replace('withinRight record member', 'withinLeft record member'),
      'greatest-lower-bound',
    ],
    [
      source.replace('containsRight record rightMember', 'containsLeft record rightMember'),
      'least-upper-bound',
    ],
    [
      source.replace(
        'completeTerminalPhysicalSupport_compatible candidate (square.records corner)',
        'by exact callerCertificate',
      ),
      'caller-or-host-certificate',
    ],
    [
      source.replace(
        'extractTerminalSupport candidate (square.records corner)',
        'extractTerminalSupport candidate fixedSquareTable',
      ),
      'hard-coded-support-family',
    ],
    [`${source}\naxiom squareClosureShortcut : True\n`, 'assumption-declaration'],
    [`${source}\ndef projectionCompatibleSquare : Prop := True\n`, 'overclaim'],
    [`${source}\ndef leaked := PNP.ResidualBandExactMinimization\n`, 'project-axiom'],
    [`${source}\ndef hostLookup := true\n`, 'caller-or-host-certificate'],
    [`${source}\ndef shortcut : True := by native_decide\n`, 'forbidden-shortcut'],
    [`import PNP.ZeroSlack\n${source}`, 'closed-import'],
    [`${source}\nprivate theorem hidden : True := True.intro\n`, 'private-helper-surface'],
    [`${source}\nexample : True := True.intro\n`, 'unaudited-declaration-form'],
  ];
  for (const [mutation, expected] of mutations) {
    assert.equal(validateSource0(mutation).includes(expected), true, expected);
  }
});
