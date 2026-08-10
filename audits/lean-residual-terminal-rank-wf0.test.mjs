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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalRankWF.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalRankWFAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalRankWF.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const PUBLICATION_PATH = 'publication/FORMAL_PUBLICATION_MAP.json';
const STATUS_PATH = 'status/FORMAL_RECONSTRUCTION_STATUS.json';
const DOCS_PATH = 'docs/lean_residual_terminal_rank_wf.md';
const NAMESPACE = 'PNP.DirectWire';

const LOCAL_DECLARATIONS = Object.freeze([
  'TerminalResidualRank',
  'mk',
  'witnessType',
  'spanType',
  'mode',
  'frontierDefect',
  'projectionDefect',
  'saturationDefect',
  'anchorCount',
  'chargeSize',
  'profileSize',
  'canonicalCode',
  'coordinates',
  'coordinates_mk',
  'coordinates_length',
  'terminalResidualRankWellFoundedRelation',
  'TerminalResidualRank.LexLT',
  'terminalResidualRankLTBool',
  'terminalResidualRankLTBool_eq_true_iff',
  'terminalResidualRankLTBool_eq_false_iff',
  'terminalResidualRankLexLT_wellFounded',
  'terminalResidualRank_accessible',
  'terminalResidualRank_induction',
  'terminalResidualRank_witnessType_lt',
  'terminalResidualRank_spanType_lt',
  'terminalResidualRank_mode_lt',
  'terminalResidualRank_frontierDefect_lt',
  'terminalResidualRank_projectionDefect_lt',
  'terminalResidualRank_saturationDefect_lt',
  'terminalResidualRank_anchorCount_lt',
  'terminalResidualRank_chargeSize_lt',
  'terminalResidualRank_profileSize_lt',
  'terminalResidualRank_canonicalCode_lt',
  'TerminalResidualRankDescent',
  'TerminalResidualRankDescent.Sound',
  'TerminalResidualRankDescent.sound',
]);

const AUDITED_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalResidualRank`,
  `${NAMESPACE}.TerminalResidualRank.mk`,
  `${NAMESPACE}.TerminalResidualRank.witnessType`,
  `${NAMESPACE}.TerminalResidualRank.spanType`,
  `${NAMESPACE}.TerminalResidualRank.mode`,
  `${NAMESPACE}.TerminalResidualRank.frontierDefect`,
  `${NAMESPACE}.TerminalResidualRank.projectionDefect`,
  `${NAMESPACE}.TerminalResidualRank.saturationDefect`,
  `${NAMESPACE}.TerminalResidualRank.anchorCount`,
  `${NAMESPACE}.TerminalResidualRank.chargeSize`,
  `${NAMESPACE}.TerminalResidualRank.profileSize`,
  `${NAMESPACE}.TerminalResidualRank.canonicalCode`,
  `${NAMESPACE}.TerminalResidualRank.coordinates`,
  `${NAMESPACE}.TerminalResidualRank.coordinates_mk`,
  `${NAMESPACE}.TerminalResidualRank.coordinates_length`,
  `${NAMESPACE}.terminalResidualRankWellFoundedRelation`,
  `${NAMESPACE}.TerminalResidualRank.LexLT`,
  `${NAMESPACE}.terminalResidualRankLTBool`,
  `${NAMESPACE}.terminalResidualRankLTBool_eq_true_iff`,
  `${NAMESPACE}.terminalResidualRankLTBool_eq_false_iff`,
  `${NAMESPACE}.terminalResidualRankLexLT_wellFounded`,
  `${NAMESPACE}.terminalResidualRank_accessible`,
  `${NAMESPACE}.terminalResidualRank_induction`,
  `${NAMESPACE}.terminalResidualRank_witnessType_lt`,
  `${NAMESPACE}.terminalResidualRank_spanType_lt`,
  `${NAMESPACE}.terminalResidualRank_mode_lt`,
  `${NAMESPACE}.terminalResidualRank_frontierDefect_lt`,
  `${NAMESPACE}.terminalResidualRank_projectionDefect_lt`,
  `${NAMESPACE}.terminalResidualRank_saturationDefect_lt`,
  `${NAMESPACE}.terminalResidualRank_anchorCount_lt`,
  `${NAMESPACE}.terminalResidualRank_chargeSize_lt`,
  `${NAMESPACE}.terminalResidualRank_profileSize_lt`,
  `${NAMESPACE}.terminalResidualRank_canonicalCode_lt`,
  `${NAMESPACE}.TerminalResidualRankDescent`,
  `${NAMESPACE}.TerminalResidualRankDescent.before`,
  `${NAMESPACE}.TerminalResidualRankDescent.after`,
  `${NAMESPACE}.TerminalResidualRankDescent.decreasing`,
  `${NAMESPACE}.TerminalResidualRankDescent.Sound`,
  `${NAMESPACE}.TerminalResidualRankDescent.sound`,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.TerminalResidualRank.coordinates_mk`,
  `${NAMESPACE}.TerminalResidualRank.coordinates_length`,
  `${NAMESPACE}.terminalResidualRankLTBool_eq_true_iff`,
  `${NAMESPACE}.terminalResidualRankLTBool_eq_false_iff`,
  `${NAMESPACE}.terminalResidualRankLexLT_wellFounded`,
  `${NAMESPACE}.terminalResidualRank_accessible`,
  `${NAMESPACE}.terminalResidualRank_induction`,
  `${NAMESPACE}.terminalResidualRank_witnessType_lt`,
  `${NAMESPACE}.terminalResidualRank_spanType_lt`,
  `${NAMESPACE}.terminalResidualRank_mode_lt`,
  `${NAMESPACE}.terminalResidualRank_frontierDefect_lt`,
  `${NAMESPACE}.terminalResidualRank_projectionDefect_lt`,
  `${NAMESPACE}.terminalResidualRank_saturationDefect_lt`,
  `${NAMESPACE}.terminalResidualRank_anchorCount_lt`,
  `${NAMESPACE}.terminalResidualRank_chargeSize_lt`,
  `${NAMESPACE}.terminalResidualRank_profileSize_lt`,
  `${NAMESPACE}.terminalResidualRank_canonicalCode_lt`,
  `${NAMESPACE}.TerminalResidualRankDescent.sound`,
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

function commonFailures0(source) {
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
  if (/\b(?:callerRank|callerRelation|callerWellFounded|rankComplete|trustFlag)\b/u.test(stripped)) {
    failures.push('caller-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|saturatePositive|bcelReady|routeComplete)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateSource0(source) {
  const failures = commonFailures0(source);
  if (JSON.stringify(declarationNames0(source))
      !== JSON.stringify(LOCAL_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify([
    'PNP.ResidualTerminalFiniteSaturatePositive',
  ])) failures.push('closed-import');

  const rank = declarationBlock0(source, 'TerminalResidualRank');
  if ((rank.match(/\bNat\b/gu) ?? []).length !== 10
      || (rank.match(/×/gu) ?? []).length !== 9) {
    failures.push('exact-ten-coordinate-rank');
  }

  const coordinates = declarationBlock0(source, 'coordinates');
  const orderedCoordinates = [
    'rank.witnessType', 'rank.spanType', 'rank.mode',
    'rank.frontierDefect', 'rank.projectionDefect',
    'rank.saturationDefect', 'rank.anchorCount', 'rank.chargeSize',
    'rank.profileSize', 'rank.canonicalCode',
  ];
  let previous = -1;
  for (const coordinate of orderedCoordinates) {
    const current = coordinates.indexOf(coordinate);
    if (current <= previous) failures.push('coordinate-priority');
    previous = current;
  }

  const relation = declarationBlock0(source,
    'terminalResidualRankWellFoundedRelation');
  if ((relation.match(/Prod\.lex/gu) ?? []).length !== 9
      || (relation.match(/Nat\.lt_wfRel/gu) ?? []).length !== 10) {
    failures.push('exact-well-founded-product');
  }

  const lex = declarationBlock0(source, 'TerminalResidualRank.LexLT');
  if (!lex.includes('rel after before')) failures.push('descending-orientation');

  const decision = source.slice(source.indexOf('private def decidableProdLex'),
    source.indexOf('/-- Executable projection'));
  for (const token of [
    'Nat.decLt', 'Prod.Lex.left', 'Prod.Lex.right',
    'terminalResidualRankLexLTDecidableRel',
    'Decidable (after.LexLT before)',
  ]) if (!decision.includes(token)) failures.push('relation-derived-decision');

  const bool = declarationBlock0(source, 'terminalResidualRankLTBool');
  if (!bool.includes('decide (after.LexLT before)')) {
    failures.push('executable-proof-relation');
  }

  const wf = declarationBlock0(source,
    'terminalResidualRankLexLT_wellFounded');
  if (!wf.includes('terminalResidualRankWellFoundedRelation.wf')) {
    failures.push('kernel-well-foundedness');
  }

  const descent = declarationBlock0(source, 'TerminalResidualRankDescent');
  for (const token of [
    'before : TerminalResidualRank', 'after : TerminalResidualRank',
    'decreasing : after.LexLT before',
  ]) if (!descent.includes(token)) failures.push('proof-bearing-descent');

  for (const theorem of LOCAL_DECLARATIONS.filter((name) =>
    name.startsWith('terminalResidualRank_') && name.endsWith('_lt'))) {
    const block = declarationBlock0(source, theorem);
    if (!block.includes('Prod.Lex.')) failures.push('coordinate-priority-witness');
  }
  return [...new Set(failures)];
}

test('residual rank source fixes ten coordinates and derives RankWF', async () => {
  assert.deepEqual(validateSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers the exact 39-declaration boundary', async () => {
  const audit = await text0(AUDIT_PATH);
  assert.deepEqual(printed0(audit), AUDITED_DECLARATIONS);
  assert.equal(new Set(AUDITED_DECLARATIONS).size, 39);
  assert.equal(audit.startsWith('import PNP.ResidualTerminalRankWF\n'), true);
  assert.match(await text0('lean/PNP.lean'),
    /^import PNP\.ResidualTerminalRankWF$/mu);
});

test('compiled inventory approves every public rank declaration', async () => {
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
  }
});

test('regression checks all priorities, reversal, descent, and induction', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'coordinates.length = 10',
    'terminalResidualRankLTBool rankZero rankZero = false',
    'terminalResidualRankLTBool rankZero rankWitnessBefore = true',
    'terminalResidualRank_witnessType_lt',
    'terminalResidualRank_spanType_lt',
    'terminalResidualRank_mode_lt',
    'terminalResidualRank_frontierDefect_lt',
    'terminalResidualRank_projectionDefect_lt',
    'terminalResidualRank_saturationDefect_lt',
    'terminalResidualRank_anchorCount_lt',
    'terminalResidualRank_chargeSize_lt',
    'terminalResidualRank_profileSize_lt',
    'terminalResidualRank_canonicalCode_lt',
    'rankEarlierLargerLaterSmallerAfter',
    'TerminalResidualRankDescent', 'rankCodeDescent.sound',
    'terminalResidualRank_induction',
  ]) assert.equal(regression.includes(token), true, token);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:Classical(?:\.choice)?|native_decide|bv_decide|grind|omega|sorry|admit)\b/u);
});

test('publication and status earn only the fixed RankWF milestone', async () => {
  const [publication, status, docs] = await Promise.all([
    text0(PUBLICATION_PATH).then(JSON.parse),
    text0(STATUS_PATH).then(JSON.parse),
    text0(DOCS_PATH),
  ]);
  const milestone = publication.milestones.find(
    ({ id }) => id === 'residual-terminal-rank-wf',
  );
  assert.equal(milestone?.classification,
    'formalized-residual-terminal-rank-wf');
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
  assert.match(milestone.scope, /ten natural coordinates/u);
  assert.match(milestone.scope, /well-founded/u);
  assert.match(milestone.nonClaim, /does not map/u);
  assert.match(milestone.nonClaim, /strictly decreases/u);
  assert.equal(status.leanResidualTerminalRankWFFormalized, true);
  assert.equal(status.leanResidualTerminalRankWFAxiomAuditPassed, true);
  assert.match(status.leanResidualTerminalRankWFScope,
    /fixed-ten-coordinate-natural-lexicographic-order/u);
  assert.equal(status.leanSaturatePositiveFormalized, false);
  assert.equal(status.leanBCELReadyFormalized, false);
  assert.equal(status.mathematicalTheoremEstablished, false);
  assert.equal(status.publicTheoremEmissionAllowed, false);
  assert.equal(status.remainingBlockers.length, 6);
  assert.match(docs, /Residual terminal `RankWF`/u);
  assert.match(docs, /does not map the current finite terminal routes/u);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow,
    /audits\/lean-residual-terminal-rank-wf0\.test\.mjs/u);
  assert.match(workflow,
    /PNPResidualTerminalRankWFAxiomAudit\.lean[\s\S]{0,1800}-eq 39/u);
  assert.match(workflow,
    /lean-regression\/PNPResidualTerminalRankWF\.lean/u);
});

test('hostile rank mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    [source.replace('Nat × (Nat × (Nat ×', 'Nat × (Nat ×'),
      'exact-ten-coordinate-rank'],
    [source.replace('rank.witnessType, rank.spanType',
      'rank.spanType, rank.witnessType'), 'coordinate-priority'],
    [source.replace('Prod.lex Nat.lt_wfRel\n', 'Prod.lex callerWellFounded\n'),
      'caller-certificate'],
    [source.replace('rel after before', 'rel before after'),
      'descending-orientation'],
    [source.replace('decide (after.LexLT before)', 'true'),
      'executable-proof-relation'],
    [source.replace('decreasing : after.LexLT before',
      'decreasing : Bool'), 'proof-bearing-descent'],
    [`${source}\naxiom rankShortcut : True\n`, 'assumption-declaration'],
  ];
  for (const [mutated, expected] of mutations) {
    assert.equal(validateSource0(mutated).includes(expected), true, expected);
  }
});
