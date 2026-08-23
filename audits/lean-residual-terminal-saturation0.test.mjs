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
const SOURCE_PATH = 'lean/PNP/ResidualTerminalSaturation.lean';
const AUDIT_PATH = 'lean-audit/PNPResidualTerminalSaturationAxiomAudit.lean';
const REGRESSION_PATH = 'lean-regression/PNPResidualTerminalSaturation.lean';
const INVENTORY_PATH = 'status/LEAN_THEOREM_INVENTORY.json';
const DOCS_PATH = 'docs/lean_residual_terminal_saturation.md';
const NAMESPACE = 'PNP.DirectWire';

const PUBLIC_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.TerminalPrimitiveRecord`,
  `${NAMESPACE}.allTerminalPrimitiveRecords`,
  `${NAMESPACE}.mem_allTerminalPrimitiveRecords`,
  `${NAMESPACE}.TerminalSaturationRuleKind`,
  `${NAMESPACE}.TerminalSaturationSystem`,
  `${NAMESPACE}.TerminalRawSupport`,
  `${NAMESPACE}.TerminalRawSupport.Subset`,
  `${NAMESPACE}.TerminalRawSupport.Closed`,
  `${NAMESPACE}.TerminalSaturationGenerated`,
  `${NAMESPACE}.terminalSaturate`,
  `${NAMESPACE}.terminalSaturate_extensive`,
  `${NAMESPACE}.terminalSaturate_closed`,
  `${NAMESPACE}.terminalSaturate_least`,
  `${NAMESPACE}.terminalSaturate_monotone`,
  `${NAMESPACE}.terminalSaturate_idempotent`,
  `${NAMESPACE}.terminalSaturate_fixed_iff_closed`,
  `${NAMESPACE}.TerminalSaturatedSupport`,
  `${NAMESPACE}.saturateSupport`,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.mem_allTerminalPrimitiveRecords`,
  `${NAMESPACE}.terminalSaturate_extensive`,
  `${NAMESPACE}.terminalSaturate_closed`,
  `${NAMESPACE}.terminalSaturate_least`,
  `${NAMESPACE}.terminalSaturate_monotone`,
  `${NAMESPACE}.terminalSaturate_idempotent`,
  `${NAMESPACE}.terminalSaturate_fixed_iff_closed`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function declarations0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map((head) => {
      if (head.name === 'Subset' || head.name === 'Closed') {
        return `${NAMESPACE}.TerminalRawSupport.${head.name}`;
      }
      return `${NAMESPACE}.${head.name}`;
    });
}

function privateHelpers0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  return [...stripped.matchAll(/^private\s+(?:def|theorem|inductive|structure|abbrev)\s+([^\s({:]+)/gmu)]
    .map((match) => match[1]);
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
  if (/\b(?:Classical(?:\.choice)?|native_decide|exact_mod_cast|linarith|nlinarith|omega|sorry|admit)\b/u.test(stripped)) {
    failures.push('forbidden-shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)) failures.push('host-evaluation');
  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption-declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) failures.push('unaudited-declaration-form');
  if (/\b(?:hostLookup|scheduleLookup|proofCertificate|callerCertificate|trustFlag|dependencyCertificate|saturationCertificate|closureSound)\b/u.test(stripped)) {
    failures.push('caller-or-host-certificate');
  }
  if (/\bPNP\.(?:CheckPCCPackexp|GeneratePCCPack|LockedNANDThreshold|ResidualBandExactMinimization)\b/u.test(stripped)) {
    failures.push('project-axiom');
  }
  if (/(?:def|theorem)\s+(?:p_eq_np|properSupport|supportCompletion|projectionSquare|squareLegitimate|saturatePositive|bcelReady|completeGainRoute|zeroSlackComplete|pccMinExact)\b/iu.test(stripped)) {
    failures.push('overclaim');
  }
  return failures;
}

function validateTerminalSaturationSource0(source) {
  const failures = commonFailures0(source);
  const imports = [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(imports) !== JSON.stringify(['PNP.ResidualTerminalProjectionTransfer'])) {
    failures.push('closed-import');
  }
  if (JSON.stringify(declarations0(source)) !== JSON.stringify(PUBLIC_DECLARATIONS)) {
    failures.push('declaration-surface');
  }
  if (privateHelpers0(source).length !== 0) failures.push('private-helper-surface');

  const primitive = declarationBlock0(source, 'TerminalPrimitiveRecord');
  const allRecords = declarationBlock0(source, 'allTerminalPrimitiveRecords');
  const allRecordsMem = declarationBlock0(source, 'mem_allTerminalPrimitiveRecords');
  const ruleKinds = declarationBlock0(source, 'TerminalSaturationRuleKind');
  const system = declarationBlock0(source, 'TerminalSaturationSystem');
  const rawSupport = declarationBlock0(source, 'TerminalRawSupport');
  const subset = declarationBlock0(source, 'Subset');
  const closed = declarationBlock0(source, 'Closed');
  const generated = declarationBlock0(source, 'TerminalSaturationGenerated');
  const saturate = declarationBlock0(source, 'terminalSaturate');
  const extensive = declarationBlock0(source, 'terminalSaturate_extensive');
  const closure = declarationBlock0(source, 'terminalSaturate_closed');
  const least = declarationBlock0(source, 'terminalSaturate_least');
  const monotone = declarationBlock0(source, 'terminalSaturate_monotone');
  const idempotent = declarationBlock0(source, 'terminalSaturate_idempotent');
  const fixed = declarationBlock0(source, 'terminalSaturate_fixed_iff_closed');
  const packaged = declarationBlock0(source, 'TerminalSaturatedSupport');
  const canonical = declarationBlock0(source, 'saturateSupport');

  for (const constructor of [
    /\| gate \(index : Fin gates\)/u,
    /\| boundary \(index : Fin inputs\)/u,
    /\| interface \(index : Fin outputs\)/u,
    /\| profile \(index : Fin profileWidth\)/u,
  ]) {
    if (!constructor.test(primitive)) failures.push('finite-primitive-universe');
  }
  for (const family of ['gate', 'boundary', 'interface', 'profile']) {
    if (!new RegExp(`allFin[\\s\\S]*TerminalPrimitiveRecord\\.${family}`, 'u').test(allRecords)
        || !new RegExp(`\\| ${family} index =>[\\s\\S]*mem_map_of_mem TerminalPrimitiveRecord\\.${family} \\(mem_allFin index\\)`, 'u').test(allRecordsMem)) {
      failures.push('canonical-universe-completeness');
    }
  }
  const exactRuleKinds = [
    'gateSource', 'interfaceConsumer', 'origin', 'kernel', 'obligation',
    'prefixTail', 'budget', 'saturation', 'direction', 'charge',
  ];
  const actualRuleKinds = [...ruleKinds.matchAll(/^\s*\|\s+([A-Za-z][A-Za-z0-9]*)\s*$/gmu)]
    .map((match) => match[1]);
  if (JSON.stringify(actualRuleKinds) !== JSON.stringify(exactRuleKinds)) {
    failures.push('ten-rule-kinds');
  }
  if (!/profileSystem : TerminalProfileSystem inputs outputs profileWidth/u.test(system)
      || !/requires : TerminalSaturationRuleKind\s*→[\s\S]*TerminalPrimitiveRecord[\s\S]*→\s*Bool/u.test(system)
      || /(?:Certificate|Sound|Valid|Closed)/u.test(system)) {
    failures.push('explicit-dependency-data');
  }
  if (!/TerminalPrimitiveRecord inputs gates outputs profileWidth → Prop/u.test(rawSupport)
      || !/∀ record, left record → right record/u.test(subset)) {
    failures.push('raw-support-subset');
  }
  if (!/∀ kind dependent required,[\s\S]*support dependent → system\.requires kind dependent required = true →[\s\S]*support required/u.test(closed)) {
    failures.push('dependency-orientation');
  }
  if (!/\| seed \{record\} \(member : seed record\)[\s\S]*TerminalSaturationGenerated system seed record/u.test(generated)) {
    failures.push('reflexive-generated-closure');
  }
  if (!/\| close \{kind dependent required\}[\s\S]*TerminalSaturationGenerated system seed dependent[\s\S]*system\.requires kind dependent required = true[\s\S]*TerminalSaturationGenerated system seed required/u.test(generated)) {
    failures.push('transitive-generated-closure');
  }
  if (!/fun record => TerminalSaturationGenerated system seed record/u.test(saturate)
      || !/TerminalSaturationGenerated\.seed member/u.test(extensive)
      || !/TerminalSaturationGenerated\.close present edge/u.test(closure)) {
    failures.push('generated-closure-operator');
  }
  if (!/seedWithin : seed\.Subset support[\s\S]*supportClosed : support\.Closed system[\s\S]*induction generated[\s\S]*supportClosed/u.test(least)) {
    failures.push('least-closed-support');
  }
  if (!/within : left\.Subset right[\s\S]*induction generated[\s\S]*TerminalSaturationGenerated\.seed \(within[\s\S]*TerminalSaturationGenerated\.close ih edge/u.test(monotone)) {
    failures.push('monotone-closure');
  }
  if (!/terminalSaturate system \(terminalSaturate system seed\) =[\s\S]*terminalSaturate system seed[\s\S]*terminalSaturate_least[\s\S]*terminalSaturate_closed[\s\S]*terminalSaturate_extensive/u.test(idempotent)) {
    failures.push('idempotent-closure');
  }
  if (!/terminalSaturate system support = support ↔ support\.Closed system[\s\S]*terminalSaturate_closed[\s\S]*terminalSaturate_least[\s\S]*terminalSaturate_extensive/u.test(fixed)) {
    failures.push('fixed-iff-closed');
  }
  if (!/records : TerminalRawSupport[\s\S]*fixed : terminalSaturate system records = records/u.test(packaged)
      || !/records := terminalSaturate system seed[\s\S]*fixed := terminalSaturate_idempotent system seed/u.test(canonical)) {
    failures.push('canonical-saturated-package');
  }
  return [...new Set(failures)];
}

test('terminal saturation exposes the exact universal finite closure interface', async () => {
  assert.deepEqual(validateTerminalSaturationSource0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all 18 public declarations exactly once', async () => {
  assert.deepEqual(printed0(await text0(AUDIT_PATH)), PUBLIC_DECLARATIONS);
  assert.equal(new Set(PUBLIC_DECLARATIONS).size, PUBLIC_DECLARATIONS.length);
  assert.equal(PUBLIC_DECLARATIONS.length, 18);
  assert.match(await text0('lean/PNP.lean'), /^import PNP\.ResidualTerminalSaturation$/mu);
});

test('compiled closure is approved for every terminal-saturation declaration', async () => {
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

test('regression covers all rule tags, long paths, cycles, emptiness, and isolation', async () => {
  const regression = await text0(REGRESSION_PATH);
  for (const token of [
    'terminalSaturationRegression_all_rules_reach_final',
    'terminalSaturationRegression_unrelated_absent',
    'terminalSaturationRegressionSeed_subset_larger',
    'terminalSaturate_monotone',
    'terminalSaturate_idempotent',
    'terminalSaturate_closed',
    'saturateSupport',
    'allTerminalPrimitiveRecords 0 0 0 0 = []',
    'terminalSaturationCycle_reaches_second',
  ]) assert.equal(regression.includes(token), true, token);
  for (const kind of [
    '.gateSource', '.interfaceConsumer', '.origin', '.kernel', '.obligation',
    '.prefixTail', '.budget', '.saturation', '.direction', '.charge',
  ]) assert.equal(regression.includes(kind), true, kind);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression), /\b(?:Classical(?:\.choice)?|native_decide|sorry|admit)\b/u);
});

test('status earns only terminal saturation closure and preserves downstream blockers', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  for (const field of [
    'leanResidualTerminalSaturationFormalized',
    'leanResidualTerminalSaturationAxiomAuditPassed',
    'leanResidualTerminalPrimitiveUniverseFormalized',
    'leanResidualTerminalSaturationExtensiveFormalized',
    'leanResidualTerminalSaturationLeastFormalized',
    'leanResidualTerminalSaturationMonotoneFormalized',
    'leanResidualTerminalSaturationIdempotentFormalized',
  ]) assert.equal(status[field], true, field);
  assert.equal(status.leanResidualTerminalSaturationScope,
    'all-finite-terminal-primitive-record-universes-with-explicit-boolean-rule-tagged-dependencies');
  for (const field of [
    'leanResidualTerminalProperSupportFormalized',
    'leanResidualTerminalProperSupportSearchCompleteFormalized',
    'leanResidualTerminalProperSupportExactLocalGainFormalized',
    'leanResidualTerminalProperSupportAxiomAuditPassed',
  ]) assert.equal(status[field], true, field);
  for (const field of [
    'leanSaturatePositiveFormalized',
    'leanBCELReadyFormalized',
    'leanResidualRoutesGlobalGainCompletenessFormalized',
    'leanZeroSlackCompletenessFormalized',
    'leanPCCMinLoopExactnessFormalized',
    'leanPCCMinPolynomialRuntimeFormalized',
  ]) assert.equal(status[field], false, field);
  assert.equal(status.remainingBlockers.length, 5);
  assert.equal(status.projectSpecificAxiomInventory.length > 0, status.projectSpecificAxiomsRemaining);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  const milestone = status.formalPublicationMilestones.find(
    ({ id }) => id === 'residual-terminal-saturation-closure',
  );
  assert.equal(milestone?.earned, true);
  assert.deepEqual(milestone?.requiredTheorems, MILESTONE_THEOREMS);
});

test('documentation records the legacy closure anchor and exact open boundary', async () => {
  const docs = (await text0(DOCS_PATH)).replaceAll(/\s+/gu, ' ');
  for (const token of [
    '§3', 'Saturated support calculus and square closure', 'Saturation closure',
    'finite primitive-record universe', 'ten', 'least', 'idempotent',
    'proper support', 'square legitimacy', 'SaturatePositive', 'BCEL',
    'ZeroSlack', 'polynomial runtime', 'P = NP',
  ]) assert.equal(docs.includes(token), true, token);
});

test('durable workflow runs transcript, regression, and hostile audit', async () => {
  const workflow = await text0('.github/workflows/lean-bridge.yml');
  assert.match(workflow, /audits\/lean-residual-terminal-saturation0\.test\.mjs/u);
  assert.match(workflow, /PNPResidualTerminalSaturationAxiomAudit\.lean[\s\S]{0,1800}-eq 18/u);
  assert.match(workflow, /lean-regression\/PNPResidualTerminalSaturation\.lean/u);
});

test('hostile mutations revoke terminal-saturation credit', async () => {
  const source = await text0(SOURCE_PATH);
  assert.equal(validateTerminalSaturationSource0(source.replace(
    '  | profile (index : Fin profileWidth)\n',
    '',
  )).includes('finite-primitive-universe'), true);
  assert.equal(validateTerminalSaturationSource0(source.replace(
    '  | charge\n',
    '  | ungoverned\n',
  )).includes('ten-rule-kinds'), true);
  assert.equal(validateTerminalSaturationSource0(source.replace(
    'support dependent → system.requires kind dependent required = true →\n      support required',
    'support required → system.requires kind dependent required = true →\n+      support dependent',
  )).includes('dependency-orientation'), true);
  assert.equal(validateTerminalSaturationSource0(source.replace(
    '  | seed {record} (member : seed record) :\n      TerminalSaturationGenerated system seed record\n',
    '',
  )).includes('reflexive-generated-closure'), true);
  assert.equal(validateTerminalSaturationSource0(source.replace(
    '(present : TerminalSaturationGenerated system seed dependent)',
    '(present : seed dependent)',
  )).includes('transitive-generated-closure'), true);
  assert.equal(validateTerminalSaturationSource0(source.replace(
    'terminalSaturate system (terminalSaturate system seed) =\n      terminalSaturate system seed',
    'terminalSaturate system seed = terminalSaturate system seed',
  )).includes('idempotent-closure'), true);
  assert.equal(validateTerminalSaturationSource0(`import PNP.ZeroSlack\n${source}`).includes('closed-import'), true);
  assert.equal(validateTerminalSaturationSource0(`${source}\naxiom hidden : True\n`).includes('assumption-declaration'), true);
  assert.equal(validateTerminalSaturationSource0(`${source}\nprivate theorem hidden : True := True.intro\n`).includes('private-helper-surface'), true);
  assert.equal(validateTerminalSaturationSource0(`${source}\nexample : True := True.intro\n`).includes('unaudited-declaration-form'), true);
  assert.equal(validateTerminalSaturationSource0(`${source}\ntheorem hidden : True := by native_decide\n`).includes('forbidden-shortcut'), true);
  assert.equal(validateTerminalSaturationSource0(`${source}\ndef callerCertificate := true\n`).includes('caller-or-host-certificate'), true);
  assert.equal(validateTerminalSaturationSource0(`${source}\ntheorem properSupport : True := True.intro\n`).includes('overclaim'), true);
  assert.equal(validateTerminalSaturationSource0(`${source}\ntheorem p_eq_np : True := True.intro\n`).includes('overclaim'), true);
});
