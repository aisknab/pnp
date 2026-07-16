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
const SOURCE = 'lean/PNP/Concrete/CookLevinBuilderTokenAppender.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinBuilderTokenAppenderAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcreteCookLevinBuilderTokenAppender.lean';
const TEST = 'audits/lean-concrete-cook-levin-builder-token-appender0.test.mjs';
const PREFIX = 'PNP.Concrete.CookLevin.BuilderTokenAppender.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'allTokens'],
  ['def', 'tokenCode'],
  ['theorem', 'tokenCode_injective'],
  ['def', 'tokenSymbol'],
  ['theorem', 'tokenSymbol_injective'],
  ['theorem', 'tokenSymbol_bits'],
  ['def', 'outputBoundarySymbol'],
  ['theorem', 'outputBoundarySymbol_ne_tokenSymbol'],
  ['theorem', 'outputBoundarySymbol_ne_tallySymbol'],
  ['theorem', 'outputBoundarySymbol_ne_rightMarker'],
  ['def', 'tokenSymbols'],
  ['theorem', 'tokenSymbols_length'],
  ['theorem', 'tokenSymbols_append'],
  ['theorem', 'tokenSymbols_reverse'],
  ['def', 'outputRegion'],
  ['def', 'workspaceTape'],
  ['theorem', 'workspaceTape_empty_eq_builderInputLength_finalTape'],
  ['theorem', 'workspaceTape_represents'],
  ['def', 'seekInputState'],
  ['def', 'seekTallyState'],
  ['def', 'seekOutputState'],
  ['def', 'rewindOutputState'],
  ['def', 'rewindTallyState'],
  ['def', 'rewindInputState'],
  ['def', 'acceptState'],
  ['def', 'rejectState'],
  ['def', 'keepRule'],
  ['def', 'writeRule'],
  ['def', 'tokenRules'],
  ['def', 'rewindRules'],
  ['def', 'rules'],
  ['def', 'machine'],
  ['theorem', 'rules_length'],
  ['theorem', 'rules_pairwise_query_distinct'],
  ['theorem', 'machine_acceptState_ne_rejectState'],
  ['def', 'entryConfiguration'],
  ['def', 'finalConfiguration'],
  ['def', 'sourceCellCount'],
  ['theorem', 'sourceCellCount_positive'],
  ['theorem', 'sourceCellCount_le'],
  ['def', 'halfSteps'],
  ['def', 'workSteps'],
  ['def', 'firstTokenRawTimeBound'],
  ['def', 'sourceSymbols'],
  ['theorem', 'sourceSymbols_length'],
  ['theorem', 'appendToken_workRunExact'],
  ['def', 'firstHeaderFinalConfiguration'],
  ['theorem', 'firstHeaderToken_workRunExact'],
  ['theorem', 'firstHeaderToken_after_builderInputPrefix'],
  ['theorem', 'finalConfiguration_isHalted'],
  ['theorem', 'firstTokenRawTimeBound_eval'],
  ['theorem', 'firstTokenRawTimeBound_le'],
  ['theorem', 'run_compile_firstHeaderToken_exact'],
  ['theorem', 'run_compile_firstHeaderToken_rawTimeBound'],
  ['theorem', 'firstHeaderToken_workBoundedDecide_accept'],
  ['theorem', 'formulaWidth_positive'],
  ['theorem', 'formulaBitSlotDirect_zero'],
  ['theorem', 'formulaBitSlotDirect_one'],
  ['theorem', 'firstHeaderToken_bits_eq_encodedFormula_take_two'],
  ['def', 'malformedTallyConfiguration'],
  ['theorem', 'malformedTallySymbol_isHalted_false'],
  ['theorem', 'malformedTallySymbol_workStep_none'],
  ['theorem', 'malformedTallySymbol_timeout'],
  ['def', 'malformedOutputConfiguration'],
  ['theorem', 'malformedOutputSymbol_isHalted_false'],
  ['theorem', 'malformedOutputSymbol_workStep_none'],
  ['theorem', 'malformedOutputSymbol_timeout'],
  ['theorem', 'firstHeaderToken_one_step_short_timeout'],
]);

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function publicHeadPairs0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map(({ kind, name }) => [kind, name]);
}

function declarationBlocks0(source) {
  const declarations = explicitLeanDeclarationHeads0(source);
  return declarations.map((declaration, index) => ({
    ...declaration,
    block: source.slice(declaration.index,
      declarations[index + 1]?.index ?? source.length),
  }));
}

function declarationBlock0(source, name) {
  return declarationBlocks0(source)
    .find((entry) => entry.name === name)?.block ?? '';
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const prose = source.replaceAll('\x60', '').replace(/\s+/gu, ' ');
  const executable = ['tokenRules', 'rewindRules', 'rules', 'machine']
    .map((name) => declarationBlock0(stripped, name)).join(' ');

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CookLevinBuilderInputPrefix',
    'PNP.Concrete.CookLevinFormulaCursor',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace BuilderTokenAppender$/mu.test(stripped)
    && /end BuilderTokenAppender\s+end CookLevin\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|referenceMinimum|SATOracle)\b/u
    .test(stripped), 'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('internal builder stage')
    && prose.includes('not yet composed with the input prefix')
    && prose.includes('does not compute the remaining formula header')
    && prose.includes('no complete formula builder')
    && prose.includes('P-equals-NP theorem'), 'explicit-nonclaims');
  require0(!/\b(?:PolynomialReduction|NPComplete|cnfSATInP|cnfSATNPComplete|p_eq_np)\b/u
    .test(stripped), 'no-reduction-or-class-claim');

  require0(compact.includes('def allTokens : List CNFToken := [.f, .t, .sep, .finish]')
    && compact.includes('def tokenCode : CNFToken → Nat | .f => 0 | .t => 1 | .sep => 2 | .finish => 3')
    && compact.includes('def tokenSymbol : CNFToken → WorkSymbol | .f => WorkSymbol.zeroZero | .t => WorkSymbol.oneOne | .sep => WorkSymbol.zeroOne | .finish => WorkSymbol.oneZero')
    && compact.includes('theorem tokenCode_injective')
    && compact.includes('theorem tokenSymbol_injective')
    && compact.includes('theorem tokenSymbol_bits'), 'four-token-injective-code');
  require0(compact.includes('def outputBoundarySymbol : WorkSymbol := WorkSymbol.blankZero')
    && compact.includes('theorem outputBoundarySymbol_ne_tokenSymbol')
    && compact.includes('theorem workspaceTape_empty_eq_builderInputLength_finalTape'),
  'phase-boundary-and-prefix-endpoint');
  require0(compact.includes('def rules : List WorkRule := allTokens.flatMap tokenRules ++ rewindRules')
    && compact.includes('theorem rules_length : rules.length = 59')
    && compact.includes('theorem rules_pairwise_query_distinct'),
  'literal-fixed-table');
  require0(compact.includes('startState := seekInputState .t')
    && compact.includes('acceptState := acceptState')
    && compact.includes('rejectState := rejectState'), 'distinguished-start-and-halts');
  require0(!/\b(?:input|output|problem|formulaBitSlotDirect|encodedFormula|NatPolynomial\.eval|SAT)\b/u
    .test(executable), 'answer-independent-executable-rules');

  require0(compact.includes('theorem appendToken_workRunExact (input : BitString)')
    && compact.includes('(output ++ [request])')
    && compact.includes('theorem firstHeaderToken_workRunExact')
    && compact.includes('theorem firstHeaderToken_after_builderInputPrefix'),
  'uniform-exact-append-and-supplied-prefix-endpoint');
  require0(compact.includes('def firstTokenRawTimeBound : NatPolynomial := .linear 24 48')
    && compact.includes('6 * workSteps input [] ≤ firstTokenRawTimeBound.eval (BitString.size input)')
    && compact.includes('theorem run_compile_firstHeaderToken_rawTimeBound'),
  'compiled-external-bound');
  require0(compact.includes('theorem formulaBitSlotDirect_zero')
    && compact.includes('theorem formulaBitSlotDirect_one')
    && compact.includes('CNFToken.t.bits = problem.encodedFormula.take 2'),
  'first-concrete-formula-bits');
  require0(compact.includes('head := WorkSymbol.zeroZero')
    && compact.includes('theorem malformedTallySymbol_timeout')
    && compact.includes('head := WorkSymbol.zeroBlank')
    && compact.includes('theorem malformedOutputSymbol_timeout'),
  'malformed-phase-timeouts');
  require0(compact.includes('theorem firstHeaderToken_one_step_short_timeout')
    && compact.includes('workSteps input [] - 1')
    && compact.includes('= .timeout := by'), 'one-step-short-timeout');

  return failures;
}

test('Cook-Levin token appender is finite, exact, uniform, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel transcript covers all 68 public declarations exactly once', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE), text0(AUDIT)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 68);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 68);
});

test('root, package, verifier, workflow, and regression enforce the milestone', async () => {
  const [root, packageText, verifier, workflow, regression] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
    text0(REGRESSION),
  ]);
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinBuilderTokenAppender'));
  assert.match(packageText, /audits\/lean-concrete-cook-levin-builder-token-appender0\.test\.mjs/u);
  assert.match(verifier, /audits\/lean-concrete-cook-levin-builder-token-appender0\.test\.mjs/u);
  assert.match(workflow, /PNPConcreteCookLevinBuilderTokenAppenderAxiomAudit\.lean/u);
  assert.match(workflow, /PNPConcreteCookLevinBuilderTokenAppender\.lean/u);
  assert.match(workflow, /Cook-Levin builder token-appender axiom closure/u);
  assert.ok(workflow.includes(
    "grep -Fc 'does not depend on any axioms')\" -eq 42",
  ));
  assert.ok(workflow.includes(
    "grep -Fc 'depends on axioms: [propext]')\" -eq 13",
  ));
  assert.ok(workflow.includes(
    "grep -Fc 'depends on axioms: [propext, Quot.sound]')\" -eq 13",
  ));
  assert.match(regression, /workSteps \(\[\] : BitString\) \[\] = 8[\s\S]*workSteps \(\[true, true, false, false\] : BitString\) \[\] = 22/u);
  assert.match(regression, /tokenSymbol \.f[\s\S]*tokenSymbol \.finish/u);
  assert.match(regression, /inputOnlyProblem[\s\S]*pairedProblem/u);
  assert.match(regression, /malformedTallySymbol_timeout/u);
  assert.match(regression, /malformedOutputSymbol_timeout/u);
  assert.match(regression, /firstHeaderToken_one_step_short_timeout/u);
  assert.equal(TEST.endsWith('0.test.mjs'), true);
});

test('alphabet, table, bound, endpoint, formula, timeout, assumption, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('allTokens : List CNFToken := [.f, .t, .sep, .finish]',
      'allTokens : List CNFToken := [.f, .t, .sep]'),
    source.replace('| .finish => 3', '| .finish => 2'),
    source.replace('| .finish => WorkSymbol.oneZero',
      '| .finish => WorkSymbol.zeroOne'),
    source.replace('allTokens.flatMap tokenRules ++ rewindRules',
      'allTokens.flatMap tokenRules'),
    source.replace('startState := seekInputState .t',
      'startState := seekInputState .f'),
    source.replace('.linear 24 48', '.linear 23 48'),
    source.replaceAll('(output ++ [request])', 'output'),
    source.replace('problem.encodedFormula.take 2', '[false, false]'),
    source.replace('head := WorkSymbol.zeroZero',
      'head := BuilderInputLength.tallySymbol'),
    source.replace('head := WorkSymbol.zeroBlank',
      'head := tokenSymbol .f'),
    source.replaceAll('workSteps input [] - 1', 'workSteps input []'),
    `${source}\naxiom hiddenBuilderOracle : True\n`,
    `${source}\ntheorem cnfSATNPComplete : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('token appender remains below a complete builder, reduction, and class theorems', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCookLevinBuilderTokenAppenderFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderTokenAppenderAxiomAuditPassed, true);
  assert.equal(status.leanConcreteCookLevinBuilderTokenAppenderAuditedDeclarationCount, 68);
  assert.equal(status.leanConcreteCookLevinBuilderTokenAppenderCompiledRawMachineFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderTokenAppenderExternalInputSizePolynomialFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderTokenAppenderFirstFormulaBitsFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderTokenAppenderInputPrefixComposed, true);
  assert.equal(status.leanConcreteCookLevinBuilderFirstTokenPrefixFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderCompleteHeaderFormalized, false);
  assert.equal(status.leanConcreteCookLevinBuilderDynamicCursorFormalized, false);
  assert.equal(status.leanConcreteCookLevinFormulaBuilderFormalized, false);
  assert.equal(status.leanConcreteCookLevinBuilderRawRefinementFormalized, false);
  assert.equal(status.leanConcreteCookLevinBuilderPolynomialReductionFormalized, false);
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
