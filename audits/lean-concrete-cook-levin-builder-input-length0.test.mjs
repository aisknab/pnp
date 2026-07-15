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
const SOURCE = 'lean/PNP/Concrete/CookLevinBuilderInputLength.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinBuilderInputLengthAxiomAudit.lean';
const REGRESSION = 'lean-regression/PNPConcreteCookLevinBuilderInputLength.lean';
const TEST = 'audits/lean-concrete-cook-levin-builder-input-length0.test.mjs';
const PREFIX = 'PNP.Concrete.CookLevin.BuilderInputLength.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'markedZeroSymbol'],
  ['def', 'markedOneSymbol'],
  ['def', 'tallySymbol'],
  ['def', 'scanState'],
  ['def', 'seekRightState'],
  ['def', 'seekTallyEndState'],
  ['def', 'returnTallyState'],
  ['def', 'seekMarkedState'],
  ['def', 'rewindState'],
  ['def', 'emptyFinishState'],
  ['def', 'acceptState'],
  ['def', 'rejectState'],
  ['def', 'keepRule'],
  ['def', 'writeRule'],
  ['def', 'rules'],
  ['def', 'machine'],
  ['theorem', 'rules_length'],
  ['theorem', 'rules_pairwise_query_distinct'],
  ['theorem', 'markedZeroSymbol_ne_markedOneSymbol'],
  ['theorem', 'tallySymbol_ne_markedZeroSymbol'],
  ['theorem', 'tallySymbol_ne_markedOneSymbol'],
  ['def', 'inputTape'],
  ['def', 'finalTape'],
  ['def', 'finalConfiguration'],
  ['theorem', 'finalTape_represents'],
  ['theorem', 'finalTape_tally_length'],
  ['def', 'workSteps'],
  ['def', 'rawTimeBound'],
  ['def', 'tallySizeBound'],
  ['theorem', 'tallySizeBound_exact'],
  ['theorem', 'malformedScanSymbol_timeout'],
  ['theorem', 'workRunExact'],
  ['theorem', 'finalConfiguration_isHalted'],
  ['theorem', 'rawTimeBound_exact'],
  ['theorem', 'run_compile'],
  ['theorem', 'workBoundedDecide_accept'],
  ['theorem', 'work_one_step_short_timeout'],
  ['theorem', 'inputTape_eq_totalInputFramerFinalTape'],
  ['theorem', 'workRunExact_after_totalInputFramer'],
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
  const rulesBlock = declarationBlock0(stripped, 'rules');
  const machineBlock = declarationBlock0(stripped, 'machine');

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.PipelineInputFramer',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /^namespace BuilderInputLength$/mu.test(stripped)
    && /end BuilderInputLength\s+end CookLevin\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|referenceMinimum|SATOracle)\b/u
    .test(stripped), 'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('literal input-length tally stage')
    && prose.includes('not a formula builder')
    && prose.includes('slot interpreter')
    && prose.includes('polynomial reduction')
    && prose.includes('complexity-class result'), 'explicit-nonclaims');
  require0(!/\b(?:PolynomialReduction|NPComplete|cnfSATInP|cnfSATNPComplete|p_eq_np|formulaBuilder)\b/u
    .test(stripped), 'no-reduction-or-class-claim');

  require0(compact.includes('def markedZeroSymbol : WorkSymbol := WorkSymbol.zeroZero')
    && compact.includes('def markedOneSymbol : WorkSymbol := WorkSymbol.oneZero')
    && compact.includes('def tallySymbol : WorkSymbol := WorkSymbol.oneOne'),
  'fixed-disjoint-symbols');
  require0(compact.includes('def rules : List WorkRule := [writeRule scanState WorkSymbol.zeroBlank seekRightState markedZeroSymbol .right')
    && compact.includes('writeRule scanState WorkSymbol.oneBlank seekRightState markedOneSymbol .right')
    && compact.includes('writeRule seekTallyEndState WorkSymbol.blank returnTallyState tallySymbol .left')
    && compact.includes('writeRule seekMarkedState markedZeroSymbol scanState WorkSymbol.zeroBlank .right')
    && compact.includes('writeRule seekMarkedState markedOneSymbol scanState WorkSymbol.oneBlank .right')
    && compact.includes('keepRule rewindState leftMarker acceptState .right]'),
  'literal-restoring-tally-rules');
  require0(compact.includes('def machine : WorkMachine := { rules := rules startState := scanState acceptState := acceptState rejectState := rejectState }')
    && compact.includes('theorem rules_length : rules.length = 19'),
  'fixed-19-rule-machine');
  require0(!/\binput\b/u.test(rulesBlock)
    && !/\binput\b/u.test(machineBlock)
    && !/formulaBitSlotDirect|NatPolynomial\.eval/u.test(rulesBlock + machineBlock),
  'answer-independent-executable-rules');

  require0(compact.includes('def inputTape (input : BitString) (outsideLeft : List WorkSymbol) : WorkTape := frameWithGarbage (Tape.ofInput input) outsideLeft []')
    && compact.includes('List.replicate input.length tallySymbol'),
  'fresh-right-workspace-and-exact-tally');
  require0(compact.includes('def workSteps (n : Nat) : Nat := 2 * n * n + 4 * n + 2')
    && compact.includes('def rawTimeBound : NatPolynomial := .add (.quadratic 12 12) (.linear 24 0)')
    && compact.includes('def tallySizeBound : NatPolynomial := .variable'),
  'explicit-external-polynomials');
  require0(compact.includes('theorem malformedScanSymbol_timeout (fuel : Nat)')
    && compact.includes('head := WorkSymbol.zeroOne')
    && compact.includes('= .timeout := by'), 'malformed-symbol-timeout');
  require0(compact.includes('theorem workRunExact (input : BitString) (outsideLeft : List WorkSymbol)')
    && compact.includes('workRunExact? machine (workSteps input.length)')
    && compact.includes('some (finalConfiguration input outsideLeft)'),
  'all-input-exact-trace');
  require0(compact.includes('theorem run_compile (input : BitString) (outsideLeft : List WorkSymbol)')
    && compact.includes('rawTimeBound.eval (BitString.size input)')
    && compact.includes('encodeWorkConfiguration (finalConfiguration input outsideLeft)'),
  'compiled-exact-trace');
  require0(compact.includes('theorem work_one_step_short_timeout (input : BitString)')
    && compact.includes('workSteps input.length - 1')
    && compact.includes('= .timeout := by'), 'one-step-short-timeout');
  require0(compact.includes('theorem inputTape_eq_totalInputFramerFinalTape (input : BitString)')
    && compact.includes('theorem workRunExact_after_totalInputFramer (input : BitString)')
    && compact.includes('PipelineInputFramer.totalInputFramerFinalTape input'),
  'total-framer-endpoint-connection');

  return failures;
}

test('Cook-Levin builder input-length stage is literal, exact, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel transcript covers all 39 public declarations exactly once', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE), text0(AUDIT)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 39);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 39);
});

test('root, package, verifier, workflow, and regression enforce the milestone', async () => {
  const [root, packageText, verifier, workflow, regression] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'),
    text0('scripts/pnp-verify-all.mjs'), text0('.github/workflows/lean-bridge.yml'),
    text0(REGRESSION),
  ]);
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinBuilderInputLength'));
  assert.match(packageText, /audits\/lean-concrete-cook-levin-builder-input-length0\.test\.mjs/u);
  assert.match(verifier, /audits\/lean-concrete-cook-levin-builder-input-length0\.test\.mjs/u);
  assert.match(workflow, /PNPConcreteCookLevinBuilderInputLengthAxiomAudit\.lean/u);
  assert.match(workflow, /PNPConcreteCookLevinBuilderInputLength\.lean/u);
  assert.match(workflow, /Cook-Levin builder input-length axiom closure/u);
  assert.match(regression, /workSteps 0 = 2[\s\S]*workSteps 4 = 50/u);
  assert.match(regression, /rawTimeBound\.eval 0 = 12[\s\S]*rawTimeBound\.eval 4 = 300/u);
  assert.match(regression, /\[false, false, false, false\][\s\S]*\[true, true, true, true\]/u);
  assert.match(regression, /work_one_step_short_timeout/u);
  assert.match(regression, /malformedScanSymbol_timeout/u);
  assert.match(regression, /workRunExact_after_totalInputFramer/u);
  assert.equal(TEST.endsWith('0.test.mjs'), true);
});

test('symbol, restoration, bound, workspace, timeout, assumption, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('def tallySymbol : WorkSymbol := WorkSymbol.oneOne',
      'def tallySymbol : WorkSymbol := WorkSymbol.zeroOne'),
    source.replace('markedZeroSymbol .right,', 'WorkSymbol.zeroBlank .right,'),
    source.replace('.quadratic 12 12', '.quadratic 11 12'),
    source.replace('2 * n * n + 4 * n + 2', '2 * n * n + 3 * n + 2'),
    source.replaceAll('workSteps input.length - 1', 'workSteps input.length'),
    source.replace('(Tape.ofInput input) outsideLeft []',
      '(Tape.ofInput input) outsideLeft [tallySymbol]'),
    `${source}\naxiom hiddenLengthOracle : True\n`,
    `${source}\ntheorem cnfSATNPComplete : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('input-length tally remains below a formula builder, reduction, and class theorem', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCookLevinBuilderInputLengthFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputLengthAxiomAuditPassed, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputLengthAuditedDeclarationCount, 39);
  assert.equal(status.leanConcreteCookLevinBuilderInputLengthCompiledRawMachineFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputLengthExternalInputSizePolynomialFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputLengthMalformedInternalInputTimeoutFormalized, true);
  assert.equal(status.leanConcreteCookLevinBuilderInputLengthConnectedToTotalInputFramerEndpointFormalized, true);
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
