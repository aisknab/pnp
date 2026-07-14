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
const SOURCE_PATH = 'lean/PNP/Concrete/PipelineInputFramer.lean';
const AUDIT_PATH = 'lean-audit/PNPConcretePipelineInputFramerAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.PipelineInputFramer.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'sourceSymbols'],
  ['inductive', 'SourceSymbol'],
  ['inductive', 'InputSourceSymbol'],
  ['inductive', 'PartialSourceSymbol'],
  ['def', 'bootState'],
  ['def', 'installOuterState'],
  ['def', 'seekSourceEndState'],
  ['def', 'installRightState'],
  ['def', 'returnOuterState'],
  ['def', 'seekUnprocessedState'],
  ['def', 'carryZeroZeroState'],
  ['def', 'carryZeroOneState'],
  ['def', 'carryOneZeroState'],
  ['def', 'carryOneOneState'],
  ['def', 'appendZeroState'],
  ['def', 'appendOneState'],
  ['def', 'installMovingRightState'],
  ['def', 'acceptState'],
  ['def', 'rejectState'],
  ['def', 'partialZeroState'],
  ['def', 'partialOneState'],
  ['def', 'partialInstallRightState'],
  ['def', 'emptyInstallLeftState'],
  ['def', 'emptyReturnHeadState'],
  ['def', 'emptyInstallRightState'],
  ['def', 'keepRule'],
  ['def', 'writeRule'],
  ['def', 'bootRules'],
  ['def', 'seekSourceEndRules'],
  ['def', 'returnSymbols'],
  ['def', 'returnOuterRules'],
  ['def', 'seekUnprocessedRules'],
  ['def', 'carryScanSymbols'],
  ['def', 'carryScanRules'],
  ['def', 'carryBoundaryRules'],
  ['def', 'framerRules'],
  ['def', 'pairedInputFramer'],
  ['def', 'packedPairCount'],
  ['def', 'inputFramerWorkSteps'],
  ['def', 'partialInputFramerWorkSteps'],
  ['def', 'packedInputCount'],
  ['def', 'inputHasPartialCell'],
  ['def', 'totalInputFramerWorkSteps'],
  ['inductive', 'CarryScanSymbol'],
  ['def', 'pairedInputFramerOutsideLeft'],
  ['def', 'pairedInputFramerFinalTape'],
  ['def', 'pairedInputFramerFinalConfiguration'],
  ['theorem', 'pairedInputFramerFinal_represents'],
  ['theorem', 'pairedInputFramer_workRunExact'],
  ['def', 'pairedInputFramerRawTimeBound'],
  ['theorem', 'pairedInputFramerRawTimeBound_exact'],
  ['theorem', 'run_compilePairedInputFramer_rawTimeBound'],
  ['theorem', 'pairedInputFramerFinal_isHalted'],
  ['theorem', 'boundedDecide_compilePairedInputFramer_accept'],
  ['def', 'totalInputFramerOutsideLeft'],
  ['def', 'totalInputFramerFinalTape'],
  ['def', 'totalInputFramerFinalConfiguration'],
  ['theorem', 'totalInputFramerFinal_represents'],
  ['theorem', 'totalInputFramer_workRunExact'],
  ['theorem', 'totalInputFramerWorkSteps_empty'],
  ['def', 'totalInputFramerRawTimeBound'],
  ['theorem', 'totalInputFramerRawTimeBound_le'],
  ['theorem', 'totalInputFramerFinal_isHalted'],
  ['theorem', 'run_compileTotalInputFramer_encoded_rawTimeBound'],
  ['theorem', 'run_compileTotalInputFramer_rawTimeBound_blankEquivalent'],
  ['theorem', 'boundedDecide_compileTotalInputFramer_accept'],
  ['theorem', 'boundedDecide_compileTotalInputFramer_ne_timeout'],
  ['theorem', 'workBoundedDecide_totalInputFramer_empty_oneStepShort'],
  ['theorem', 'workBoundedDecide_totalInputFramer_zero_oneStepShort'],
  ['theorem', 'workBoundedDecide_totalInputFramer_one_oneStepShort'],
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)]
    .map((match) => match[1]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function publicHeadPairs0(source) {
  return explicitLeanDeclarationHeads0(source)
    .map(({ kind, name }) => [kind, name]);
}

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);
  const prose = source.replaceAll('\x60', '').replace(/\s+/gu, ' ');

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.PipelineTapeGeometry',
    'PNP.Concrete.TapeBlankEquivalence',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace PipelineInputFramer$/mu.test(stripped)
    && /end PipelineInputFramer\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|ac_rfl|aesop|simp_all|grind|Classical|funext|propext)\b/u.test(stripped)
    && !/Nat\.(?:add_mul|mul_assoc|mul_left_comm)\b/u.test(stripped),
    'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('The all-input declarations additionally handle the empty word and an odd final raw cell by literal finite transitions.')
    && prose.includes('They do not combine the framer with a simulated machine')
    && prose.includes('prove malformed-input semantics for the full pipeline')
    && prose.includes('construct a pipeline refinement, or establish any complexity-class equality.'),
  'explicit-nonclaims');
  require0(!/\b(?:liftMachine|RawRefinement|FunctionProgram|DecisionProgram|machineOutput|outputBits|handoffTarget|CNFSAT|PEqualsNP)\b/u
    .test(stripped), 'no-composition-or-class-claim');

  require0(compact.includes('def pairedInputFramer : WorkMachine := { rules := framerRules startState := bootState acceptState := acceptState rejectState := rejectState }'),
    'literal-finite-work-machine');
  require0(compact.includes('def packedPairCount (left right : BitString) : Nat := left.length + right.length + 1'),
    'packed-pair-count');
  require0(compact.includes('def inputFramerWorkSteps (packedCells : Nat) : Nat := 4 * packedCells * packedCells + 9 * packedCells + 7'),
    'exact-work-cost');
  require0(compact.includes('def partialInputFramerWorkSteps (packedCells : Nat) : Nat := 4 * packedCells * packedCells + 9 * packedCells + 5'),
    'exact-partial-work-cost');
  require0(compact.includes('def partialZeroState : Nat := 15')
    && compact.includes('def partialInstallRightState : Nat := 17')
    && compact.includes('def emptyInstallLeftState : Nat := 18')
    && compact.includes('def emptyInstallRightState : Nat := 20'),
  'literal-total-control-states');
  require0(compact.includes('writeRule seekUnprocessedState WorkSymbol.zeroBlank partialZeroState WorkSymbol.blank .right')
    && compact.includes('writeRule partialInstallRightState WorkSymbol.blank returnOuterState rightMarker .left')
    && compact.includes('writeRule emptyInstallRightState WorkSymbol.blank acceptState rightMarker .left'),
  'literal-empty-and-partial-rules');
  require0(compact.includes('List.replicate (packedPairCount left right) WorkSymbol.blank ++ [rightMarker]'),
    'exterior-garbage-shape');
  require0(compact.includes('frameWithGarbage (Tape.ofInput (BitString.pair left right)) (pairedInputFramerOutsideLeft left right) []'),
    'represented-frame-endpoint');
  require0(compact.includes('workRunExact? pairedInputFramer (inputFramerWorkSteps (packedPairCount left right)) (workStartConfiguration pairedInputFramer (pairedWorkTape left right)) = some (pairedInputFramerFinalConfiguration left right)'),
    'exact-work-trace');
  require0(compact.includes('def pairedInputFramerRawTimeBound : NatPolynomial := .add (.quadratic 6 42) (.linear 27 0)'),
    'exact-raw-polynomial');
  require0(compact.includes('pairedInputFramerRawTimeBound.eval (BitString.size (BitString.pair left right)) = 6 * inputFramerWorkSteps (packedPairCount left right)'),
    'raw-polynomial-exactness');
  require0(compact.includes('(startConfig (compileWorkMachine pairedInputFramer) (BitString.pair left right)) = encodeWorkConfiguration (pairedInputFramerFinalConfiguration left right)'),
    'literal-compiled-canonical-start');
  require0(compact.includes('pairedInputFramer.isHalted (pairedInputFramerFinalConfiguration left right) = true'),
    'designated-accept-halt');
  require0(compact.includes('boundedDecide (compileWorkMachine pairedInputFramer)')
    && compact.includes('(BitString.pair left right) = .accept'),
  'bounded-framer-accept');
  require0(compact.includes('frameWithGarbage (Tape.ofInput input) (totalInputFramerOutsideLeft input) []'),
    'all-input-represented-endpoint');
  require0(compact.includes('workRunExact? pairedInputFramer (totalInputFramerWorkSteps input) (workStartConfiguration pairedInputFramer (rawInputWorkTape input)) = some (totalInputFramerFinalConfiguration input)'),
    'all-input-exact-work-trace');
  require0(compact.includes('def totalInputFramerRawTimeBound : NatPolynomial := .add (.quadratic 6 75) (.linear 39 0)'),
    'all-input-raw-polynomial');
  require0(compact.includes('6 * totalInputFramerWorkSteps input ≤ totalInputFramerRawTimeBound.eval (BitString.size input)'),
    'all-input-raw-polynomial-bound');
  require0(compact.includes('run_compileTotalInputFramer_rawTimeBound_blankEquivalent')
    && compact.includes('Configuration.BlankEquivalent')
    && compact.includes('(startConfig (compileWorkMachine pairedInputFramer) input)'),
  'ordinary-start-blank-equivalence');
  require0(compact.includes('boundedDecide_compileTotalInputFramer_accept')
    && compact.includes('boundedDecide_compileTotalInputFramer_ne_timeout'),
  'all-input-accepts-without-timeout');
  require0(compact.includes('workBoundedDecide pairedInputFramer 3 (rawInputWorkTape []) = .timeout')
    && compact.includes('workBoundedDecide pairedInputFramer 17 (rawInputWorkTape [false]) = .timeout')
    && compact.includes('workBoundedDecide pairedInputFramer 17 (rawInputWorkTape [true]) = .timeout'),
  'one-step-short-regressions');

  return failures;
}

test('all-input framer source is closed, literal, exact, and shortcut-free', async () => {
  const source = await text0(SOURCE_PATH);
  assert.deepEqual(validate0(source), []);
});

test('all-input framer axiom transcript covers all 70 explicit public heads', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE_PATH), text0(AUDIT_PATH)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 70);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 70);
});

test('root, package, and workflow enforce the all-input framer audit', async () => {
  const [root, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.PipelineInputFramer'), true);
  assert.match(packageText, /audits\/lean-concrete-pipeline-input-framer0\.test\.mjs/u);
  assert.match(workflow, /PNPConcretePipelineInputFramerAxiomAudit\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 70/u);
});

test('all-input framer audit rejects scope, cost, endpoint, and trust regressions', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('4 * packedCells * packedCells + 9 * packedCells + 7',
      '4 * packedCells * packedCells + 9 * packedCells + 8'),
    source.replace('.add (.quadratic 6 42) (.linear 27 0)',
      '.add (.quadratic 6 43) (.linear 27 0)'),
    source.replace('4 * packedCells * packedCells + 9 * packedCells + 5',
      '4 * packedCells * packedCells + 9 * packedCells + 6'),
    source.replace('.add (.quadratic 6 75) (.linear 39 0)',
      '.add (.quadratic 6 74) (.linear 39 0)'),
    source.replace('writeRule emptyInstallRightState WorkSymbol.blank acceptState',
      'writeRule emptyInstallRightState WorkSymbol.blank rejectState'),
    source.replace('frameWithGarbage (Tape.ofInput (BitString.pair left right))',
      'frameWithGarbage (Tape.ofInput left)'),
    `${source}\naxiom broadenedFramer : True\n`,
    `${source}\ntheorem hiddenPipelineRefinement : FunctionProgram.RawRefinement := by trivial\n`,
    source.replace('They do not combine the', 'They combine the'),
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('framer milestone remains local and the concrete publication gate remains closed', async () => {
  const [status, map] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
  ]);
  assert.equal(status.remainingBlockers.length, 7);
  assert.equal(status.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'), true);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.leanConcretePipelineInputFramerAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelineInputFramerAuditedDeclarationCount, 70);
  assert.equal(status.leanConcretePipelineAllInputFramingFormalized, true);
  assert.equal(status.leanConcretePipelineMalformedInputBehaviorFormalized, true);
  assert.equal(status.leanConcretePipelineAllInputCompilationFormalized, true);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, false);
  const framerNonClaim = status.nonClaims.find((entry) => entry.includes(
    'PipelineInputFramer is one literal finite machine for every raw bitstring'));
  assert.equal(typeof framerNonClaim, 'string');
  assert.match(framerNonClaim, /empty word, complete two-bit work cells, and an odd final raw bit/u);
  assert.match(framerNonClaim, /6 \* m \* m \+ 39 \* m \+ 75/u);
  assert.match(framerNonClaim, /All 70 public declarations have empty axiom closure/u);
  assert.match(framerNonClaim, /PipelineCompiler now transports that endpoint/u);
  assert.match(framerNonClaim, /recursive pipeline RawRefinement/u);
  const foundation = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-machine-cost-kernel',
  );
  for (const name of [
    `${PREFIX}pairedInputFramerFinal_represents`,
    `${PREFIX}pairedInputFramer_workRunExact`,
    `${PREFIX}pairedInputFramerRawTimeBound_exact`,
    `${PREFIX}run_compilePairedInputFramer_rawTimeBound`,
    `${PREFIX}boundedDecide_compileTotalInputFramer_accept`,
    `${PREFIX}boundedDecide_compileTotalInputFramer_ne_timeout`,
    `${PREFIX}run_compileTotalInputFramer_encoded_rawTimeBound`,
    `${PREFIX}run_compileTotalInputFramer_rawTimeBound_blankEquivalent`,
    `${PREFIX}totalInputFramerFinal_isHalted`,
    `${PREFIX}totalInputFramerFinal_represents`,
    `${PREFIX}totalInputFramerRawTimeBound_le`,
    `${PREFIX}totalInputFramer_workRunExact`,
  ]) assert.equal(foundation.requiredTheorems.includes(name), true, name);
  assert.match(foundation.scope, /four-stage pipeline handles every raw bitstring/u);
  assert.match(foundation.scope, /exactly 4 work steps on empty input/u);
  assert.match(foundation.scope, /6 \* m \* m \+ 39 \* m \+ 75/u);
  assert.match(foundation.scope, /PipelineCompiler uses the same terminal-bridge rule table/u);
  assert.match(foundation.scope,
    /R\(m\) = PipelineRaw\(p\)\(m\) \+ 6 \+ PipelineRaw\(q\)\(m \+ p\(m\) \+ 1\)/u);
  assert.match(foundation.scope, /31 public declarations have empty axiom closure/u);
  assert.match(foundation.nonClaim, /composes two already-raw proof-bearing targets/u);
  assert.match(foundation.nonClaim, /recursive raw-refinement constructors/u);
  assert.equal(map.gate.standardComplexityModelEligible, false);
  assert.deepEqual([
    map.gate.expectedConcreteTargetKernelTypeSha256,
    map.gate.expectedConcreteTargetKernelValueSha256,
    map.gate.expectedRootKernelTypeSha256,
    map.gate.expectedAxiomClosureSha256,
    map.gate.expectedSourceClosureSha256,
  ], [null, null, null, null, null]);
});
