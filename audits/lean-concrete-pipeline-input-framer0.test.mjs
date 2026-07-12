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
    'PNP.Concrete.WorkInput',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace PipelineInputFramer$/mu.test(stripped)
    && /end PipelineInputFramer\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|ac_rfl)\b/u.test(stripped)
    && !/Nat\.(?:add_mul|mul_assoc|mul_left_comm)\b/u.test(stripped),
    'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('The public exact trace is restricted to BitString.pair inputs.')
    && prose.includes('It does not frame arbitrary empty or odd raw inputs')
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

  return failures;
}

test('paired-input framer source is closed, literal, exact, and shortcut-free', async () => {
  const source = await text0(SOURCE_PATH);
  assert.deepEqual(validate0(source), []);
});

test('paired-input framer axiom transcript covers all 42 explicit public heads', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE_PATH), text0(AUDIT_PATH)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 42);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 42);
});

test('root, package, and workflow enforce the paired-input framer audit', async () => {
  const [root, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.PipelineInputFramer'), true);
  assert.match(packageText, /audits\/lean-concrete-pipeline-input-framer0\.test\.mjs/u);
  assert.match(workflow, /PNPConcretePipelineInputFramerAxiomAudit\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 42/u);
});

test('paired-input framer audit rejects scope, cost, endpoint, and trust regressions', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('4 * packedCells * packedCells + 9 * packedCells + 7',
      '4 * packedCells * packedCells + 9 * packedCells + 8'),
    source.replace('.add (.quadratic 6 42) (.linear 27 0)',
      '.add (.quadratic 6 43) (.linear 27 0)'),
    source.replace('frameWithGarbage (Tape.ofInput (BitString.pair left right))',
      'frameWithGarbage (Tape.ofInput left)'),
    `${source}\naxiom broadenedFramer : True\n`,
    `${source}\ntheorem arbitraryRawInputFramer (input : BitString) : True := True.intro\n`,
    source.replace('The public exact trace is restricted to `BitString.pair` inputs.',
      'The public exact trace applies to every raw input.'),
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
  const framerNonClaim = status.nonClaims.find((entry) => entry.includes(
    'PipelineInputFramer is one literal finite machine for canonical BitString.pair inputs'));
  assert.equal(typeof framerNonClaim, 'string');
  assert.match(framerNonClaim, /launches that endpoint into the lifted target/u);
  assert.match(framerNonClaim, /does not accept arbitrary empty, odd, malformed, or unpaired raw words/u);
  assert.match(framerNonClaim, /does not .*prove target termination/u);
  const foundation = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-machine-cost-kernel',
  );
  for (const name of [
    `${PREFIX}pairedInputFramerFinal_represents`,
    `${PREFIX}pairedInputFramer_workRunExact`,
    `${PREFIX}pairedInputFramerRawTimeBound_exact`,
    `${PREFIX}run_compilePairedInputFramer_rawTimeBound`,
  ]) assert.equal(foundation.requiredTheorems.includes(name), true, name);
  assert.match(foundation.scope, /canonical paired input/u);
  assert.match(foundation.scope, /exact quadratic raw-input-length polynomial/u);
  assert.match(foundation.scope, /one-step framer-to-simulator launch/u);
  assert.match(foundation.nonClaim, /no theorem proves target termination/u);
  assert.match(foundation.nonClaim, /no polynomial in external encoded input length/u);
  assert.equal(map.gate.standardComplexityModelEligible, false);
  assert.deepEqual([
    map.gate.expectedConcreteTargetKernelTypeSha256,
    map.gate.expectedConcreteTargetKernelValueSha256,
    map.gate.expectedRootKernelTypeSha256,
    map.gate.expectedAxiomClosureSha256,
    map.gate.expectedSourceClosureSha256,
  ], [null, null, null, null, null]);
});
