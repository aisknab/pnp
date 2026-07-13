import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH = 'lean/PNP/Concrete/TerminalOutputPacker.lean';
const AUDIT_PATH = 'lean-audit/PNPConcreteTerminalOutputPackerAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.TerminalOutputPacker.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'allWorkSymbols'],
  ['def', 'outputSymbols'],
  ['def', 'sourceBlankSymbols'],
  ['def', 'startState'],
  ['def', 'seekPackedState'],
  ['def', 'rememberFirstZeroState'],
  ['def', 'rememberFirstOneState'],
  ['def', 'rememberPackedZeroState'],
  ['def', 'rememberPackedOneState'],
  ['def', 'firstCarryZeroZeroState'],
  ['def', 'firstCarryZeroOneState'],
  ['def', 'firstCarryOneZeroState'],
  ['def', 'firstCarryOneOneState'],
  ['def', 'firstWriteZeroState'],
  ['def', 'firstWriteOneState'],
  ['def', 'firstWriteZeroZeroState'],
  ['def', 'firstWriteZeroOneState'],
  ['def', 'firstWriteOneZeroState'],
  ['def', 'firstWriteOneOneState'],
  ['def', 'packedCarryZeroZeroState'],
  ['def', 'packedCarryZeroOneState'],
  ['def', 'packedCarryOneZeroState'],
  ['def', 'packedCarryOneOneState'],
  ['def', 'seekOuterZeroState'],
  ['def', 'seekOuterOneState'],
  ['def', 'seekOuterZeroZeroState'],
  ['def', 'seekOuterZeroOneState'],
  ['def', 'seekOuterOneZeroState'],
  ['def', 'seekOuterOneOneState'],
  ['def', 'installOuterState'],
  ['def', 'returnOutputState'],
  ['def', 'returnSourceState'],
  ['def', 'acceptState'],
  ['def', 'rejectState'],
  ['def', 'firstRememberState'],
  ['def', 'packedRememberState'],
  ['def', 'firstCarryState'],
  ['def', 'firstWriteSingleState'],
  ['def', 'firstWritePairState'],
  ['def', 'packedCarryState'],
  ['def', 'seekOuterSingleState'],
  ['def', 'seekOuterPairState'],
  ['def', 'keepRule'],
  ['def', 'writeRule'],
  ['def', 'writeAllRules'],
  ['def', 'carryRules'],
  ['def', 'seekOuterRules'],
  ['def', 'terminalOutputPackerRules'],
  ['def', 'terminalOutputPacker'],
  ['def', 'bitSymbol'],
  ['def', 'pairSymbol'],
  ['def', 'bitSymbols'],
  ['def', 'packedSymbols'],
  ['def', 'packedCellCount'],
  ['def', 'packedLoopSteps'],
  ['def', 'terminalOutputPackerWorkSteps'],
  ['def', 'terminalOutputPackerRawTimeBound'],
  ['def', 'terminalOutputPackerOutside'],
  ['def', 'terminalOutputPackerInputTape'],
  ['def', 'terminalOutputPackerFinalTape'],
  ['def', 'terminalOutputPackerFinalConfiguration'],
  ['theorem', 'terminalOutputPacker_workRunExact'],
  ['theorem', 'terminalOutputPackerFinal_isHalted'],
  ['theorem', 'terminalOutputPacker_output_eq'],
  ['theorem', 'run_compileTerminalOutputPacker_exact'],
  ['theorem', 'terminalOutputPacker_runtime_le'],
  ['theorem', 'run_compileTerminalOutputPacker'],
  ['theorem', 'machineOutput_compileTerminalOutputPacker_eq'],
  ['theorem', 'terminalOutputPacker_one_step_short_timeout'],
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
    'PNP.Concrete.PipelineOutputHandoff',
    'PNP.Concrete.Complexity',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace TerminalOutputPacker$/mu.test(stripped)
    && /end TerminalOutputPacker\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|ac_rfl|aesop|simp_all|Classical|funext|propext)\b/u
    .test(stripped), 'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes('only the terminal packing stage')
    && prose.includes('does not prove termination of an arbitrary simulated target')
    && prose.includes('compose the complete pipeline')
    && prose.includes('establish a RawRefinement')
    && prose.includes('external encoded-input-size polynomial')
    && prose.includes('prove CNF-SAT in P or NP-completeness')
    && prose.includes('prove P = NP.')
    && prose.includes('not from external startConfig'), 'explicit-nonclaims');
  require0(!/\b(?:cnfSATInP|cnfSATNPComplete|p_eq_np)\b/u.test(stripped),
    'no-class-or-root-claim');

  require0(compact.includes(
    'def terminalOutputPacker : WorkMachine := { rules := terminalOutputPackerRules startState := startState acceptState := acceptState rejectState := rejectState }'),
  'literal-finite-machine');
  require0(compact.includes(
    '| false, false => WorkSymbol.zeroZero | false, true => WorkSymbol.zeroOne | true, false => WorkSymbol.oneZero | true, true => WorkSymbol.oneOne'),
  'four-pair-symbols');
  require0(compact.includes(
    '| [] => [] | [bit] => [bitSymbol bit] | first :: second :: rest => pairSymbol first second :: packedSymbols rest'),
  'empty-single-pair-packing');
  require0(compact.includes(
    'def terminalOutputPackerRawTimeBound : NatPolynomial := .add (.quadratic 18 6) (.linear 36 0)'),
  'exact-raw-polynomial');
  require0(compact.includes(
    'head := bitSymbol bit right := leftMarker :: terminalOutputPackerOutside [bit] outsideRight')
    && compact.includes(
      'head := pairSymbol first second right := packedSymbols rest ++ leftMarker :: terminalOutputPackerOutside'),
  'blank-delimited-final-layout');
  require0(compact.includes(
    'theorem terminalOutputPacker_workRunExact (bits : BitString) (outsideLeft outsideRight : List WorkSymbol)')
    && compact.includes(
      'theorem terminalOutputPackerFinal_isHalted (bits : BitString) (outsideLeft outsideRight : List WorkSymbol)')
    && compact.includes(
      'theorem terminalOutputPacker_output_eq (bits : BitString) (outsideLeft outsideRight : List WorkSymbol)')
    && compact.includes(
      'Tape.outputBits (encodeWorkTape (terminalOutputPackerFinalTape bits outsideLeft outsideRight)) = bits'),
  'universal-garbage-exact-halt-output');
  require0(compact.includes(
    '6 * terminalOutputPackerWorkSteps bits ≤ terminalOutputPackerRawTimeBound.eval bits.length')
    && compact.includes(
      '6 * (length * (3 * length + 5) + length + 1) = (18 * length * length + 6) + (36 * length + 0)'),
  'compiled-runtime-bound');
  require0(compact.includes(
    'theorem machineOutput_compileTerminalOutputPacker_eq (bits : BitString)')
    && compact.includes(
      'terminalOutputPackerRawTimeBound.eval bits.length')
    && compact.includes(
      'theorem terminalOutputPacker_one_step_short_timeout (bits : BitString)')
    && compact.includes(
      'terminalOutputPackerWorkSteps bits - 1')
    && compact.includes('= .timeout := by'),
  'compiled-output-and-one-short-timeout');

  return failures;
}

test('terminal output packer is finite, universal, exact, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
});

test('terminal output packer axiom transcript covers all 69 public heads', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE_PATH), text0(AUDIT_PATH)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 69);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 69);
});

test('root, package, and workflow enforce the terminal output packer audit', async () => {
  const [root, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.TerminalOutputPacker'), true);
  assert.match(packageText, /audits\/lean-concrete-terminal-output-packer0\.test\.mjs/u);
  assert.match(workflow, /PNPConcreteTerminalOutputPackerAxiomAudit\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 69/u);
});

test('packer audit rejects packing, delimiter, bound, timeout, assumption, and claim mutations', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('| false, true => WorkSymbol.zeroOne',
      '| false, true => WorkSymbol.zeroZero'),
    source.replace('right := packedSymbols rest ++ leftMarker ::',
      'right := packedSymbols rest ++ rightMarker ::'),
    source.replace('.quadratic 18 6', '.quadratic 17 6'),
    source.replaceAll('terminalOutputPackerWorkSteps bits - 1',
      'terminalOutputPackerWorkSteps bits'),
    `${source}\naxiom hiddenPackingOracle : True\n`,
    source.replace('not from external `startConfig`', 'from external `startConfig`'),
    `${source}\ntheorem p_eq_np : True := True.intro\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('terminal packing and canonical-pair compiler are earned while general refinement stays fail-closed', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcretePipelineInternalOutputHandoffComposed, true);
  assert.equal(status.leanConcretePipelineTerminalOutputPackingFormalized, true);
  assert.equal(status.leanConcretePipelineTerminalOutputPackerAxiomAuditPassed, true);
  assert.equal(status.leanConcretePipelineTerminalOutputPackerAuditedDeclarationCount, 69);
  assert.equal(status.leanConcretePipelineTerminalOutputPackerConnectedToBridgeEndpointFormalized, true);
  assert.equal(status.leanConcretePipelinePriorTraceTransportToTerminalBridgeFormalized, true);
  assert.equal(status.leanConcretePipelineRawRefinementFormalized, false);
  assert.equal(status.leanConcretePipelineCanonicalPairCompilationFormalized, true);
  assert.equal(status.leanConcretePipelineAllInputCompilationFormalized, true);
  assert.equal(status.leanConcretePipelineExternalInputSizePolynomialFormalized, true);
  assert.equal(status.leanConcretePipelineMalformedInputBehaviorFormalized, true);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.concretePublicationGate.passed, false);
});
