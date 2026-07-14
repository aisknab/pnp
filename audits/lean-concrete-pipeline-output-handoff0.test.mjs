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
const SOURCE_PATH = 'lean/PNP/Concrete/PipelineOutputHandoff.lean';
const AUDIT_PATH = 'lean-audit/PNPConcretePipelineOutputHandoffAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.PipelineOutputHandoff.';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'allWorkSymbols'],
  ['def', 'startState'],
  ['def', 'installLeftBitState'],
  ['def', 'installLeftEmptyState'],
  ['def', 'scanRightState'],
  ['def', 'returnLeftState'],
  ['def', 'emptyMoveRightState'],
  ['def', 'emptyInstallRightState'],
  ['def', 'acceptState'],
  ['def', 'rejectState'],
  ['def', 'keepRule'],
  ['def', 'writeRule'],
  ['def', 'installLeftRules'],
  ['def', 'installRightRules'],
  ['def', 'handoffRules'],
  ['def', 'framedOutputHandoff'],
  ['def', 'framedOutputHandoffWorkSteps'],
  ['def', 'framedOutputHandoffRawTimeBound'],
  ['def', 'framedOutputHandoffFinalConfiguration'],
  ['theorem', 'framedOutputHandoff_workRunExact_of_represents'],
  ['theorem', 'framedOutputHandoffFinal_isHalted'],
  ['theorem', 'framedOutputHandoffRawTimeBound_exact'],
  ['theorem', 'run_compileFramedOutputHandoff_of_represents'],
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
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace PipelineOutputHandoff$/mu.test(stripped)
    && /end PipelineOutputHandoff\s+end PNP\.Concrete\s*$/u.test(compact),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|omega|ac_rfl|Classical|funext|propext)\b/u
    .test(stripped) && !/Nat\.(?:add_mul|mul_assoc|mul_left_comm)\b/u.test(stripped),
  'forbidden-shortcut');
  require0(JSON.stringify(publicHeadPairs0(source)) === JSON.stringify(EXPECTED_HEADS),
    'declaration-surface');

  require0(prose.includes(
    'The compiled endpoint is still the ordinary two-cell encoding of a framed work tape.')
    && prose.includes('does not claim that raw machineOutput can directly decode')
    && prose.includes('compose the handoff with another rule table')
    && prose.includes('reset a later machine\'s state')
    && prose.includes('prove source-machine termination')
    && prose.includes('construct a pipeline refinement or complexity-class equality.'),
  'explicit-nonclaims');
  require0(!/\b(?:machineOutput|boundedDecide|startConfig|RawRefinement|FunctionProgram|DecisionProgram|CNFSAT|PEqualsNP)\b/u
    .test(stripped), 'no-external-output-composition-or-class-claim');

  require0(compact.includes(
    'def framedOutputHandoff : WorkMachine := { rules := handoffRules startState := startState acceptState := acceptState rejectState := rejectState }'),
  'literal-finite-work-machine');
  require0(compact.includes(
    'def framedOutputHandoffWorkSteps (raw : Tape) : Nat := 2 * BitString.size raw.outputBits + 4'),
  'exact-work-cost');
  require0(compact.includes(
    'def framedOutputHandoffRawTimeBound : NatPolynomial := .linear 12 24'),
  'exact-compiled-cost');
  require0(compact.includes(
    'def framedOutputHandoffFinalConfiguration (tape : WorkTape) : WorkConfiguration := { state := framedOutputHandoff.acceptState, tape := tape }'),
  'designated-accept-endpoint');
  require0(compact.includes('Represents raw.handoffTarget finalTape ∧ workRunExact? framedOutputHandoff')
    && compact.includes('(framedOutputHandoffWorkSteps raw) (workStartConfiguration framedOutputHandoff work) = some (framedOutputHandoffFinalConfiguration finalTape)'),
  'exact-work-trace');
  require0(compact.includes(
    'framedOutputHandoff.isHalted (framedOutputHandoffFinalConfiguration tape) = true'),
  'designated-accept-halt');
  require0(compact.includes(
    'framedOutputHandoffRawTimeBound.eval (BitString.size raw.outputBits) = 6 * framedOutputHandoffWorkSteps raw'),
  'compiled-polynomial-exactness');
  require0(compact.includes('run (compileWorkMachine framedOutputHandoff)')
    && compact.includes('(framedOutputHandoffRawTimeBound.eval (BitString.size raw.outputBits))')
    && compact.includes('(encodeWorkConfiguration (workStartConfiguration framedOutputHandoff work)) = encodeWorkConfiguration (framedOutputHandoffFinalConfiguration finalTape)'),
  'compiled-internal-trace');

  return failures;
}

test('internal output handoff source is closed, literal, exact, and shortcut-free', async () => {
  const source = await text0(SOURCE_PATH);
  assert.deepEqual(validate0(source), []);
});

test('internal output handoff axiom transcript covers all 23 explicit public heads', async () => {
  const [source, audit] = await Promise.all([text0(SOURCE_PATH), text0(AUDIT_PATH)]);
  const expectedNames = EXPECTED_HEADS.map(([, name]) => `${PREFIX}${name}`);
  assert.equal(EXPECTED_HEADS.length, 23);
  assert.deepEqual(publicHeadPairs0(source), EXPECTED_HEADS);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), expectedNames);
  assert.equal(new Set(printed0(audit)).size, 23);
});

test('root, package, and workflow enforce the internal output handoff audit', async () => {
  const [root, packageText, workflow] = await Promise.all([
    text0('lean/PNP.lean'), text0('package.json'), text0('.github/workflows/lean-bridge.yml'),
  ]);
  assert.equal(imports0(root).includes('PNP.Concrete.PipelineOutputHandoff'), true);
  assert.match(packageText, /audits\/lean-concrete-pipeline-output-handoff0\.test\.mjs/u);
  assert.match(workflow, /PNPConcretePipelineOutputHandoffAxiomAudit\.lean/u);
  assert.match(workflow, /grep -Fc 'does not depend on any axioms'\)" -eq 23/u);
});

test('internal output handoff audit rejects scope, cost, endpoint, and trust regressions', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('2 * BitString.size raw.outputBits + 4',
      '2 * BitString.size raw.outputBits + 5'),
    source.replace('.linear 12 24', '.linear 12 25'),
    source.replaceAll('raw.handoffTarget', 'raw'),
    source.replace('encodeWorkConfiguration\n            (workStartConfiguration',
      'startConfig (compileWorkMachine framedOutputHandoff)\n            (workStartConfiguration'),
    `${source}\naxiom broadenedHandoff : True\n`,
    `${source}\ntheorem terminalMachineOutput : True := True.intro\n`,
    source.replace(
      'The compiled endpoint is still the ordinary two-cell encoding of a framed\nwork tape.',
      'The compiled endpoint is terminal raw output.'),
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('internal handoff milestone remains local and the publication gate remains closed', async () => {
  const [status, map] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
  ]);
  assert.equal(status.remainingBlockers.length, 6);
  assert.equal(status.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'), false);
  assert.equal(status.projectSpecificAxiomInventory.length, 4);
  assert.equal(status.rootLeanTheoremPresent, false);
  const handoffNonClaim = status.nonClaims.find((entry) => entry.includes(
    'PipelineOutputHandoff is one literal finite machine for an already represented internal tape'));
  assert.equal(typeof handoffNonClaim, 'string');
  assert.match(handoffNonClaim, /exactly 2 \* n \+ 4 work steps/u);
  assert.match(handoffNonClaim, /12 \* n \+ 24 compiled steps/u);
  assert.match(handoffNonClaim, /preserves the earlier ordinary-input trace/u);
  assert.match(handoffNonClaim, /verdict-indexed terminal-packer copies/u);
  assert.match(handoffNonClaim, /every supplied exact target execution/u);
  const foundation = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-machine-cost-kernel',
  );
  for (const name of [
    `${PREFIX}framedOutputHandoff_workRunExact_of_represents`,
    `${PREFIX}framedOutputHandoffFinal_isHalted`,
    `${PREFIX}framedOutputHandoffRawTimeBound_exact`,
    `${PREFIX}run_compileFramedOutputHandoff_of_represents`,
  ]) assert.equal(foundation.requiredTheorems.includes(name), true, name);
  assert.match(foundation.scope, /preserves the second verdict and output/u);
  assert.match(foundation.scope, /PipelineRefinement recursively applies that compiler/u);
  assert.match(foundation.nonClaim, /closes the concrete complexity machine-link blocker only/u);
  assert.equal(map.gate.standardComplexityModelEligible, true);
  assert.deepEqual([
    map.gate.expectedConcreteTargetKernelTypeSha256,
    map.gate.expectedConcreteTargetKernelValueSha256,
    map.gate.expectedRootKernelTypeSha256,
    map.gate.expectedAxiomClosureSha256,
    map.gate.expectedSourceClosureSha256,
  ], [null, null, null, null, null]);
});
