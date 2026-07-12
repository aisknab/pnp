import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasPrivateLeanDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const SOURCE_PATH = 'lean/PNP/Concrete/PipelineTapeGeometry.lean';
const AUDIT_PATH = 'lean-audit/PNPConcretePipelineTapeGeometryAxiomAudit.lean';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'dataSymbol', 'PNP.Concrete.PipelineTape.dataSymbol'],
  ['def', 'leftMarker', 'PNP.Concrete.PipelineTape.leftMarker'],
  ['def', 'rightMarker', 'PNP.Concrete.PipelineTape.rightMarker'],
  ['theorem', 'dataSymbol_injective', 'PNP.Concrete.PipelineTape.dataSymbol_injective'],
  ['theorem', 'dataSymbol_ne_leftMarker', 'PNP.Concrete.PipelineTape.dataSymbol_ne_leftMarker'],
  ['theorem', 'dataSymbol_ne_rightMarker', 'PNP.Concrete.PipelineTape.dataSymbol_ne_rightMarker'],
  ['theorem', 'leftMarker_ne_rightMarker', 'PNP.Concrete.PipelineTape.leftMarker_ne_rightMarker'],
  ['def', 'frameWithGarbage', 'PNP.Concrete.PipelineTape.frameWithGarbage'],
  ['def', 'Represents', 'PNP.Concrete.PipelineTape.Represents'],
  ['def', 'frame', 'PNP.Concrete.PipelineTape.frame'],
  ['theorem', 'frameWithGarbage_represents',
    'PNP.Concrete.PipelineTape.frameWithGarbage_represents'],
  ['theorem', 'frame_represents', 'PNP.Concrete.PipelineTape.frame_represents'],
  ['theorem', 'represents_write', 'PNP.Concrete.PipelineTape.represents_write'],
  ['theorem', 'represents_moveLeft_of_cons',
    'PNP.Concrete.PipelineTape.represents_moveLeft_of_cons'],
  ['def', 'expandLeftBoundary', 'PNP.Concrete.PipelineTape.expandLeftBoundary'],
  ['theorem', 'represents_expandLeft_of_nil',
    'PNP.Concrete.PipelineTape.represents_expandLeft_of_nil'],
  ['theorem', 'represents_moveRight_of_cons',
    'PNP.Concrete.PipelineTape.represents_moveRight_of_cons'],
  ['def', 'expandRightBoundary', 'PNP.Concrete.PipelineTape.expandRightBoundary'],
  ['theorem', 'represents_expandRight_of_nil',
    'PNP.Concrete.PipelineTape.represents_expandRight_of_nil'],
  ['theorem', 'handoffTarget_withGarbage_represents',
    'PNP.Concrete.PipelineTape.handoffTarget_withGarbage_represents'],
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function printed0(audit) {
  return [...audit.matchAll(/^#print axioms (.+?)[ \t]*$/gmu)].map((match) => match[1]);
}

function compactLean0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
}

function headPairs0(source) {
  return explicitLeanDeclarationHeads0(source).map(({ kind, name }) => [kind, name]);
}

function withoutImports0(source) {
  return stripLeanCommentsAndStrings0(source).replace(/^\s*import\s+[^\n]+$/gmu, '');
}

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const body = withoutImports0(source);
  const compact = compactLean0(source);

  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.TapeHandoff',
    'PNP.Concrete.WorkMachine',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped) &&
    /^namespace PipelineTape$/mu.test(stripped) &&
    /end PipelineTape\s+end PNP\.Concrete\s*$/u.test(compact), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasPrivateLeanDeclaration0(source), 'private-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|funext|propext|String)\b/u.test(stripped),
    'forbidden-shortcut');
  require0(JSON.stringify(headPairs0(source)) ===
    JSON.stringify(EXPECTED_HEADS.map(([kind, name]) => [kind, name])),
  'declaration-surface');
  require0(!/\b(?:WorkRule|WorkConfiguration|WorkMachine|Machine|Rule|Configuration|NatPolynomial|RawRefinement|boundedDecide|compileWorkMachine|FunctionProgram|DecisionProgram)\b/u.test(body) &&
    !/\b(?:rules|timeBound)\s*:/u.test(body), 'no-machine-or-compiler');

  require0(compact.includes('def dataSymbol (symbol : TapeSymbol) : WorkSymbol := ⟨symbol, .blank⟩'),
    'data-on-first-track');
  require0(compact.includes('def leftMarker : WorkSymbol := ⟨.blank, .zero⟩'),
    'left-marker');
  require0(compact.includes('def rightMarker : WorkSymbol := ⟨.blank, .one⟩'),
    'right-marker');
  require0(compact.includes('raw.left.map dataSymbol ++ (leftMarker :: outsideLeft)') &&
    compact.includes('head := dataSymbol raw.head') &&
    compact.includes('raw.right.map dataSymbol ++ (rightMarker :: outsideRight)'),
  'exact-garbage-frame');
  require0(compact.includes('def Represents (raw : Tape) (work : WorkTape) : Prop := ∃ outsideLeft outsideRight, work = frameWithGarbage raw outsideLeft outsideRight'),
    'existential-garbage-relation');
  require0(compact.includes('def frame (raw : Tape) : WorkTape := frameWithGarbage raw [] []'),
    'canonical-frame');
  require0(compact.includes('Represents (raw.write symbol) (work.write (dataSymbol symbol))'),
    'write-preservation');
  require0(compact.includes('Represents raw.moveLeft work.moveLeft'),
    'interior-left-move');
  require0(compact.includes('Represents raw.moveRight work.moveRight'),
    'interior-right-move');
  require0(compact.includes('def expandLeftBoundary (work : WorkTape) : WorkTape := (((work.moveLeft).write (dataSymbol .blank)).moveLeft.write leftMarker).moveRight'),
    'left-boundary-expansion');
  require0(compact.includes('def expandRightBoundary (work : WorkTape) : WorkTape := (((work.moveRight).write (dataSymbol .blank)).moveRight.write rightMarker).moveLeft'),
    'right-boundary-expansion');
  require0(compact.includes('Represents raw.moveLeft (expandLeftBoundary work)') &&
    compact.includes('Represents raw.moveRight (expandRightBoundary work)'),
  'boundary-preservation');
  require0(compact.includes('Represents raw.handoffTarget (frameWithGarbage raw.handoffTarget outsideLeft outsideRight)'),
    'pure-handoff-target-witness');

  return failures;
}

test('pipeline tape geometry is closed, exact, garbage-tolerant, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all twenty geometry declarations exactly once', async () => {
  const [audit, root] = await Promise.all([
    text0(AUDIT_PATH),
    text0('lean/PNP.lean'),
  ]);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), EXPECTED_HEADS.map(([, , full]) => full));
  assert.equal(new Set(printed0(audit)).size, EXPECTED_HEADS.length);
  assert.ok(imports0(root).includes('PNP.Concrete.PipelineTapeGeometry'));
});

test('package verifier and workflow enforce the complete geometry audit', async () => {
  const [pkg, surface, verifier, workflow] = await Promise.all([
    text0('package.json').then(JSON.parse),
    text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditCommand = 'audits/lean-concrete-pipeline-tape-geometry0.test.mjs';
  assert.ok(pkg.scripts.test.includes(auditCommand));
  assert.ok(surface.includes(auditCommand));
  assert.ok(verifier.includes(`'${auditCommand}'`));
  assert.equal((workflow.match(/audits\/lean-concrete-pipeline-tape-geometry0\.test\.mjs/g) ?? []).length, 3);
  assert.match(workflow,
    /PNPConcretePipelineTapeGeometryAxiomAudit\.lean[\s\S]{0,900}grep -Fc 'does not depend on any axioms'\)" -eq 20/u);
});

test('hostile tag, marker, frame, garbage, movement, and compiler mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('⟨symbol, .blank⟩', '⟨symbol, .zero⟩'),
    source.replace('⟨.blank, .one⟩', '⟨.blank, .zero⟩'),
    source.replace('raw.left.map dataSymbol ++ (leftMarker :: outsideLeft)',
      'leftMarker :: raw.left.map dataSymbol ++ outsideLeft'),
    source.replace('raw.right.map dataSymbol ++ (rightMarker :: outsideRight)',
      'rightMarker :: raw.right.map dataSymbol ++ outsideRight'),
    source.replace('∃ outsideLeft outsideRight,\n    work = frameWithGarbage raw outsideLeft outsideRight',
      'work = frame raw'),
    source.replace('frameWithGarbage raw [] []', 'WorkTape.blank'),
    source.replace('(((work.moveLeft).write (dataSymbol .blank)).moveLeft.write leftMarker).moveRight',
      'work.moveLeft'),
    source.replace('(((work.moveRight).write (dataSymbol .blank)).moveRight.write rightMarker).moveLeft',
      'work.moveRight'),
    source.replace('frameWithGarbage raw.handoffTarget outsideLeft outsideRight',
      'frameWithGarbage raw outsideLeft outsideRight'),
    `${source}\nnamespace PNP.Concrete.PipelineTape\ndef handoffMachine : WorkMachine := { rules := [], startState := 0, acceptState := 1, rejectState := 2 }\nend PNP.Concrete.PipelineTape\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('the executable compiler blocker and publication gate remain fail-closed', async () => {
  const [status, map] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
  ]);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'));
  assert.equal(status.rootLeanTheoremPresent, false);
  assert.equal(status.nonClaims.some((entry) => entry.includes(
    'PipelineTape frames raw cells between distinct two-track markers')), true);
  const foundation = status.formalPublicationMilestones.find(
    (entry) => entry.id === 'concrete-machine-cost-kernel',
  );
  assert.equal(foundation.requiredTheorems.includes(
    'PNP.Concrete.PipelineTape.represents_expandLeft_of_nil'), true);
  assert.equal(foundation.requiredTheorems.includes(
    'PNP.Concrete.PipelineTape.represents_expandRight_of_nil'), true);
  assert.match(foundation.scope,
    /one-step framer-to-simulator launch/u);
  assert.match(foundation.scope,
    /supplied stuck nonhalting endpoint is timeout/u);
  assert.match(foundation.nonClaim,
    /internal two-track representation of Tape\.handoffTarget/u);
  assert.match(foundation.nonClaim,
    /does not prove target termination/u);
  assert.match(foundation.nonClaim,
    /no ordinary machineOutput equality theorem/u);
  assert.match(foundation.nonClaim,
    /no complete FunctionProgram\.RawRefinement or DecisionProgram\.RawRefinement/u);
  assert.equal(map.gate.standardComplexityModelEligible, false);
  assert.equal(map.gate.expectedSourceClosureSha256, null);
});
