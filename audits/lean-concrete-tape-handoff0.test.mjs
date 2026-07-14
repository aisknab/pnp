import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
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
const SOURCE_PATH = 'lean/PNP/Concrete/TapeHandoff.lean';
const AUDIT_PATH = 'lean-audit/PNPConcreteTapeHandoffAxiomAudit.lean';

const EXPECTED_HEADS = Object.freeze([
  ['def', 'decodeOutputCells', 'PNP.Concrete.Tape.decodeOutputCells'],
  ['theorem', 'decodeOutputCells_map_ofBool', 'PNP.Concrete.Tape.decodeOutputCells_map_ofBool'],
  ['theorem', 'decodeOutputCells_append_blank', 'PNP.Concrete.Tape.decodeOutputCells_append_blank'],
  ['def', 'outputBits', 'PNP.Concrete.Tape.outputBits'],
  ['theorem', 'outputBits_ofInput', 'PNP.Concrete.Tape.outputBits_ofInput'],
  ['theorem', 'outputBits_right_append_blank', 'PNP.Concrete.Tape.outputBits_right_append_blank'],
  ['theorem', 'outputBits_blank_head', 'PNP.Concrete.Tape.outputBits_blank_head'],
  ['theorem', 'outputBits_set_left', 'PNP.Concrete.Tape.outputBits_set_left'],
  ['theorem', 'outputBits_explicit_blank_matches_implicit',
    'PNP.Concrete.Tape.outputBits_explicit_blank_matches_implicit'],
  ['theorem', 'outputBits_moveRight_moveLeft',
    'PNP.Concrete.Tape.outputBits_moveRight_moveLeft'],
  ['theorem', 'outputBits_moveLeft_moveRight',
    'PNP.Concrete.Tape.outputBits_moveLeft_moveRight'],
  ['def', 'handoffTarget', 'PNP.Concrete.Tape.handoffTarget'],
  ['theorem', 'outputBits_handoffTarget', 'PNP.Concrete.Tape.outputBits_handoffTarget'],
  ['theorem', 'handoffTarget_idempotent', 'PNP.Concrete.Tape.handoffTarget_idempotent'],
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

async function filesBelow0(directory) {
  const entries = await readdir(directory, { withFileTypes: true });
  const nested = await Promise.all(entries.map((entry) => {
    const child = path.join(directory, entry.name);
    return entry.isDirectory() ? filesBelow0(child) : [child];
  }));
  return nested.flat();
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

function validate0(source) {
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compactLean0(source);

  require0(JSON.stringify(imports0(source)) ===
    JSON.stringify(['PNP.Concrete.Machine']), 'closed-import');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped) &&
    /^namespace Tape$/mu.test(stripped) &&
    /end Tape\s+end PNP\.Concrete\s*$/u.test(compact), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption-declaration');
  require0(!hasPrivateLeanDeclaration0(source), 'private-declaration');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited-declaration-form');
  require0(!/\b(?:sorry|admit|unsafe|native_decide|Classical|funext|propext|String)\b/u.test(stripped),
    'forbidden-shortcut');
  require0(JSON.stringify(headPairs0(source)) ===
    JSON.stringify(EXPECTED_HEADS.map(([kind, name]) => [kind, name])),
  'declaration-surface');
  require0(!/\b(?:rules|timeBound)\s*:/u.test(stripped) &&
    !/\b(?:RawRefinement|boundedDecide|FunctionProgram|DecisionProgram)\b/u.test(stripped),
  'no-executable-handoff');
  require0(!stripped.includes('TapeSymbol.toBool'), 'blank-not-totalized-to-false');

  require0(compact.includes('def decodeOutputCells : List TapeSymbol → BitString | [] => [] | .blank :: _ => [] | .zero :: rest => false :: decodeOutputCells rest | .one :: rest => true :: decodeOutputCells rest'),
    'first-blank-decoder');
  require0(compact.includes('decodeOutputCells (bits.map TapeSymbol.ofBool ++ .blank :: suffix) = bits'),
    'first-blank-suffix-ignored');
  require0(compact.includes('def outputBits (tape : Tape) : BitString := decodeOutputCells (tape.head :: tape.right)'),
    'head-then-right-output');
  require0(compact.includes('outputBits { left := left, head := .blank, right := right } = [] := rfl'),
    'blank-head-empty');
  require0(compact.includes('outputBits { tape with left := left } = outputBits tape'),
    'left-region-ignored');
  require0(compact.includes('theorem outputBits_moveRight_moveLeft (tape : Tape) : outputBits (tape.moveRight.moveLeft) = outputBits tape'),
    'right-left-invariance');
  require0(compact.includes('theorem outputBits_moveLeft_moveRight (tape : Tape) : outputBits (tape.moveLeft.moveRight) = outputBits tape'),
    'left-right-invariance');
  require0(compact.includes('def handoffTarget (tape : Tape) : Tape := ofInput (outputBits tape)'),
    'exact-pure-handoff-target');
  require0(compact.includes('outputBits (handoffTarget tape) = outputBits tape'),
    'handoff-output-preservation');
  require0(compact.includes('handoffTarget (handoffTarget tape) = handoffTarget tape'),
    'handoff-idempotence');

  return failures;
}

test('blank-delimited output and pure handoff target are closed and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE_PATH)), []);
});

test('axiom transcript covers all fourteen output/handoff declarations exactly once', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE_PATH),
    text0(AUDIT_PATH),
    text0('lean/PNP.lean'),
  ]);
  assert.deepEqual(imports0(audit), ['PNP']);
  assert.deepEqual(printed0(audit), EXPECTED_HEADS.map(([, , full]) => full));
  assert.equal(new Set(printed0(audit)).size, EXPECTED_HEADS.length);
  assert.ok(imports0(root).includes('PNP.Concrete.TapeHandoff'));
});

test('outputBits has one authoritative definition and machineOutput consumes it', async () => {
  const files = (await filesBelow0(path.join(ROOT, 'lean')))
    .filter((file) => file.endsWith('.lean'));
  const definitions = [];
  for (const file of files) {
    const source = await readFile(file, 'utf8');
    const matches = [...stripLeanCommentsAndStrings0(source)
      .matchAll(/^\s*def\s+outputBits\b/gmu)];
    for (const _ of matches) definitions.push(path.relative(ROOT, file));
  }
  assert.deepEqual(definitions, [SOURCE_PATH]);
  const complexity = compactLean0(await text0('lean/PNP/Concrete/Complexity.lean'));
  assert.ok(complexity.includes('def machineOutput (machine : Machine) (steps : Nat) (input : BitString) : BitString := (run machine steps (startConfig machine input)).tape.outputBits'));
});

test('package verifier and workflow enforce the complete output/handoff audit', async () => {
  const [pkg, surface, verifier, workflow] = await Promise.all([
    text0('package.json').then(JSON.parse),
    text0('pcc-formal-public-surface0.mjs'),
    text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'),
  ]);
  const auditCommand = 'audits/lean-concrete-tape-handoff0.test.mjs';
  assert.ok(pkg.scripts.test.includes(auditCommand));
  assert.ok(surface.includes(auditCommand));
  assert.ok(verifier.includes(`'${auditCommand}'`));
  assert.equal((workflow.match(/audits\/lean-concrete-tape-handoff0\.test\.mjs/g) ?? []).length, 3);
  assert.match(workflow,
    /PNPConcreteTapeHandoffAxiomAudit\.lean[\s\S]{0,900}grep -Fc 'does not depend on any axioms'\)" -eq 14/u);
});

test('hostile blank, bit-order, geometry, target, and compiler mutations fail closed', async () => {
  const source = await text0(SOURCE_PATH);
  const mutations = [
    source.replace('decodeOutputCells (tape.head :: tape.right)',
      'match tape.head with\n  | .blank => []\n  | .zero => false :: tape.right.map TapeSymbol.toBool\n  | .one => true :: tape.right.map TapeSymbol.toBool'),
    source.replace('| .blank :: _ => []',
      '| .blank :: rest => false :: decodeOutputCells rest'),
    source.replace('| .blank :: _ => []',
      '| .blank :: rest => decodeOutputCells rest'),
    source.replace('| .zero :: rest => false :: decodeOutputCells rest',
      '| .zero :: rest => true :: decodeOutputCells rest'),
    source.replace('decodeOutputCells (tape.head :: tape.right)',
      'decodeOutputCells tape.right'),
    source.replace('decodeOutputCells (tape.head :: tape.right)',
      'decodeOutputCells (tape.left ++ tape.head :: tape.right)'),
    source.replace('ofInput (outputBits tape)', 'tape'),
    `${source}\nnamespace PNP.Concrete.Tape\ndef handoffMachine : Machine := { rules := [], startState := 0, acceptState := 1, rejectState := 2 }\nend PNP.Concrete.Tape\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} must change the source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} must be rejected`);
  }
});

test('the general compiler blocker and publication gate remain fail-closed', async () => {
  const [status, map] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
    text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
  ]);
  assert.equal(status.remainingBlockers.includes('Formal.ConcreteComplexityMachineLink'), false);
  assert.equal(map.gate.standardComplexityModelEligible, true);
  assert.equal(map.gate.expectedSourceClosureSha256, null);
});
