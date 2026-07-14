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
const SOURCE = 'lean/PNP/Concrete/CookLevinLayout.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinLayoutAxiomAudit.lean';
const PREFIX = 'PNP.Concrete.CookLevin.';

async function text0(relative) {
  return readFile(path.join(ROOT, relative), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^import\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)].map((match) => match[1]);
}

function validate0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const failures = [];
  const require0 = (condition, label) => { if (!condition) failures.push(label); };
  require0(JSON.stringify(imports0(source)) === JSON.stringify([
    'PNP.Concrete.CNF',
    'PNP.Concrete.WorkMachine',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped) &&
    /^namespace CookLevin$/mu.test(stripped) && /end PNP\.Concrete\s*$/u.test(stripped),
  'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|funext|propext|referenceMinimum)\b/u.test(stripped),
    'shortcut');
  require0((stripped.match(/rw \[hLarge, run_add\]/gmu) ?? []).length === 2 &&
    /theorem run_pad_of_stuck[\s\S]*run_eq_self_of_step\?_eq_none/u.test(stripped),
  'fuel-padding');
  require0(/def encodedInputPolynomial[\s\S]*InputMode[\s\S]*\.inputOnly => \.variable[\s\S]*\.paired/u.test(stripped),
    'input-polynomial');
  require0(/def tapeWidth \(dimensions : Dimensions\)[\s\S]*encodedInputLength mode \+ 2 \* dimensions\.timeBound \+ 1/u.test(stripped),
    'tape-window');
  require0(/def symbolBlock[\s\S]*def headBlock[\s\S]*def stateBlock[\s\S]*def certificateBitBlock[\s\S]*def certificateLengthBlock/u.test(stripped),
    'ordered-blocks');
  require0(/def headBlock[\s\S]*offset := layout\.symbolBlock\.endOffset/u.test(stripped) &&
    /def stateBlock[\s\S]*offset := layout\.headBlock\.endOffset/u.test(stripped) &&
    /def certificateBitBlock[\s\S]*offset := layout\.stateBlock\.endOffset/u.test(stripped),
  'block-offsets');
  require0((stripped.match(/_lt_variableCount/gmu) ?? []).length >= 5,
    'range-proofs');
  require0(/def exactlyOneClauses[\s\S]*atLeastOneClause variables :: atMostOneClauses variables/u.test(stripped),
    'exactly-one-combinator');
  require0(!/RawRefinement|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np/u.test(stripped),
    'boundary-overclaim');
  return failures;
}

test('Cook–Levin layout is finite, collision-free, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers every explicit declaration', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.ok(printed.every((name) => name.startsWith(PREFIX)));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinLayout'));
});

test('padding, namespace collision, and polynomial truncation mutations fail', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('rw [hLarge, run_add]', 'rw [hLarge]'),
    source.replace('offset := layout.symbolBlock.endOffset', 'offset := 0'),
    source.replace('2 * dimensions.timeBound + 1', 'dimensions.timeBound + 1'),
    `${source}\ntheorem cnfSATInP := True\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('publication boundary remains fail-closed', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
