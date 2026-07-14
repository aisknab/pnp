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
const SOURCE = 'lean/PNP/Concrete/CookLevinTableau.lean';
const AUDIT = 'lean-audit/PNPConcreteCookLevinTableauAxiomAudit.lean';
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
    'PNP.Concrete.CookLevinLayout',
  ]), 'closed-imports');
  require0(/^namespace PNP\.Concrete$/mu.test(stripped)
    && /^namespace CookLevin$/mu.test(stripped)
    && /end PNP\.Concrete\s*$/u.test(stripped), 'namespace');
  require0(!hasLeanAssumptionDeclaration0(source), 'assumption');
  require0(!hasPrivateLeanDeclaration0(source), 'private');
  require0(!hasUnauditedLeanDeclarationForm0(source), 'unaudited');
  require0(!/\b(?:sorry|admit|axiom|unsafe|native_decide|Classical|funext|propext|referenceMinimum)\b/u.test(stripped),
    'shortcut');
  require0(/def advance[\s\S]*match step\? machine config with[\s\S]*\| none => config[\s\S]*\| some next => next/u.test(stripped),
    'stuck-repetition');
  require0(/def traceTail[\s\S]*\| fuel \+ 1, config =>[\s\S]*next :: traceTail machine fuel next/u.test(stripped),
    'literal-trace');
  require0(/def ValidTableau[\s\S]*rest\.length = fuel[\s\S]*FollowsFrom machine initial rest/u.test(stripped),
    'exact-validity');
  require0(/theorem validTableau_iff_eq_trace[\s\S]*ValidTableau machine initial fuel tableau ↔[\s\S]*tableau = trace machine fuel initial/u.test(stripped),
    'sound-complete');
  require0(/def rawInput[\s\S]*BitString\.pair fixed\.input fixed\.certificate/u.test(stripped),
    'canonical-pair');
  require0(/theorem tableauVerdict_of_valid[\s\S]*boundedDecide fixed\.machine fixed\.fuel fixed\.rawInput/u.test(stripped),
    'exact-verdict');
  require0(/theorem exists_accepting_iff_boundedDecide_accept/u.test(stripped),
    'fixed-acceptance');
  require0(!/CNFFormula|PolynomialReduction|NPComplete|cnfSATInP|p_eq_np/u.test(stripped),
    'boundary-overclaim');
  return failures;
}

test('fixed Cook–Levin tableau is exact, canonical, and shortcut-free', async () => {
  assert.deepEqual(validate0(await text0(SOURCE)), []);
});

test('kernel audit covers every explicit tableau declaration', async () => {
  const [source, audit, root] = await Promise.all([
    text0(SOURCE), text0(AUDIT), text0('lean/PNP.lean'),
  ]);
  const declarations = explicitLeanDeclarationHeads0(source);
  const printed = printed0(audit);
  assert.equal(imports0(audit).join(','), 'PNP');
  assert.equal(printed.length, 30);
  assert.equal(printed.length, declarations.length);
  assert.equal(new Set(printed).size, printed.length);
  assert.ok(printed.every((name) => name.startsWith(PREFIX)));
  assert.ok(imports0(root).includes('PNP.Concrete.CookLevinTableau'));
});

test('stuck, length, pairing, and overclaim mutations fail closed', async () => {
  const source = await text0(SOURCE);
  const mutations = [
    source.replace('| none => config\n  | some next => next', '| none => startConfig machine []\n  | some next => next'),
    source.replace('rest.length = fuel ∧', 'True ∧'),
    source.replace('BitString.pair fixed.input fixed.certificate', 'fixed.input'),
    `${source}\ntheorem cnfSATNPComplete := True\n`,
  ];
  for (const [index, mutated] of mutations.entries()) {
    assert.notEqual(mutated, source, `mutation ${index} changed source`);
    assert.notDeepEqual(validate0(mutated), [], `mutation ${index} rejected`);
  }
});

test('tableau milestone preserves the fail-closed publication boundary', async () => {
  const status = JSON.parse(await text0('status/FORMAL_RECONSTRUCTION_STATUS.json'));
  assert.equal(status.leanConcreteCNFNPCompletenessFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.ok(status.remainingBlockers.includes('Formal.ConcreteSAT'));
});
