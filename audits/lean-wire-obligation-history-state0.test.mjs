import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  hasLeanAssumptionDeclaration0, hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const sourceURL = new URL('../lean/PNP/NANDWireObligationHistoryState.lean', import.meta.url);
const compact = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
function inspect(source) {
  const text = compact(source);
  const failures = [];
  const require = (condition, name) => { if (!condition) failures.push(name); };
  require(!hasLeanAssumptionDeclaration0(source), 'no-assumptions');
  require(!hasUnauditedLeanDeclarationForm0(source), 'audited-declarations');
  require(!/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical)\b/u.test(text), 'no-shortcuts');
  require(text.includes('carrier := state.current fullValue := fun valuation => state.available valuation field available'), 'actual-pre-drop-snapshot');
  require(text.includes('current := masked state.current (keepExcept field)'), 'quotient-only-create');
  require(text.includes('pending := setPending state.pending field (some (state.capture identity field available))'), 'created-binding');
  require(text.includes('current := state.current.normalize pending := state.pending'), 'immutable-normalized-snapshots');
  require(text.includes('removed := state.removed + (runPhysicalNormalization state.current.exposed).trace.savedGates'), 'actual-normalization-savings');
  require(text.includes('current := join state.current (materializer snapshot.carrier (keepExcept field)) (keepExcept field)'), 'captured-materializer');
  require(text.includes('charged := state.charged + (materializer snapshot.carrier (keepExcept field)).implementation.gateCount'), 'whole-physical-charge');
  require(text.includes('(state.pending field).isNone'), 'derived-availability');
  require(text.includes('WireQuotientLift.QuotientAgreement source state.keep state.current'), 'transported-quotient');
  require(text.includes('alias.full_value state.current state.currentAgreement valuation'), 'actual-visible-full-value');
  require(text.includes('balance : current.implementation.gateCount + removed = source.implementation.gateCount + charged'), 'physical-balance');
  require(text.includes('(closed : ∀ field, state.pending field = none)'), 'all-obligations-closed');
  return failures;
}

test('M263 physical history state retains source snapshots and exact gate accounting', async () => {
  assert.deepEqual(inspect(await readFile(sourceURL, 'utf8')), []);
});

test('M263 history state rejects forgotten snapshots, free restoration and false closure', async () => {
  const source = await readFile(sourceURL, 'utf8');
  for (const [before, after, category] of [
    ['carrier := state.current', 'carrier := source', 'actual-pre-drop-snapshot'],
    ['current := masked state.current (keepExcept field)', 'current := projected state.current (keepExcept field)', 'quotient-only-create'],
    ['current := state.current.normalize\n  pending := state.pending', 'current := state.current.normalize\n  pending := fun _ => none', 'immutable-normalized-snapshots'],
    ['(runPhysicalNormalization state.current.exposed).trace.savedGates', '0', 'actual-normalization-savings'],
    ['materializer snapshot.carrier (keepExcept field)', 'materializer source (keepExcept field)', 'captured-materializer'],
    ['charged := state.charged + (materializer snapshot.carrier (keepExcept field)).implementation.gateCount', 'charged := state.charged', 'whole-physical-charge'],
    ['(state.pending field).isNone', 'true', 'derived-availability'],
    ['alias.full_value state.current state.currentAgreement valuation', 'suppliedFullWitness valuation', 'actual-visible-full-value'],
    ['(closed : ∀ field, state.pending field = none)', '(closed : True)', 'all-obligations-closed'],
  ]) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    assert.ok(inspect(source.replaceAll(before, after)).includes(category), category);
  }
});

test('M263 state forbids replacing derived semantics with project assumptions', async () => {
  const source = await readFile(sourceURL, 'utf8');
  assert.ok(inspect(source + '\naxiom inventedFullValue : False\n').includes('no-assumptions'));
  assert.ok(inspect(source + '\nnoncomputable def hiddenWitness := Classical.choice\n').includes('no-shortcuts'));
});
