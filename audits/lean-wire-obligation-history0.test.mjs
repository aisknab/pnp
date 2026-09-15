import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  hasLeanAssumptionDeclaration0, hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const sourceURL = new URL('../lean/PNP/NANDWireObligationHistory.lean', import.meta.url);
const compact = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
function inspect(source) {
  const text = compact(source);
  const failures = [];
  const require = (condition, name) => { if (!condition) failures.push(name); };
  require(!hasLeanAssumptionDeclaration0(source), 'no-assumptions');
  require(!hasUnauditedLeanDeclarationForm0(source), 'audited-declarations');
  require(!/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical)\b/u.test(text), 'no-shortcuts');
  require(text.includes('structure RawEvent (fields : Nat) where identity : Nat predecessorIDs : List Nat action : Action fields deriving Repr, DecidableEq'), 'raw-only-inputs');
  require(text.includes('| realizeR7 (creationID : Nat) (records : List RawSupportRecord) | normalize'), 'raw-r7-only-inputs');
  require(text.includes('| .cancelR6 identity => [identity] | .restoreR8 identity => [identity] | .realizeR7 identity _ => [identity]'), 'intrinsic-discharge-dependency');
  require(text.includes('event.predecessorIDs ++ event.action.creationDependencies'), 'complete-dependency-list');
  require(text.includes('decide ((raw.get left).identity = (raw.get right).identity → left = right)'), 'global-identity-injectivity');
  require(text.includes('(raw.get consumer).dependencies.all fun identity => (allFin raw.length).any fun producer'), 'every-reference-present');
  require(text.includes('decide ((raw.get producer).identity ∈ (raw.get consumer).dependencies)'), 'actual-predecessor-graph');
  require(text.includes('if unique : uniqueIDs raw = true then if complete : completeReferences raw = true then match PNP.DependencyScheduler.compile (eventGraph raw) with | none => none'), 'validated-computed-order');
  require(text.includes('UniqueIDs raw ∧ CompleteReferences raw ∧ WellFounded (eventGraph raw).Depends'), 'full-ordering-contract');
  for (const name of ['order_complete', 'order_nodup', 'order_length', 'identities_nodup']) {
    require(text.includes('theorem OrderedEvents.' + name), 'exact-once:' + name);
  }
  return failures;
}

test('M263 raw event ordering derives all dependency and identity checks', async () => {
  assert.deepEqual(inspect(await readFile(sourceURL, 'utf8')), []);
});

test('M263 raw event ordering rejects missing guards and supplied ordering', async () => {
  const source = await readFile(sourceURL, 'utf8');
  for (const [before, after, category] of [
    ['predecessorIDs : List Nat', 'predecessorIDs : List Nat\n  suppliedWitness : True', 'raw-only-inputs'],
    ['| realizeR7 (creationID : Nat) (records : List RawSupportRecord)', '| realizeR7 (creationID : Nat) (records : List RawSupportRecord) (supplied : True)', 'raw-r7-only-inputs'],
    ['| .restoreR8 identity => [identity]', '| .restoreR8 identity => []', 'intrinsic-discharge-dependency'],
    ['| .realizeR7 identity _ => [identity]', '| .realizeR7 identity _ => []', 'intrinsic-discharge-dependency'],
    ['event.predecessorIDs ++ event.action.creationDependencies', 'event.predecessorIDs', 'complete-dependency-list'],
    ['(raw.get left).identity = (raw.get right).identity → left = right', 'left = left', 'global-identity-injectivity'],
    ['(raw.get consumer).dependencies.all fun identity', '(raw.get consumer).dependencies.any fun identity', 'every-reference-present'],
    ['if unique : uniqueIDs raw = true then', 'if unique : True then', 'validated-computed-order'],
    ['if complete : completeReferences raw = true then', 'if complete : True then', 'validated-computed-order'],
    ['PNP.DependencyScheduler.compile (eventGraph raw)', 'callerSuppliedOrder raw', 'validated-computed-order'],
  ]) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    assert.ok(inspect(source.replaceAll(before, after)).includes(category), category);
  }
});

test('M263 ordering source has no assumed well-foundedness or native proof authority', async () => {
  const source = await readFile(sourceURL, 'utf8');
  assert.ok(inspect(source + '\naxiom assumedOrder : False\n').includes('no-assumptions'));
  assert.ok(inspect(source + '\nnoncomputable def chosenSchedule := Classical.choice\n').includes('no-shortcuts'));
});
