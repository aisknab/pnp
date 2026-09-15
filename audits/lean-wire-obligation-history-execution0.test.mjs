import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  hasLeanAssumptionDeclaration0, hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const sourceURL = new URL('../lean/PNP/NANDWireObligationHistoryExecution.lean', import.meta.url);
const compact = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
function inspect(source) {
  const text = compact(source);
  const failures = [];
  const require = (condition, name) => { if (!condition) failures.push(name); };
  require(!hasLeanAssumptionDeclaration0(source), 'no-assumptions');
  require(!hasUnauditedLeanDeclarationForm0(source), 'audited-declarations');
  require(!/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical)\b/u.test(text), 'no-shortcuts');
  require(text.includes('found : state.pending field = some snapshot identified : snapshot.identity = identity'), 'exact-open-creation');
  require(text.includes('if same : snapshot.identity = identity then some ⟨field, snapshot, found, same⟩'), 'computed-identity-lookup');
  require(text.includes('scanPending state identity (allFin fields)'), 'all-field-lookup');
  require(text.includes('match computed : WireMatchedCancellation.representative source state.keep entry.field with | none => none'), 'computed-visible-r6');
  require(text.includes('match computed : computeR7 entry.snapshot.carrier raw with | none => none'), 'captured-computed-r7');
  require(text.includes('(materializer realization.carrier (keepExcept entry.field)).implementation.gateCount'), 'actual-r7-trace-charge');
  require(text.includes('fullWitness := before.restoreR7_full_value entry.field entry.snapshot entry.found raw realization'), 'derived-r7-discharge-record');
  require(text.includes('| .readFull field => match available : state.pending field with | none => some ⟨state, .read state event field kind available⟩ | some _ => none'), 'full-read-firewall');
  require(text.includes('(materializer entry.snapshot.carrier (keepExcept entry.field)).implementation.gateCount'), 'actual-trace-charge');
  require(text.includes('(runPhysicalNormalization before.current.exposed).trace.savedGates'), 'actual-trace-savings');
  require(text.includes('let next ← applyEvent state event let rest ← execute next.1 remaining return ⟨rest.1, .cons next.2 rest.2⟩'), 'one-transition-per-event');
  require(text.includes('execution : Execution source (State.initial source) (ordered.order.map raw.get) state'), 'source-bound-full-trace');
  require(text.includes('def compileHistory (source : WireCarrier inputs outputs fields) (raw : List (RawEvent fields)) : Option (ClosedHistory source raw) := do let ordered ← orderEvents raw let result ← execute (State.initial source) (ordered.order.map raw.get) if closed : result.1.isClosed = true then return ⟨ordered, result.1, result.2, result.1.isClosed_sound closed⟩ else none'), 'computed-closed-history');
  require(text.includes('step.created = some ⟨field, snapshot⟩ → tail.Discharged field snapshot'), 'strictly-later-discharge');
  require(text.includes('fullWitness := before.restore_full_value entry.field entry.snapshot entry.found') &&
    text.includes('fullWitness := before.cancel_full_value entry.field entry.snapshot entry.found alias'), 'derived-discharge-records');
  require(text.includes('history.state.current.implementation.gateCount + history.execution.removed = source.implementation.gateCount + history.execution.charged'), 'trace-derived-physical-balance');
  for (const name of ['full_output', 'full_field', 'gate_balance', 'creation_lifecycle', 'executed_count', 'executed_identities_nodup', 'dependency_before']) {
    require(text.includes('theorem ' + name + ' (history : ClosedHistory source raw)'), 'closed-result:' + name);
  }
  return failures;
}

test('M263 executes all raw events with source-bound records and closed lifecycle evidence', async () => {
  assert.deepEqual(inspect(await readFile(sourceURL, 'utf8')), []);
});

test('M263 execution rejects wrong identities, quotient reads and incomplete histories', async () => {
  const source = await readFile(sourceURL, 'utf8');
  for (const [before, after, category] of [
    ['if same : snapshot.identity = identity then', 'if same : True then', 'computed-identity-lookup'],
    ['computeR7 entry.snapshot.carrier raw', 'computeR7 state.current raw', 'captured-computed-r7'],
    ['(materializer realization.carrier (keepExcept entry.field)).implementation.gateCount', '0', 'actual-r7-trace-charge'],
    ['fullWitness := before.restoreR7_full_value entry.field entry.snapshot entry.found raw realization', 'fullWitness := suppliedWitness', 'derived-r7-discharge-record'],
    ['scanPending state identity (allFin fields)', 'scanPending state identity []', 'all-field-lookup'],
    ['WireMatchedCancellation.representative source state.keep entry.field', 'callerSuppliedRepresentative', 'computed-visible-r6'],
    ['(materializer entry.snapshot.carrier (keepExcept entry.field)).implementation.gateCount', '0', 'actual-trace-charge'],
    ['let rest ← execute next.1 remaining', 'let rest ← execute next.1 []', 'one-transition-per-event'],
    ['(State.initial source) (ordered.order.map raw.get)', '(State.initial source) []', 'source-bound-full-trace'],
    ['if closed : result.1.isClosed = true then', 'if closed : True then', 'computed-closed-history'],
    ['→ tail.Discharged field snapshot', '→ True', 'strictly-later-discharge'],
    ['fullWitness := before.restore_full_value entry.field entry.snapshot entry.found', 'fullWitness := suppliedValueWitness', 'derived-discharge-records'],
  ]) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    assert.ok(inspect(source.replaceAll(before, after)).includes(category), category);
  }
});

test('M263 execution cannot be replaced with supplied state or proof authority', async () => {
  const source = await readFile(sourceURL, 'utf8');
  assert.ok(inspect(source.replace('let ordered ← orderEvents raw', 'let ordered ← suppliedOrder raw')).includes('computed-closed-history'));
  assert.ok(inspect(source + '\naxiom assumedDischarge : False\n').includes('no-assumptions'));
  assert.ok(inspect(source + '\nnoncomputable def hiddenWitness := Classical.choice\n').includes('no-shortcuts'));
});
