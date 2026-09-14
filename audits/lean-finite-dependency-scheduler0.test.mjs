import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  hasLeanAssumptionDeclaration0, hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const sourceURL = new URL('../lean/PNP/FiniteDependencyScheduler.lean', import.meta.url);
const compact = source => stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim();
function inspect(source) {
  const text = compact(source);
  const failures = [];
  const require = (condition, name) => { if (!condition) failures.push(name); };
  require(!hasLeanAssumptionDeclaration0(source), 'no-assumptions');
  require(!hasUnauditedLeanDeclarationForm0(source), 'audited-declarations');
  require(!/\b(?:sorry|admit|unsafe|native_decide|noncomputable|Classical)\b/u.test(text), 'no-shortcuts');
  require(text.includes('structure Graph (nodes : Nat) where predecessors : Fin nodes → List (Fin nodes)'), 'arbitrary-finite-predecessors');
  require(text.includes('producer ∈ graph.predecessors consumer'), 'actual-dependency-edges');
  require(text.includes('(graph.predecessors node).all (fun producer => (state.position producer).isSome)'), 'all-predecessors-ready');
  require(text.includes('remaining := state.remaining.erase step.node'), 'strict-node-removal');
  require(text.includes('at_position : ∀ node, nodeAt (position node) = node') &&
    text.includes('position_at : ∀ index, position (nodeAt index) = index'), 'complete-bijective-order');
  require(text.includes('ordered : ∀ producer consumer, graph.Depends producer consumer → (position producer).val < (position consumer).val'), 'strict-edge-order');
  require(text.includes('def compile {nodes : Nat} (graph : Graph nodes) : Option (Schedule graph) := let stop := run (State.initial graph) if complete : stop.state.remaining = [] then some (stop.state.finish complete) else none'), 'computed-fail-closed-schedule');
  require(text.includes('theorem compile_success_iff {nodes : Nat} (graph : Graph nodes) : (∃ schedule, compile graph = some schedule) ↔ WellFounded graph.Depends'), 'general-success-type');
  require(text.includes('theorem compile_failure_iff {nodes : Nat} (graph : Graph nodes) : compile graph = none ↔ ¬WellFounded graph.Depends'), 'general-rejection-type');
  for (const name of ['Schedule.order_complete', 'Schedule.order_nodup', 'Schedule.order_length']) {
    require(text.includes('theorem ' + name + ' {nodes : Nat}'), 'general-order-evidence:' + name);
  }
  return failures;
}

test('M263 scheduler is computed for arbitrary finite dependency lists', async () => {
  assert.deepEqual(inspect(await readFile(sourceURL, 'utf8')), []);
});

test('M263 scheduler rejects source mutations that skip dependencies or accept stuck nodes', async () => {
  const source = await readFile(sourceURL, 'utf8');
  for (const [before, after, category] of [
    ['predecessors : Fin nodes → List (Fin nodes)', 'predecessors : Fin nodes → Fin nodes', 'arbitrary-finite-predecessors'],
    ['producer ∈ graph.predecessors consumer', 'producer = consumer', 'actual-dependency-edges'],
    ['(graph.predecessors node).all', '(graph.predecessors node).any', 'all-predecessors-ready'],
    ['remaining := state.remaining.erase step.node', 'remaining := state.remaining', 'strict-node-removal'],
    ['(position producer).val < (position consumer).val', '(position producer).val ≤ (position consumer).val', 'strict-edge-order'],
    ['if complete : stop.state.remaining = [] then', 'if complete : True then', 'computed-fail-closed-schedule'],
  ]) {
    assert.ok(source.includes(before), 'mutation anchor: ' + category);
    assert.ok(inspect(source.replaceAll(before, after)).includes(category), category);
  }
});

test('M263 scheduler does not accept a supplied schedule or proof shortcut', async () => {
  const source = await readFile(sourceURL, 'utf8');
  assert.ok(inspect(source.replace('let stop := run (State.initial graph)',
    'let stop := callerSuppliedStop')).includes('computed-fail-closed-schedule'));
  assert.ok(inspect(source + '\naxiom inventedOrdering : False\n').includes('no-assumptions'));
  assert.ok(inspect(source + '\nnoncomputable def hiddenChoice := Classical.choice\n').includes('no-shortcuts'));
});
