import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const SOURCE = 'lean/PNP/NANDGrowingWindowUniverseBound.lean';
const PROBE = 'lean-regression/PNPGrowingWindowUniverseBoundProbe.lean';
const NAMESPACE = 'PNP.DirectWire.GrowingWindowUniverseBound';
const HEADS = [
  ['theorem', 'programs_tail_length_le'],
  ['theorem', 'smallerCandidates_exceeds_polynomial'],
  ['def', 'query'],
  ['def', 'queryLengthPolynomial'],
  ['theorem', 'query_length_le'],
  ['theorem', 'valid_requires_full_budget'],
  ['theorem', 'valid_universe_exceeds_encoded_polynomial'],
  ['theorem', 'no_uniform_polynomial_complete_universe'],
];
const THEOREMS = HEADS.filter(([kind]) => kind === 'theorem').map(([, name]) => NAMESPACE + '.' + name);
const PROBES = [
  'zero_gate_count', 'one_gate_count', 'two_gate_count', 'exact_small_universe',
  'empty_budget', 'query_roundtrip', 'query_elaborates',
  'every_polynomial_at_real_bits', 'complete_uniform_polynomial_contradiction',
].map(name => 'PNP.DirectWire.GrowingWindowUniverseBoundProbe.' + name);
// Reviewed independent contracts, never recomputed from the input under test.
const SOURCE_SHA256 = '3f976e8b5251b1d84c128f9b971d44897fede7071d7465a49f3afa493e45f4f6';
const PROBE_SHA256 = 'ec2d7f919a43635a0e586e6f43ebc9f79072df028293d7abe7ca9156e36d45e7';
const read0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');
const printed0 = source => [...source.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]);

function inspect0(source) {
  const issues = [];
  if (hasLeanAssumptionDeclaration0(source)) issues.push('assumption declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) issues.push('unaudited declaration');
  const clean = stripLeanCommentsAndStrings0(source);
  if (/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|implemented_by|csimp)\b|decide\s+\+native/u.test(clean))
    issues.push('unsupported proof authority');
  const heads = explicitLeanDeclarationHeads0(source).map(({kind, name}) => [kind, name]);
  if (JSON.stringify(heads) !== JSON.stringify(HEADS)) issues.push('declaration contract');
  if (digest0(source) !== SOURCE_SHA256) issues.push('source contract');
  return issues;
}

test('growing-window bound retains the complete reviewed general statement and actual enumerator', async () => {
  assert.deepEqual(inspect0(await read0(SOURCE)), []);
});

const mutations = [
  ['all polynomials', '(polynomial : NatPolynomial)', '(polynomial : Fin 10)'],
  ['unbounded source family', '∀ n : Nat,', '∀ n : Fin 10,'],
  ['all record widths', '(width : Nat)', '(width : Fin 1)'],
  ['arbitrary records', '(records : List (TerminalPrimitiveRecord', '(records : Array (TerminalPrimitiveRecord'],
  ['real encoded bit length', 'polynomial.eval (query n).length', 'polynomial.eval n'],
  ['actual universe', '(candidateUniverse (candidate (n + 2)) records).length', '0'],
  ['strict count separation', 'polynomial.eval n < (smallerCandidates', 'polynomial.eval n ≤ (smallerCandidates'],
  ['strict nonminimum witness', '0 < residualSlack', '0 ≤ residualSlack'],
  ['complete polynomial negation', '¬ ∃ polynomial : NatPolynomial', '∃ polynomial : NatPolynomial'],
  ['no supplied completeness premise', 'theorem no_uniform_polynomial_complete_universe :',
    'theorem no_uniform_polynomial_complete_universe (suppliedCoverage : False) :'],
  ['actual encoding', 'def query (n : Nat) : Concrete.BitString :=', 'def query (n : Nat) : Concrete.BitString := [] --'],
  ['real threshold', '(candidate (n + 2)) (n + 3)', '(candidate (n + 2)) 0'],
  ['actual gate budget', 'n + 4 ≤ (extractTerminalSupport', 'n + 3 ≤ (extractTerminalSupport'],
];
for (const [label, before, after] of mutations) {
  test('growing-window contract rejects substitution: ' + label, async () => {
    const source = await read0(SOURCE);
    assert.ok(source.includes(before), 'mutation target must exist');
    const changed = source.replace(before, after);
    assert.notEqual(changed, source);
    assert.ok(inspect0(changed).length > 0);
  });
}
for (const declaration of ['axiom supplied : False', 'opaque supplied : False', 'theorem bypass : True := by sorry']) {
  test('growing-window contract rejects added authority: ' + declaration.split(' ')[0], async () => {
    assert.ok(inspect0((await read0(SOURCE)) + '\n' + declaration + '\n').length > 0);
  });
}

test('growing-window conclusions and regression probes bind to the explicit root', async () => {
  const root = await read0('lean/PNP.lean');
  assert.equal(root.split('\n').filter(line => line === 'import PNP.NANDGrowingWindowUniverseBound').length, 1);
  const audit = await read0('lean-audit/PNPGrowingWindowUniverseBoundAxiomAudit.lean');
  const probe = await read0(PROBE);
  assert.match(audit, /^import PNP\n/u);
  assert.match(probe, /^import PNP\n/u);
  assert.deepEqual(printed0(audit).sort(), THEOREMS.slice().sort());
  assert.deepEqual(printed0(probe).sort(), PROBES.slice().sort());
  assert.equal(digest0(probe), PROBE_SHA256);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(probe),
    /\b(?:sorry|admit|unsafe|native_decide|Classical)\b|decide\s+\+native|#(?:eval|reduce)/u);
});

test('growing-window boundary remains in durable read-only verification', async () => {
  const workflow = await read0('.github/workflows/lean-bridge.yml');
  const verifier = await import('../scripts/pnp-verify-all.mjs');
  for (const file of [
    'audits/lean-growing-window-universe-bound0.test.mjs',
    'audits/lean-growing-window-universe-bound-publication0.test.mjs',
  ]) assert.ok(verifier.CURRENT_VERIFICATION_TESTS0.includes(file), file);
  for (const command of [
    'for name in JointAsymmetricBound GuardedSpineSupportMinimum GuardedSpineBoundedQuiet GrowingWindowUniverseBound; do',
    'node --test audits/lean-{fixed-window-coverage-obstruction,growing-window-universe-bound}{0,-publication0}.test.mjs',
    'node scripts/check-lean-axioms.mjs "lean-audit/PNP${name}AxiomAudit.lean"',
    'lake env lean -DwarningAsError=true "lean-regression/PNP${name}Probe.lean"',
  ]) assert.ok(workflow.includes(command), command);
});

test('growing-window documentation separates list size, runtime and proof completion', async () => {
  const doc = (await read0('docs/lean_growing_window_universe_bound.md')).replace(/\s+/gu, ' ');
  for (const phrase of [
    'actual encoded bit length', 'materialized-list cardinality bound',
    'not a lower bound on the number of candidates visited',
    'a raw-machine runtime lower bound', 'does not decide P versus NP',
    'No positive publication row or fixed checkpoint is awarded',
    'Defer a separate website update',
    'Formal artefact coverage:', 'Risk-weighted proof completion estimate:',
    'Uncertainty range:', 'Global gates closed:',
  ]) assert.ok(doc.includes(phrase), phrase);
});
