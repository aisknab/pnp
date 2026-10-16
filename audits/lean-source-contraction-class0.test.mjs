import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const fixture0 = JSON.parse(await text0('audits/fixtures/source-contraction-class-source-contract0.json'));
const base0 = 'lean/PNP/Concrete/ResidualReduction/';
const newFiles0 = ['SourceContractionClass', 'SourceClassCompleteness', 'SourceClassChart']
  .map(name => base0 + name + '.lean');
const reviewedNames0 = [
  "PNP.Concrete.ResidualReduction.SourceClass.coefficient_implies_menu",
  "PNP.Concrete.ResidualReduction.SourceClass.decode_encode_eq_retraction",
  "PNP.Concrete.ResidualReduction.SourceClass.globalStep_complete_for_chart",
  "PNP.Concrete.ResidualReduction.SourceClass.globalStep_complete_for_semantic",
  "PNP.Concrete.ResidualReduction.SourceClass.globalStep_none_no_semantic",
  "PNP.Concrete.ResidualReduction.SourceClass.quadratic_of_third_zero",
  "PNP.Concrete.ResidualReduction.SourceClass.semantic_iff_chart",
  "PNP.Concrete.ResidualReduction.SourceClass.semantic_iff_coefficient",
  "PNP.Concrete.ResidualReduction.SourceClass.semantic_implies_coefficient",
  "PNP.Concrete.ResidualReduction.SourceClass.third_zero_iff_quadratic"
];
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');
const heads0 = source => explicitLeanDeclarationHeads0(source).map(({kind, name}) => ({kind, name}));
const imports0 = source => [...stripLeanCommentsAndStrings0(source)
  .matchAll(/^(?:public[ \t]+)?import[ \t]+([^\n]+)/gmu)]
  .flatMap(match => match[1].trim().split(/\s+/u)).filter(name => /^PNP(?:\.|$)/u.test(name));

function inspect0(spec, source) {
  const issues = [];
  if (newFiles0.includes(spec.file) && hasLeanAssumptionDeclaration0(source))
    issues.push('assumption declaration');
  if (/\b(?:sorry|admit|unsafe|native_decide)\b|decide\s+\+native/u.test(stripLeanCommentsAndStrings0(source)))
    issues.push('unchecked authority');
  if (digest0(source) !== spec.sourceContractSha256) issues.push('changed reviewed contract');
  return issues;
}
async function closure0(roots) {
  const seen = new Map(), pending = [...roots];
  while (pending.length) {
    const module = pending.pop();
    if (seen.has(module)) continue;
    assert.match(module, /^PNP(?:\.[A-Za-z0-9_]+)*$/u);
    const file = 'lean/' + module.replaceAll('.', '/') + '.lean';
    const source = await text0(file);
    seen.set(module, {file, source});
    pending.push(...imports0(source));
  }
  return [...seen.values()].sort((a, b) => a.file.localeCompare(b.file, 'en'));
}

test('source contraction class: frozen compiled closure and independent auxiliary contracts', async () => {
  assert.equal(fixture0.kind, 'PNPSourceContractionClassSourceContract0');
  assert.equal(fixture0.version, 0);
  assert.deepEqual(fixture0.rootModules, ['PNP.Concrete.ResidualReduction.SourceClassChart']);
  assert.deepEqual(fixture0.allowedAxioms, ['propext', 'Quot.sound']);
  const actual = await closure0(fixture0.rootModules);
  assert.deepEqual(actual.map(row => row.file), fixture0.files.map(row => row.file));
  for (const row of actual) {
    const spec = fixture0.files.find(item => item.file === row.file);
    assert.deepEqual(inspect0(spec, row.source), [], row.file);
    assert.deepEqual(inspect0(spec, row.source + '\n/- explanatory prose only -/\n'), [], row.file);
  }
  for (const spec of fixture0.auxiliaryContracts)
    assert.deepEqual(inspect0(spec, await text0(spec.file)), [], spec.file);
});

test('source contraction class: explicit root and exact independently reviewed theorem set', async () => {
  const [root, audit, regression] = await Promise.all([
    text0('lean/PNP.lean'), text0('lean-audit/PNPSourceContractionClassAxiomAudit.lean'),
    text0('lean-regression/PNPSourceContractionClass.lean'),
  ]);
  assert.equal(root.split('\n').filter(line =>
    line === 'import PNP.Concrete.ResidualReduction.SourceClassChart').length, 1);
  assert.match(audit, /^import PNP\n/u);
  assert.match(regression, /^import PNP\n/u);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]).sort(),
    reviewedNames0);
  assert.deepEqual(fixture0.auditedTheorems, reviewedNames0);
  for (const file of newFiles0) {
    const source = await text0(file);
    assert.equal(hasUnauditedLeanDeclarationForm0(source), false, file);
    assert.deepEqual(heads0(source), fixture0.newModuleDeclarationHeads[file], file);
  }
  assert.equal((regression.match(/^example\b/gmu) ?? []).length, 6);
  assert.equal((regression.match(/^theorem\b/gmu) ?? []).length, 4);
  assert.deepEqual([...regression.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]), [
    'exhausted_class_can_be_satisfiable', 'balance_does_not_supply_degree_closure',
    'unselected_cubic_row_blocks_closure', 'affine_constants_are_retained',
  ].map(name => 'PNP.Concrete.SourceClassRegression.' + name));
  assert.ok(regression.includes('source-class-regressions-complete'));
  assert.doesNotMatch(stripLeanCommentsAndStrings0(audit), /^#eval\b/mu);
});

test('source contraction class: supplied authority and unchecked shortcuts reject', async () => {
  for (const file of newFiles0) {
    const source = await text0(file), spec = fixture0.files.find(row => row.file === file);
    for (const extra of [
      'axiom suppliedContraction : True', 'private axiom suppliedRuntime : True',
      'opaque suppliedCoverage : True', 'theorem fabricatedResult : True := by sorry',
      'variable (suppliedCorrectness : Prop)', 'import PNP.Main',
    ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length, file + ': ' + extra);
  }
});

test('source contraction class: exact class, complete rows, existence premise and decoder cannot drift', async () => {
  for (const [file, label, before, after] of [
    ['SourceContractionClass', 'input-derived scalar', 'if weightedValue F w x then pXor x v else x',
      'if suppliedScalar x then pXor x v else x'],
    ['SourceContractionClass', 'balance for all points', '∀ x, weightedPolar F w x v = false',
      'weightedPolar F w (zeroPoint n) v = false'],
    ['SourceContractionClass', 'unselected source rows retained', '∀ r ∈ F, ∃ q : Quadratic n, ∀ x,',
      '∀ r ∈ F.take 1, ∃ q : Quadratic n, ∀ x,'],
    ['SourceContractionClass', 'quadratic ambient semantics', 'qEval q x = r.eval (sourceRetraction F w v x)',
      'True'],
    ['SourceClassCompleteness', 'semantic not supplied menu', '(h : ∃ w v, SemanticContraction F w v)',
      '(h : MenuEligible F)'],
    ['SourceClassCompleteness', 'existence not universal progress', '(h : ∃ w v, SemanticContraction F w v)',
      '(h : True)'],
    ['SourceClassCompleteness', 'stopping is only class exclusion',
      ': ¬ ∃ w v, SemanticContraction F w v :=', ': ∀ x, models F x = false :='],
    ['SourceClassChart', 'actual quotient decoder', 'r.eval (decode (markSource F w) c.1 c.2 z)',
      'r.eval (suppliedDecoder z)'],
    ['SourceClassChart', 'ambient not just model equality',
      '(hc : chooseChart v = some c) (hb : Balanced F w v) (x : Point (n+1))',
      '(hc : chooseChart v = some c) (hb : Balanced F w v) (x : Point (n+1)) (model : models F x = true)'],
  ]) {
    const path = base0 + file + '.lean';
    const source = await text0(path), spec = fixture0.files.find(row => row.file === path);
    assert.ok(source.includes(before), 'missing mutation anchor: ' + label);
    const changed = source.replace(before, () => after);
    assert.notEqual(changed, source, label);
    assert.ok(inspect0(spec, changed).length, 'accepted mutation: ' + label);
  }
});

test('source contraction class: original selector dependencies cannot change behind class proofs', async () => {
  for (const name of ['SourceGlobalSelector', 'SourceRankOneQuery', 'SourceRankTwoQuery']) {
    const file = base0 + name + '.lean';
    const spec = fixture0.files.find(row => row.file === file);
    assert.ok(spec, file);
    const source = await text0(file);
    assert.ok(inspect0(spec, source + '\naxiom suppliedCompleteness : True\n').length, file);
  }
});
