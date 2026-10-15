import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const fixture0 = JSON.parse(await text0('audits/fixtures/residual-reducer-source-contract0.json'));
const facade0 = 'lean/PNP/Concrete/ResidualReducer.lean';
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');
const heads0 = source => explicitLeanDeclarationHeads0(source).map(({kind, name}) => ({kind, name}));
const imports0 = source => [...stripLeanCommentsAndStrings0(source)
  .matchAll(/^(?:public[ \t]+)?import[ \t]+([^\n]+)/gmu)]
  .flatMap(match => match[1].trim().split(/\s+/u)).filter(name => /^PNP(?:\.|$)/u.test(name));

function inspect0(spec, source) {
  const issues = [];
  if (spec.file === facade0 && hasLeanAssumptionDeclaration0(source))
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

test('residual reducer: frozen compiled source closure and auxiliary contracts', async () => {
  assert.equal(fixture0.kind, 'PNPResidualReducerSourceContract0');
  assert.equal(fixture0.version, 0);
  assert.deepEqual(fixture0.rootModules, ['PNP.Concrete.ResidualReducer']);
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

test('residual reducer: public root, declaration heads and exact audited theorem set', async () => {
  const [source, root, audit, regression] = await Promise.all([
    text0(facade0), text0('lean/PNP.lean'),
    text0('lean-audit/PNPResidualReducerAxiomAudit.lean'),
    text0('lean-regression/PNPResidualReducer.lean'),
  ]);
  assert.equal(hasUnauditedLeanDeclarationForm0(source), false);
  assert.deepEqual(heads0(source), fixture0.facadeDeclarationHeads);
  assert.equal(root.split('\n').filter(line => line === 'import PNP.Concrete.ResidualReducer').length, 1);
  assert.match(audit, /^import PNP\n/u);
  assert.match(regression, /^import PNP\n/u);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]),
    fixture0.auditedTheorems);
  assert.deepEqual(fixture0.auditedTheorems,
    heads0(source).filter(row => row.kind === 'theorem')
      .map(row => 'PNP.Concrete.ResidualReducer.' + row.name).sort());
  assert.equal((regression.match(/^example\b/gmu) ?? []).length, 16);
  assert.equal((regression.match(/^theorem\b/gmu) ?? []).length, 10);
  assert.deepEqual([...regression.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]),
    [
      'positive_guard_retained', 'linear_guard_retained', 'product_guard_retained',
      'duplicate_terms_cancel', 'coordinate_order_retained', 'unknown_can_be_satisfiable',
      'unknown_can_be_unsatisfiable', 'zero_dimensional_success', 'zero_dimensional_failure',
      'reconstruction_requires_a_model',
    ].map(name => 'PNP.Concrete.ResidualReducerRegression.' + name));
  assert.ok(regression.includes('residual-reducer-regressions-complete: 16 general type contracts; 10 kernel guards'));
});

test('residual reducer: supplied authority and unchecked shortcuts reject', async () => {
  const source = await text0(facade0), spec = fixture0.files.find(row => row.file === facade0);
  for (const extra of [
    'axiom suppliedSolution : True', 'private axiom suppliedRuntime : True',
    'opaque suppliedCompleteness : True', 'theorem fabricatedResult : True := by sorry',
    'variable (suppliedCorrectness : Prop)', 'import PNP.Main',
  ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length, extra);
});

test('residual reducer: complete source, actual output and partial-result boundaries cannot drift', async () => {
  const source = await text0(facade0), spec = fixture0.files.find(row => row.file === facade0);
  for (const [label, before, after] of [
    ['all original bitstrings', 'def decision (input : BitString)', 'def decision (input : Fin 8)'],
    ['source language', '↔ CNFSAT input :=', '↔ True :='],
    ['complete native system', 'D.Satisfied (ResidualReduction.NativeSource.pointRows x)', 'True'],
    ['all linear and product rows', '1+D.e.length+D.a.length', 'D.a.length'],
    ['actual source output', 'NativeOutputPacket.codec.decode (SerializedNormalizer.output input)',
      'NativeOutputPacket.codec.decode suppliedOutput'],
    ['unknown is not false', 'decision input = none :=', 'decision input = some false :='],
    ['sound accepted result', '(answer : decision input = some true)', '(answer : True)'],
    ['sound rejected result', '(answer : decision input = some false)', '(answer : True)'],
    ['source inverse needs a model', '(satisfied : D.Satisfied u)', '(satisfied : True)'],
    ['certificate checker', 'NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input)',
      'suppliedChecker'],
    ['step bound uses source size', '30*input.length+12', '30*1+12'],
    ['linked history', 'ResidualReduction.SourceChain.Linked (sourceFamily D)', 'suppliedHistory'],
  ]) {
    assert.ok(source.includes(before), 'missing mutation anchor: ' + label);
    const changed = source.replace(before, () => after);
    assert.notEqual(changed, source, label);
    assert.ok(inspect0(spec, changed).length, 'accepted mutation: ' + label);
  }
});

test('residual reducer: mathematical dependencies cannot change behind the facade', async () => {
  for (const file of [
    'lean/PNP/Concrete/ResidualReduction/NativeSourceCoordinates.lean',
    'lean/PNP/Concrete/ResidualReduction/NativeSourceSystem.lean',
    'lean/PNP/Concrete/ResidualReduction/NativeSourceReduction.lean',
    'lean/PNP/Concrete/ResidualReduction/SourceReductionChain.lean',
    'lean/PNP/Concrete/ResidualReduction/SourceGlobalSelector.lean',
  ]) {
    const source = await text0(file), spec = fixture0.files.find(row => row.file === file);
    assert.ok(spec, file);
    assert.ok(inspect0(spec, source + '\naxiom suppliedCompleteness : True\n').length, file);
    assert.ok(inspect0(spec, source + '\nopaque suppliedRuntime : True\n').length, file);
  }
});

test('residual reducer: no full solver or total polynomial-runtime claim', async () => {
  const source = await text0(facade0), regression = await text0('lean-regression/PNPResidualReducer.lean');
  assert.ok(source.includes('A nonzero-dimensional stopped core remains\nunknown, not UNSAT.'));
  assert.ok(source.includes('A step-count bound is not a total polynomial runtime proof.'));
  assert.ok(source.includes('No all-input residual solver, exact PCCMin or unconditional ZeroSlack is supplied.'));
  assert.ok(source.includes('ResidualReduction.SourceChain.stopped (reduce D).core'));
  assert.ok(regression.includes('(∀ x : Point 2, models (sourceFamily impossible) x = false)'));
  assert.ok(regression.includes('models (sourceFamily positiveOnly) (true,(false,())) = true'));
});
