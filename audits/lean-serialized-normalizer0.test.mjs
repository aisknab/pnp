import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const text0 = path => readFile(new URL('../' + path, import.meta.url), 'utf8');
const fixture0 = JSON.parse(await text0('audits/fixtures/serialized-normalizer-source-contract0.json'));
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');
const facade0 = 'lean/PNP/Concrete/SerializedNormalizer.lean';
const heads0 = source => explicitLeanDeclarationHeads0(source).map(({kind, name}) => ({kind, name}));
const imports0 = source => [...stripLeanCommentsAndStrings0(source)
  .matchAll(/^(?:public[ \t]+)?import[ \t]+([^\n]+)/gmu)]
  .flatMap(match => match[1].trim().split(/\s+/u)).filter(name => /^PNP(?:\.|$)/u.test(name));
function inspect0(spec, source) {
  const issues = [];
  // Dependencies are frozen to compiled, axiom-audited hashes. The API-only
  // declaration guard must not mistake a wrapped expression's `constant` for a command.
  if (spec.file === facade0 && hasLeanAssumptionDeclaration0(source)) issues.push('assumption declaration');
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
test('serialized normalizer: exact compiled source closure, not a self-updating fixture', async () => {
  assert.equal(fixture0.kind, 'PNPSerializedNormalizerSourceContract0');
  assert.deepEqual(fixture0.rootModules, ['PNP.Concrete.SerializedNormalizer']);
  const actual = await closure0(fixture0.rootModules);
  assert.deepEqual(actual.map(row => row.file), fixture0.files.map(row => row.file));
  for (const row of actual) {
    const spec = fixture0.files.find(item => item.file === row.file);
    assert.deepEqual(inspect0(spec, row.source), [], row.file);
    assert.deepEqual(inspect0(spec, row.source + '\n/- explanatory prose only -/\n'), [], row.file);
  }
});
test('serialized normalizer: reviewed all-input public interface and exact audit names', async () => {
  const [source, root, audit, regression] = await Promise.all([
    text0(facade0), text0('lean/PNP.lean'),
    text0('lean-audit/PNPSerializedNormalizerAxiomAudit.lean'),
    text0('lean-regression/PNPSerializedNormalizer.lean'),
  ]);
  assert.equal(hasUnauditedLeanDeclarationForm0(source), false);
  assert.deepEqual(heads0(source), fixture0.facadeDeclarationHeads);
  assert.equal(root.split('\n').filter(line => line === 'import PNP.Concrete.SerializedNormalizer').length, 1);
  assert.match(audit, /^import PNP\n/u);
  assert.match(regression, /^import PNP\n/u);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]),
    fixture0.auditedTheorems);
  assert.deepEqual(fixture0.auditedTheorems, heads0(source).filter(row => row.kind === 'theorem')
    .map(row => 'PNP.Concrete.SerializedNormalizer.' + row.name));
  assert.equal((regression.match(/^example\b/gmu) ?? []).length, 12);
  assert.equal((regression.match(/^theorem\b/gmu) ?? []).length, 6);
  assert.deepEqual([...regression.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]), [
    'malformed_empty', 'empty_output_is_not_a_packet', 'malformed_packet_rejects',
    'model_framing_roundtrip', 'trailing_packet_rejected', 'empty_residual_has_no_certificate',
  ].map(name => 'PNP.Concrete.SerializedNormalizerRegression.' + name));
  assert.ok(regression.includes('serialized-normalizer-regressions-complete: 12 general type contracts; 6 kernel guards'));
});
test('serialized normalizer: added assumptions and unchecked shortcuts reject', async () => {
  const source = await text0(facade0), spec = fixture0.files.find(row => row.file === facade0);
  for (const extra of [
    'axiom suppliedSolution : True', 'private axiom suppliedRuntime : True',
    'opaque suppliedCompleteness : True', 'theorem fabricatedResult : True := by sorry',
    'variable (suppliedCorrectness : Prop)', 'import PNP.Main',
  ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length, extra);
});
test('serialized normalizer: machine, polynomial bound and complete semantic target cannot be substituted', async () => {
  const source = await text0(facade0), spec = fixture0.files.find(row => row.file === facade0);
  for (const [label, before, after] of [
    ['actual complete program', 'NormalizerBlocks.OriginalNormalizer.polynomial', 'PolynomialTimeFunction.identity'],
    ['literal machine', 'machineOutput rawRefinement.machine', 'machineOutput suppliedMachine'],
    ['encoded source size', 'rawRefinement.timeBound.eval (BitString.size input)', 'rawRefinement.timeBound.eval 1'],
    ['unbounded inputs', 'theorem output_eq (input : BitString)', 'theorem output_eq (input : Fin 8)'],
    ['source language', 'CNFSAT input := by', 'True := by'],
    ['complete residual equations', 'D.Satisfied (MeasuredBits.rowValues rows certificate)', 'True'],
    ['computed model meaning', 'F.Satisfied assignment', 'True'],
    ['explicit malformed output', 'output input = [false, false, false]', 'output input = []'],
    ['actual serialized target', 'NativeSerializedNormalizer.checkEncoded bytes certificate = true', 'True'],
  ]) {
    assert.ok(source.includes(before), 'missing mutation anchor: ' + label);
    const changed = source.replace(before, () => after);
    assert.notEqual(changed, source, label);
    assert.ok(inspect0(spec, changed).length, 'accepted mutation: ' + label);
  }
});
test('serialized normalizer: source construction retains a residual problem, not a decision procedure', async () => {
  const source = await text0(facade0);
  assert.ok(source.includes('No general residual solver or deterministic SAT decision procedure is supplied.'));
  assert.ok(source.includes('A short witness exists for satisfiable inputs; this does not find that witness.'));
  assert.ok(source.includes('A computed residual packet carries the full system, not an unsatisfiable verdict.'));
  assert.ok(source.includes('def reduction : PolynomialReduction CNFSAT language'));
});
