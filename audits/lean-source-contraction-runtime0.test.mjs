import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const fixture0 = JSON.parse(await text0('audits/fixtures/source-contraction-runtime-source-contract0.json'));
const base0 = 'lean/PNP/Concrete/ResidualReduction/';
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');
const imports0 = source => [...stripLeanCommentsAndStrings0(source)
  .matchAll(/^(?:public[ \t]+)?import[ \t]+([^\n]+)/gmu)]
  .flatMap(match => match[1].trim().split(/\s+/u)).filter(name => /^PNP(?:\.|$)/u.test(name));

// These reviewed source digests detect changed contracts. They are not proof
// authority: the explicit-root build, compiled types and axiom audit supply it.
// Check direct top-level declaration syntax here. Record fields and theorem
// terms may also use "constant"; compiled axiom closures and frozen source
// digests cover indented declarations and other syntactic forms.
const hasAssumption0 = source =>
  /^(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe)[ \t]+)*(?:axiom|constant|opaque)[ \t]+(?:«[^»\n]+»|[^\s({:=]+)/mu
    .test(stripLeanCommentsAndStrings0(source));
function inspect0(spec, source) {
  const issues = [];
  if (hasAssumption0(source)) issues.push('assumption declaration');
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
  return new Map([...seen.values()].map(row => [row.file, row.source]));
}

test('source runtime: all reviewed implementation and regression sources are root reachable', async () => {
  assert.equal(fixture0.kind, 'PNPSourceContractionRuntimeSourceContract0');
  assert.equal(fixture0.version, 0);
  assert.deepEqual(fixture0.allowedAxioms, ['propext', 'Quot.sound']);
  assert.ok(fixture0.requiredRootImports.includes('PNP.Concrete.ResidualReduction.SourceReductionRuntime'));
  assert.ok(fixture0.requiredRootImports.includes('PNP.Concrete.ResidualReduction.SourceReductionRuntimeRegression'));
  assert.equal(new Set(fixture0.requiredRootImports).size, fixture0.requiredRootImports.length);
  assert.equal(new Set(fixture0.newSources.map(row => row.file)).size, fixture0.newSources.length);
  const root = (await text0('lean/PNP.lean')).split('\n');
  for (const name of fixture0.requiredRootImports)
    assert.equal(root.filter(line => line === 'import ' + name).length, 1, name);
  const closure = await closure0(fixture0.requiredRootImports);
  for (const spec of fixture0.newSources) {
    assert.ok(closure.has(spec.file), 'unreachable reviewed source: ' + spec.file);
    const source = closure.get(spec.file);
    assert.deepEqual(inspect0(spec, source), [], spec.file);
    assert.deepEqual(inspect0(spec, source + '\n/- explanatory prose only -/\n'), [], spec.file);
  }
});

test('source runtime: the root audit uses the exact reviewed endpoint declarations', async () => {
  const audit = await text0('lean-audit/PNPSourceContractionRuntimeAxiomAudit.lean');
  assert.match(audit, /^import PNP\n/u);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]),
    fixture0.auditedTheorems);
  assert.equal(fixture0.auditedTheorems.length, 14);
  assert.equal(new Set(fixture0.auditedTheorems).size, 14);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(audit), /^#eval\b/mu);
  const contracts = await text0(base0 + 'SourceReductionRuntimeRegression.lean');
  assert.equal((contracts.match(/^example\b/gmu) ?? []).length, 12);
  assert.ok(contracts.includes('SOURCE_REDUCTION_RUNTIME_AXIOMS_GREEN'));
  assert.ok(contracts.includes('SOURCE_REDUCTION_RUNTIME_CONTRACT_GREEN'));
});

test('source runtime: supplied authority and unchecked proof shortcuts reject', async () => {
  for (const name of ['SourceReductionRuntime', 'SourceReductionPolynomial',
    'SourceReplayEndpointPolynomial', 'SourceReplayEndpointGenerated', 'SourceReplayEndpointBudget']) {
    const file = base0 + name + '.lean';
    const spec = fixture0.newSources.find(row => row.file === file);
    assert.ok(spec, file);
    const source = await text0(file);
    for (const extra of [
      'axiom suppliedSolver : True', 'private axiom suppliedRuntime : True',
      'opaque suppliedHistory : True', 'theorem fabricatedResult : True := by sorry',
      'variable (suppliedCorrectness : Prop)', 'import PNP.Main',
    ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length, file + ': ' + extra);
  }
});

test('source runtime: original input, actual checker and retained model premise cannot drift', async () => {
  for (const [name, label, before, after] of [
    ['SourceReductionRuntime', 'all source inputs', 'theorem source_halts (input : BitString)',
      'theorem source_halts (input : BitString) (onlyFixture : input = [])'],
    ['SourceReductionRuntime', 'source-derived history',
      'SourceEncoding.toData (NativeSource.reduceSystem D)', 'suppliedHistory'],
    ['SourceReductionRuntime', 'actual source checker',
      'NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input) certificate = true',
      'True'],
    ['SourceReductionRuntime', 'genuine terminal model remains a premise',
      '(model : models (NativeSource.reduceSystem D).core z = true)', '(model : True)'],
    ['SourceReductionRuntime', 'original-input physical replay bound',
      'SourceReplayEndpointBudget.nativeRuntimePolynomial.eval input.length',
      'SourceReplayEndpointBudget.nativeRuntimePolynomial.eval (SourceReplayRequest.codec.encode (recoveryRequest c D z)).length'],
    ['SourceReductionRuntime', 'unknown is not rejection',
      'NativeSource.sourceVerdict input = none', 'NativeSource.sourceVerdict input = some false'],
    ['SourceReductionRuntime', 'every raw replay request',
      'SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input)',
      'SourceReplayEndpointOutput.codec.encode (some [])'],
    ['SourceReplayEndpointGenerated', 'computed not supplied reduction',
      'SourceEncoding.toData (reduce n F)', 'suppliedHistory'],
    ['SourceReplayEndpointBudget', 'model width accounted in request',
      'request.dimension + 2 * request.data.length + 2 * request.witness.length + 4',
      'request.dimension + 2 * request.data.length + 4'],
  ]) {
    const file = base0 + name + '.lean';
    const source = await text0(file), spec = fixture0.newSources.find(row => row.file === file);
    assert.ok(spec, file);
    assert.ok(source.includes(before), 'missing mutation anchor: ' + label);
    const changed = source.replace(before, () => after);
    assert.notEqual(changed, source, label);
    assert.ok(inspect0(spec, changed).length, 'accepted mutation: ' + label);
  }
});

test('source runtime: authority guard distinguishes declarations from record fields', () => {
  assert.equal(hasAssumption0('structure Stored where\n  constant : BitString\n'), false);
  assert.equal(hasAssumption0('theorem constant_eval :\n    constant q = qEval q zero := by\n  rfl\n'), false);
  for (const source of ['axiom supplied : True', 'private axiom supplied : True',
    'constant supplied : True', 'opaque supplied : True'])
    assert.equal(hasAssumption0(source), true, source);
});
