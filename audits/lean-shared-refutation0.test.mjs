import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const fixture0 = JSON.parse(await text0('audits/fixtures/shared-refutation-source-contract0.json'));
const base0 = 'lean/PNP/Concrete/ResidualReduction/';
const sourceNames0 = [
  'Algebra', 'Assembly', 'Audit', 'Circuit', 'Contraction', 'Extraction',
  'GlobalStep', 'Regression', 'SourceLift', 'Terminal', 'Transport',
];
const newFiles0 = sourceNames0.map(name => base0 + 'SharedRefutation' + name + '.lean');
const auditFile0 = 'lean-audit/PNPSharedRefutationAxiomAudit.lean';
const endpoints0 = [
  'extract_of_false_verdict', 'extract_some_false_verdict', 'extract_contract',
  'extract_unsatisfiable', 'unwind_linked',
].map(name => 'PNP.Concrete.ResidualReduction.SharedRefutationExtraction.' + name);
const claimBoundary0 = Object.freeze({
  sourceOnlyPublicExtractor: true,
  falseExistingVerdictImpliesExtraction: true,
  returnedCertificateRefutesOriginalRows: true,
  unknownIsFalse: false,
  universalSelectorCompleteness: false,
  wholeEncodedPolynomialRuntime: false,
  efficientStandaloneCircuitIdentityChecking: false,
  checkpointEarned: false,
});
const rawDigest0 = source => createHash('sha256').update(source).digest('hex');
const digest0 = source => rawDigest0(stripLeanCommentsAndStrings0(source)
  .replace(/\s+/gu, ' ').trim());
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
function checkBoundary0(boundary) { assert.deepEqual(boundary, claimBoundary0); }
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

// This source/claim contract is neither a Lean proof nor an arbitrary-circuit
// identity checker. The separate root-context Lean audit is fail-closed.
test('shared refutation: exact reviewed sources and complete project import closure', async () => {
  assert.equal(fixture0.kind, 'PNPSharedRefutationSourceContract0');
  assert.equal(fixture0.version, 0);
  assert.deepEqual(fixture0.rootModules, ['PNP.Concrete.ResidualReduction.SharedRefutationAudit']);
  assert.deepEqual(fixture0.allowedAxioms, ['propext', 'Quot.sound']);
  assert.deepEqual(fixture0.publicEndpoints, endpoints0);
  checkBoundary0(fixture0.claimBoundary);
  assert.deepEqual(fixture0.reviewedSources.map(row => row.file), newFiles0);
  const actual = await closure0(fixture0.rootModules);
  assert.deepEqual(actual.map(row => row.file), fixture0.files.map(row => row.file));
  for (const row of actual) {
    const spec = fixture0.files.find(item => item.file === row.file);
    assert.deepEqual(inspect0(spec, row.source), [], row.file);
    assert.deepEqual(inspect0(spec, row.source + '\n/- explanatory prose only -/\n'), [], row.file);
  }
  for (const spec of fixture0.reviewedSources) {
    const source = await text0(spec.file);
    assert.equal(rawDigest0(source), spec.sha256, spec.file);
    assert.equal(Buffer.byteLength(source), spec.bytes, spec.file);
    assert.deepEqual(heads0(source), spec.declarationHeads, spec.file);
    assert.equal(hasUnauditedLeanDeclarationForm0(source), false, spec.file);
  }
  assert.deepEqual(fixture0.auxiliaryContracts.map(row => row.file), [auditFile0]);
  for (const spec of fixture0.auxiliaryContracts)
    assert.deepEqual(inspect0(spec, await text0(spec.file)), [], spec.file);
});

test('shared refutation: root context, exact typed endpoints and exhaustive axiom closure', async () => {
  const root = await text0('lean/PNP.lean'), audit = await text0(auditFile0);
  assert.equal(root.split('\n').filter(line =>
    line === 'import PNP.Concrete.ResidualReduction.SharedRefutationAudit').length, 1);
  assert.match(audit, /^import PNP\n/u);
  assert.equal((audit.match(/^example\b/gmu) ?? []).length, 8);
  for (const name of endpoints0) assert.ok(audit.includes(name.split('.').at(-1)), name);
  for (const anchor of [
    'for (name, _) in environment.constants.toList do',
    'name.toString.splitOn "PNP.Concrete.ResidualReduction.SharedRefutation"',
    'let axioms ← Lean.collectAxioms name', 'for axiomName in axioms do',
    'if axiomName != ' + String.fromCharCode(96).repeat(2) + 'propext && axiomName != ' +
      String.fromCharCode(96).repeat(2) + 'Quot.sound then',
    'if checked = 0 then', 'if rejected > 0 then',
    'SHARED_REFUTATION_ROOT_ALL_DECLARATIONS_AXIOM_OK',
  ]) assert.ok(audit.includes(anchor), anchor);
  assert.equal((audit.match(/throwError /gu) ?? []).length, 2);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(audit), /^#(?:eval|print)\b/mu);
});

test('shared refutation: source-generated replay, false verdict and row attachment cannot weaken', async () => {
  for (const [name, label, before, after] of [
    ['Extraction', 'no supplied seed', 'def extract {n : Nat} (F : Family n)',
      'def extract {n : Nat} (F : Family n) (seed : Certificate n)'],
    ['Extraction', 'no supplied history', 'def extract {n : Nat} (F : Family n)',
      'def extract {n : Nat} (F : Family n) (history : List StepRecord)'],
    ['Extraction', 'actual single reduction', 'let reduction := reduce n F',
      'let reduction := suppliedReduction'],
    ['Extraction', 'actual history', 'unwind seed n reduction.history', 'unwind seed n suppliedHistory'],
    ['Extraction', 'actual terminal source', 'terminal reduction.dimension reduction.core',
      'terminal reduction.dimension suppliedCore'],
    ['Extraction', 'linked replay premise', '(linked : Linked F history G)', '(linked : True)'],
    ['Extraction', 'replay seed refutation premise', '(refutation : Refutes G seed)', '(refutation : True)'],
    ['Extraction', 'false existing verdict', '(falseVerdict : verdict F = some false)', '(falseVerdict : True)'],
    ['Extraction', 'unknown is not false', '| _ + 1, _ => none', '| _ + 1, _ => suppliedCertificate'],
    ['Extraction', 'returned certificate premise', '(accepted : extract F = some q)', '(accepted : True)'],
    ['Extraction', 'gate count tied to source dimensions', '2 + (4 * F.length + 1) * n', '2 + n'],
    ['Assembly', 'chronological gate validity', 'codeValid p.1 = true', 'True'],
    ['Assembly', 'root bounds', '(∀ i ∈ p.2, i < p.1.length)', 'True'],
    ['Assembly', 'one root per original row', 'p.2.length = F.length', 'True'],
    ['Assembly', 'every source point', '∀ x, SharedRefutationSourceLift.pairedSum',
      '∀ x, models F x = true → SharedRefutationSourceLift.pairedSum'],
    ['Assembly', 'original rows retained', '(F.map (fun r => r.eval x))',
      '((F.take 1).map (fun r => r.eval x))'],
    ['Assembly', 'attachment rejects length mismatch', '| _, _ => none', '| _, _ => some []'],
    ['Terminal', 'first violated row only', '1 :: rows.map (fun _ => 0)', '1 :: roots rows'],
    ['Terminal', 'all row positions retained', '(roots rows).length = rows.length', '(roots rows).length ≤ rows.length'],
    ['SourceLift', 'quadratic tail retained', '(tail : Quadratic n)', '(tail : Affine n)'],
  ]) {
    const file = base0 + 'SharedRefutation' + name + '.lean';
    const source = await text0(file), spec = fixture0.files.find(row => row.file === file);
    assert.ok(source.includes(before), 'missing mutation anchor: ' + label);
    const changed = source.replace(before, () => after);
    assert.notEqual(changed, source, label);
    assert.ok(inspect0(spec, changed).length, 'accepted mutation: ' + label);
  }
});

test('shared refutation: missing inputs and malformed references have retained regressions', async () => {
  const source = await text0(base0 + 'SharedRefutationRegression.lean');
  const names = heads0(source).filter(row => row.kind === 'theorem').map(row => row.name);
  for (const name of [
    'invalid_forward_reference', 'invalid_input_root', 'wrong_source_guard_rejected',
    'source_root_out_of_range_rejected', 'missing_coefficient_rejected',
    'missing_source_value_rejected', 'valid_guard_does_not_invent_refutation',
    'nonlinear_source_refutation', 'terminal_selects_only_first_violation',
    'terminal_even_violations_still_refute', 'attachment_missing_root_rejected',
    'attachment_extra_root_rejected', 'empty_history_wrong_dimension_rejected',
    'source_history_extracts', 'source_history_refutes_every_input',
    'source_history_growth_bound', 'positive_dimension_unknown_not_refuted',
    'satisfiable_terminal_not_refuted',
  ]) assert.ok(names.includes(name), name);
});

test('shared refutation: source assumptions and unchecked authority reject', async () => {
  for (const file of newFiles0) {
    const source = await text0(file), spec = fixture0.files.find(row => row.file === file);
    for (const extra of [
      'axiom suppliedIdentity : True', 'private axiom suppliedCompleteness : True',
      'opaque suppliedRuntime : True', 'theorem fabricated : True := by sorry',
      'variable (suppliedHistoryCorrect : Prop)', 'import PNP.Main',
    ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length, file + ': ' + extra);
  }
});

test('shared refutation: strict audit cannot become a print-only or permissive audit', async () => {
  const source = await text0(auditFile0), spec = fixture0.auxiliaryContracts[0];
  for (const [before, after] of [
    ['import PNP\n', 'import PNP.Concrete.ResidualReduction.SharedRefutationExtraction\n'],
    ['environment.constants.toList', '[]'],
    ['let axioms ← Lean.collectAxioms name', 'let axioms := #[]'],
    ['if rejected > 0 then', 'if false then'],
    ['if checked = 0 then', 'if false then'],
    ['(falseVerdict : verdict F = some false)', '(falseVerdict : True)'],
    ['(accepted : extract F = some q)', '(accepted : True)'],
    ['q.1.length ≤ 2 + (4 * F.length + 1) * n', 'True'],
  ]) {
    assert.ok(source.includes(before), before);
    assert.ok(inspect0(spec, source.replace(before, () => after)).length, before);
  }
  assert.ok(inspect0(spec, source + '\naxiom suppliedAuditAuthority : True\n').length);
});

test('shared refutation: compact gates do not assert universal discovery, runtime or identity checking', () => {
  checkBoundary0(fixture0.claimBoundary);
  for (const [key, value] of Object.entries(claimBoundary0))
    assert.throws(() => checkBoundary0({...fixture0.claimBoundary, [key]: !value}), key);
});
