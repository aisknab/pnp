import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen after the general contracts and exact axiom closures were kernel checked.
const SPEC = {
  "file": "lean/PNP/NANDWireProfileRestoration.lean",
  "sourceContractSha256": "96bc0a4ef5df84ee578ab239577bffff5695c53e07952b9c7a5a0fa0674dc37d",
  "heads": [
    {
      "kind": "theorem",
      "name": "quotientAgreement_iff"
    },
    {
      "kind": "theorem",
      "name": "expanded_fullEquivalent"
    },
    {
      "kind": "def",
      "name": "paidWitness"
    },
    {
      "kind": "theorem",
      "name": "paidWitness_fullEquivalent"
    },
    {
      "kind": "theorem",
      "name": "paidWitness_gateCount"
    },
    {
      "kind": "theorem",
      "name": "fullMinimum_le_quotientMinimum_add_charge"
    },
    {
      "kind": "theorem",
      "name": "projectionDefect_le_charge"
    },
    {
      "kind": "def",
      "name": "overhead"
    },
    {
      "kind": "theorem",
      "name": "paidWitness_exact_overhead"
    },
    {
      "kind": "theorem",
      "name": "paidWitness_smaller_iff"
    },
    {
      "kind": "theorem",
      "name": "paidWitness_optimal_iff"
    },
    {
      "kind": "def",
      "name": "normalizedWitness"
    },
    {
      "kind": "def",
      "name": "reclaimed"
    },
    {
      "kind": "theorem",
      "name": "normalizedWitness_fullEquivalent"
    },
    {
      "kind": "theorem",
      "name": "normalizedWitness_exact_accounting"
    },
    {
      "kind": "theorem",
      "name": "reclaimed_le_overhead"
    },
    {
      "kind": "def",
      "name": "remainingOverhead"
    },
    {
      "kind": "theorem",
      "name": "normalizedWitness_exact_overhead"
    },
    {
      "kind": "theorem",
      "name": "normalizedWitness_smaller_iff"
    },
    {
      "kind": "theorem",
      "name": "normalizedWitness_optimal_iff"
    },
    {
      "kind": "structure",
      "name": "CheckedGain"
    },
    {
      "kind": "def",
      "name": "checkedGain"
    },
    {
      "kind": "theorem",
      "name": "checkedGain_isSome_iff"
    },
    {
      "kind": "def",
      "name": "CheckedGain.strictGain"
    },
    {
      "kind": "theorem",
      "name": "CheckedGain.checked"
    },
    {
      "kind": "theorem",
      "name": "unary_fullMinimum"
    },
    {
      "kind": "theorem",
      "name": "unary_smaller_iff_fullSlack_positive"
    }
  ]
};
const AXIOM_NAMES = [
  "PNP.DirectWire.WireProfileRestoration.quotientAgreement_iff",
  "PNP.DirectWire.WireProfileRestoration.expanded_fullEquivalent",
  "PNP.DirectWire.WireProfileRestoration.paidWitness_fullEquivalent",
  "PNP.DirectWire.WireProfileRestoration.paidWitness_gateCount",
  "PNP.DirectWire.WireProfileRestoration.fullMinimum_le_quotientMinimum_add_charge",
  "PNP.DirectWire.WireProfileRestoration.projectionDefect_le_charge",
  "PNP.DirectWire.WireProfileRestoration.paidWitness_exact_overhead",
  "PNP.DirectWire.WireProfileRestoration.paidWitness_smaller_iff",
  "PNP.DirectWire.WireProfileRestoration.paidWitness_optimal_iff",
  "PNP.DirectWire.WireProfileRestoration.normalizedWitness_fullEquivalent",
  "PNP.DirectWire.WireProfileRestoration.normalizedWitness_exact_accounting",
  "PNP.DirectWire.WireProfileRestoration.reclaimed_le_overhead",
  "PNP.DirectWire.WireProfileRestoration.normalizedWitness_exact_overhead",
  "PNP.DirectWire.WireProfileRestoration.normalizedWitness_smaller_iff",
  "PNP.DirectWire.WireProfileRestoration.normalizedWitness_optimal_iff",
  "PNP.DirectWire.WireProfileRestoration.checkedGain_isSome_iff",
  "PNP.DirectWire.WireProfileRestoration.CheckedGain.checked",
  "PNP.DirectWire.WireProfileRestoration.unary_fullMinimum",
  "PNP.DirectWire.WireProfileRestoration.unary_smaller_iff_fullSlack_positive"
];
const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');

function inspect0(source) {
  const issues = [];
  if (hasLeanAssumptionDeclaration0(source)) issues.push('assumption declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) issues.push('unaudited declaration');
  if (/\b(?:sorry|admit|unsafe|native_decide)\b|decide\s+\+native/u.test(stripLeanCommentsAndStrings0(source)))
    issues.push('unchecked authority');
  const heads = explicitLeanDeclarationHeads0(source).map(({ kind, name }) => ({ kind, name }));
  if (JSON.stringify(heads) !== JSON.stringify(SPEC.heads)) issues.push('changed public interface');
  if (digest0(source) !== SPEC.sourceContractSha256) issues.push('changed reviewed contract');
  return issues;
}

async function reject0(mutations) {
  const source = await text0(SPEC.file);
  assert.deepEqual(inspect0(source), []);
  for (const [label, before, after] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor absent: ' + label);
    const changed = source.replace(before, () => after);
    assert.notEqual(changed, source, label);
    assert.ok(inspect0(changed).length > 0, 'accepted mutation: ' + label);
  }
}

test('wire-profile restoration: reviewed general source and comment-only prose', async () => {
  const source = await text0(SPEC.file);
  assert.deepEqual(inspect0(source), []);
  assert.deepEqual(inspect0(source + '\n/- explanatory prose only -/\n'), []);
});

test('wire-profile restoration: added assumptions and proof shortcuts reject', async () => {
  const source = await text0(SPEC.file);
  for (const extra of [
    'axiom suppliedMinimum : True',
    'private axiom suppliedCost : True',
    'opaque suppliedFullLift : True',
    'private theorem additionalAuthority : True := by trivial',
    'theorem assumedCompleteness : True := by sorry',
    'example : True := by trivial',
    'variable (suppliedMinimum : Nat)',
    'import PNP.Main',
  ]) assert.ok(inspect0(source + '\n' + extra + '\n').length > 0, extra);
});

test('wire-profile restoration: actual quotient witness and full field restoration remain necessary', async () => {
  await reject0([
    ['same quotient interface', 'QuotientEquivalent keep carrier offered', 'True'],
    ['actual computed quotient witness', 'WireQuotientLift.expanded carrier keep (quotientWitness carrier keep)',
      'WireQuotientLift.expanded carrier keep carrier'],
    ['all ordinary outputs', 'WireQuotientLift.expanded_output carrier keep offered agreement',
      'suppliedOutputEquality'],
    ['all field values', 'WireQuotientLift.expanded_field carrier keep offered agreement',
      'suppliedFieldEquality'],
    ['unbounded input dimensions', 'carrier offered : WireCarrier inputs outputs fields',
      'carrier offered : WireCarrier 1 outputs fields'],
  ]);
});

test('wire-profile restoration: actual materializer cost is an upper bound, not a forced equality', async () => {
  await reject0([
    ['semantic defect bound', 'projectionDefect carrier keep ≤ WireQuotientLift.charge carrier keep',
      'projectionDefect carrier keep = WireQuotientLift.charge carrier keep'],
    ['pay the full materializer', 'quotientMinimum carrier keep + WireQuotientLift.charge carrier keep',
      'quotientMinimum carrier keep'],
    ['restoration overhead', 'WireQuotientLift.charge carrier keep - projectionDefect carrier keep',
      '0'],
    ['exact paid witness cost', 'fullMinimum carrier + overhead carrier keep',
      'fullMinimum carrier'],
    ['normalization savings bounded by overhead', 'reclaimed carrier keep ≤ overhead carrier keep',
      'True'],
  ]);
});

test('wire-profile restoration: strict original gain and real normalization cannot be replaced by relative saving', async () => {
  await reject0([
    ['actual physical normalization', '(paidWitness carrier keep).normalize', 'paidWitness carrier keep'],
    ['computed reclaimed gates', '(runPhysicalNormalization (paidWitness carrier keep).exposed).trace.savedGates',
      'overhead carrier keep'],
    ['remaining cost', 'overhead carrier keep - reclaimed carrier keep', 'overhead carrier keep'],
    ['strict size test', 'if smaller : (normalizedWitness carrier keep).implementation.gateCount <',
      'if smaller : (normalizedWitness carrier keep).implementation.gateCount ≤'],
    ['original comparison target', 'smaller : (normalizedWitness carrier keep).implementation.gateCount <\n    carrier.implementation.gateCount',
      'smaller : (normalizedWitness carrier keep).implementation.gateCount <\n    (paidWitness carrier keep).implementation.gateCount'],
    ['honest acceptance criterion', 'remainingOverhead carrier keep < fullSlack carrier', '0 < fullSlack carrier'],
  ]);
});

test('wire-profile restoration: existing complete unary construction is reused at its actual scope', async () => {
  await reject0([
    ['existing unary construction', 'WireUnaryRealization.realize_minimal carrier (fullWitness carrier)',
      'suppliedMinimality carrier'],
    ['one-input scope is explicit', 'theorem unary_fullMinimum (carrier : WireCarrier 1 outputs fields)',
      'theorem unary_fullMinimum (carrier : WireCarrier inputs outputs fields)'],
    ['exact minimum identity', 'fullMinimum carrier = (WireUnaryRealization.realize carrier).implementation.gateCount',
      'fullMinimum carrier = 0'],
  ]);
});

test('wire-profile restoration: root and reviewed axiom names stay synchronized', async () => {
  const [root, audit] = await Promise.all([
    text0('lean/PNP.lean'), text0('lean-audit/PNPWireProfileRestorationAxiomAudit.lean'),
  ]);
  assert.ok(root.split('\n').includes('import PNP.NANDWireProfileRestoration'));
  assert.match(audit, /^import PNP$/mu);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]), AXIOM_NAMES);
  assert.equal(new Set(AXIOM_NAMES).size, AXIOM_NAMES.length);
});

test('wire-profile restoration: general contracts, guarded executions, and obstruction/recovery stay distinct', async () => {
  const [regression, obstruction] = await Promise.all([
    text0('lean-regression/PNPWireProfileRestoration.lean'),
    text0('lean-regression/PNPWireProfileRestorationObstruction.lean'),
  ]);
  for (const source of [regression, obstruction]) {
    assert.match(source, /^import PNP$/mu);
    assert.doesNotMatch(stripLeanCommentsAndStrings0(source),
      /\b(?:sorry|admit|unsafe|native_decide)\b|decide\s+\+native|#eval!/u);
  }
  assert.equal([...regression.matchAll(/^example\b/gmu)].length, 9);
  for (const name of ['projectionDefect_le_charge', 'paidWitness_exact_overhead',
    'reclaimed_le_overhead', 'normalizedWitness_exact_overhead', 'checkedGain_isSome_iff',
    'unary_fullMinimum', 'unary_smaller_iff_fullSlack_positive'])
    assert.ok(regression.includes(name), name);
  assert.match(regression, /if metrics != expected then\s+throw \(IO\.userError/u);
  assert.match(regression, /if \(checkedGain carrier keep\)\.isSome != gainExpected then\s+throw \(IO\.userError/u);
  for (const name of ['positive_full_slack', 'computed_restoration_refuses',
    'positive_slack_does_not_force_restoration_gain', 'existing_unary_route_recovers'])
    assert.match(obstruction, new RegExp('^theorem ' + name + '\\b', 'mu'));
});
