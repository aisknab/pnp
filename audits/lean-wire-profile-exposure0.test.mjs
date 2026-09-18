import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen source contracts complement, but do not replace, kernel and compiled-inventory checks.
const SPEC = {
  "file": "lean/PNP/NANDWireProfileExposure.lean",
  "sourceContractSha256": "b6b314a7cb82c581e87261265622078ca4b0a4183f689605717a282fd4626b18",
  "heads": [
    {
      "kind": "def",
      "name": "mask"
    },
    {
      "kind": "theorem",
      "name": "mask_implementation"
    },
    {
      "kind": "theorem",
      "name": "mask_fieldValue"
    },
    {
      "kind": "def",
      "name": "FullEquivalent"
    },
    {
      "kind": "def",
      "name": "QuotientEquivalent"
    },
    {
      "kind": "theorem",
      "name": "full_iff"
    },
    {
      "kind": "theorem",
      "name": "quotient_iff"
    },
    {
      "kind": "theorem",
      "name": "full_to_quotient"
    },
    {
      "kind": "theorem",
      "name": "full_lift_iff"
    },
    {
      "kind": "def",
      "name": "fullMinimum"
    },
    {
      "kind": "def",
      "name": "quotientMinimum"
    },
    {
      "kind": "def",
      "name": "fullWitness"
    },
    {
      "kind": "theorem",
      "name": "fullWitness_gateCount"
    },
    {
      "kind": "theorem",
      "name": "fullWitness_matches"
    },
    {
      "kind": "theorem",
      "name": "fullMinimum_le_physical"
    },
    {
      "kind": "theorem",
      "name": "quotientMinimum_le_full"
    },
    {
      "kind": "def",
      "name": "quotientWitness"
    },
    {
      "kind": "theorem",
      "name": "quotientWitness_gateCount"
    },
    {
      "kind": "theorem",
      "name": "quotientWitness_matches"
    },
    {
      "kind": "theorem",
      "name": "quotient_candidate_lower_bound"
    },
    {
      "kind": "theorem",
      "name": "full_candidate_lower_bound"
    },
    {
      "kind": "def",
      "name": "fullSlack"
    },
    {
      "kind": "def",
      "name": "projectionDefect"
    },
    {
      "kind": "theorem",
      "name": "fullSlack_add_projectionDefect"
    },
    {
      "kind": "theorem",
      "name": "exposure_balance"
    },
    {
      "kind": "theorem",
      "name": "exposure_preserves_positive_alternative"
    },
    {
      "kind": "theorem",
      "name": "quotient_minimum_cannot_lift_of_positive_defect"
    },
    {
      "kind": "theorem",
      "name": "exposure_loss_has_unliftable_quotient_witness"
    },
    {
      "kind": "def",
      "name": "allGateFields"
    },
    {
      "kind": "theorem",
      "name": "allGateFields_value"
    },
    {
      "kind": "theorem",
      "name": "allGateFields_positive_alternative"
    },
    {
      "kind": "theorem",
      "name": "quotientMinimum_forget_all"
    },
    {
      "kind": "theorem",
      "name": "source_slack_balance"
    },
    {
      "kind": "theorem",
      "name": "source_positive_alternative"
    },
    {
      "kind": "theorem",
      "name": "mask_absorb_equivalent"
    },
    {
      "kind": "theorem",
      "name": "quotientMinimum_mask_active"
    },
    {
      "kind": "theorem",
      "name": "fullMinimum_mask_mono"
    },
    {
      "kind": "theorem",
      "name": "exposure_states_balance"
    },
    {
      "kind": "theorem",
      "name": "exposure_moves_exact_slack_to_defect"
    },
    {
      "kind": "theorem",
      "name": "normalize_fullEquivalent"
    },
    {
      "kind": "theorem",
      "name": "fullMinimum_normalize"
    },
    {
      "kind": "theorem",
      "name": "quotientMinimum_normalize"
    },
    {
      "kind": "theorem",
      "name": "splice_fullEquivalent"
    },
    {
      "kind": "theorem",
      "name": "fullMinimum_splice"
    },
    {
      "kind": "theorem",
      "name": "quotientMinimum_splice"
    }
  ]
};
const AXIOM_NAMES = [
  "PNP.DirectWire.WireProfile.mask_implementation",
  "PNP.DirectWire.WireProfile.mask_fieldValue",
  "PNP.DirectWire.WireProfile.full_iff",
  "PNP.DirectWire.WireProfile.quotient_iff",
  "PNP.DirectWire.WireProfile.full_to_quotient",
  "PNP.DirectWire.WireProfile.full_lift_iff",
  "PNP.DirectWire.WireProfile.fullWitness_gateCount",
  "PNP.DirectWire.WireProfile.fullWitness_matches",
  "PNP.DirectWire.WireProfile.fullMinimum_le_physical",
  "PNP.DirectWire.WireProfile.quotientMinimum_le_full",
  "PNP.DirectWire.WireProfile.quotientWitness_gateCount",
  "PNP.DirectWire.WireProfile.quotientWitness_matches",
  "PNP.DirectWire.WireProfile.quotient_candidate_lower_bound",
  "PNP.DirectWire.WireProfile.full_candidate_lower_bound",
  "PNP.DirectWire.WireProfile.fullSlack_add_projectionDefect",
  "PNP.DirectWire.WireProfile.exposure_balance",
  "PNP.DirectWire.WireProfile.exposure_preserves_positive_alternative",
  "PNP.DirectWire.WireProfile.quotient_minimum_cannot_lift_of_positive_defect",
  "PNP.DirectWire.WireProfile.exposure_loss_has_unliftable_quotient_witness",
  "PNP.DirectWire.WireProfile.allGateFields_value",
  "PNP.DirectWire.WireProfile.allGateFields_positive_alternative",
  "PNP.DirectWire.WireProfile.quotientMinimum_forget_all",
  "PNP.DirectWire.WireProfile.source_slack_balance",
  "PNP.DirectWire.WireProfile.source_positive_alternative",
  "PNP.DirectWire.WireProfile.mask_absorb_equivalent",
  "PNP.DirectWire.WireProfile.quotientMinimum_mask_active",
  "PNP.DirectWire.WireProfile.fullMinimum_mask_mono",
  "PNP.DirectWire.WireProfile.exposure_states_balance",
  "PNP.DirectWire.WireProfile.exposure_moves_exact_slack_to_defect",
  "PNP.DirectWire.WireProfile.normalize_fullEquivalent",
  "PNP.DirectWire.WireProfile.fullMinimum_normalize",
  "PNP.DirectWire.WireProfile.quotientMinimum_normalize",
  "PNP.DirectWire.WireProfile.splice_fullEquivalent",
  "PNP.DirectWire.WireProfile.fullMinimum_splice",
  "PNP.DirectWire.WireProfile.quotientMinimum_splice"
];

const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');

function inspect0(source) {
  const issues = [];
  if (hasLeanAssumptionDeclaration0(source)) issues.push('assumption declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) issues.push('unaudited declaration');
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:sorry|admit|unsafe|native_decide)\b|decide\s+\+native/u.test(stripped))
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

function definition0(source, name) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const heads = [...stripped.matchAll(/^(?:private )?(?:def|theorem|structure|inductive) ([^\s(:]+)/gmu)];
  const index = heads.findIndex(head => head[1] === name);
  assert.notEqual(index, -1, 'missing definition: ' + name);
  assert.match(heads[index][0], /^(?:private )?def /u, name);
  return stripped.slice(heads[index].index, heads[index + 1]?.index ?? stripped.length);
}

test('wire-profile exposure: general source retains the reviewed contract', async () => {
  const source = await text0(SPEC.file);
  assert.deepEqual(inspect0(source), []);
  assert.deepEqual(inspect0(source + '\n/- explanatory prose only -/\n'), []);
});

test('wire-profile exposure: assumptions and hidden proof shortcuts reject', async () => {
  const source = await text0(SPEC.file);
  for (const extra of [
    'axiom suppliedMinimum : True',
    'private axiom suppliedProfile : True',
    'opaque suppliedRoute : True',
    'private theorem extraAuthority : True := by trivial',
    'theorem extraAuthority : True := by sorry',
    'example : True := by trivial',
    'variable (suppliedObserver : Nat)',
    'import PNP.Main',
  ]) assert.ok(inspect0(source + '\n' + extra + '\n').length > 0, extra);
});

test('wire-profile exposure: ordinary outputs and full restoration are mandatory', async () => {
  await reject0([
    ['same physical implementation', 'implementation := carrier.implementation',
      'implementation := suppliedImplementation'],
    ['literal forgotten slot', 'else .constant false', 'else carrier.source field'],
    ['full observation includes ordinary outputs',
      'Equivalent offered.exposed.candidate.program', 'True ∨ Equivalent offered.exposed.candidate.program'],
    ['complete forgotten-field restoration',
      'QuotientEquivalent keep target offered ∧', 'QuotientEquivalent keep target offered ∨'],
    ['all dimensions', 'keep : Fin fields → Bool', 'keep : Fin 1 → Bool'],
  ]);
});

test('wire-profile exposure: semantic minima and attained witnesses cannot become size assertions', async () => {
  await reject0([
    ['semantic full minimum', 'referenceMinimum carrier.exposed', 'carrier.implementation.gateCount'],
    ['semantic quotient minimum', 'referenceMinimum (mask carrier keep).exposed',
      '(mask carrier keep).implementation.gateCount'],
    ['attained full witness', 'WireCarrier.unpack (referenceMinimumImplementation carrier.exposed)',
      'carrier'],
    ['actual lower bound', 'quotientMinimum carrier keep ≤ offered.implementation.gateCount',
      'quotientMinimum carrier keep ≤ carrier.implementation.gateCount'],
  ]);
  const source = await text0(SPEC.file);
  for (const name of ['mask', 'allGateFields'])
    assert.doesNotMatch(definition0(source, name),
      /\b(?:referenceMinimum|referenceMinimumImplementation|allCandidates|allPrograms|allBoolTuples|equivalentBool)\b/u,
      name);
  assert.match(definition0(source, 'fullWitness'), /referenceMinimumImplementation/u);
});

test('wire-profile exposure: exact two-measure accounting and non-liftability remain checked', async () => {
  await reject0([
    ['exact combined balance', 'fullSlack carrier + projectionDefect carrier keep',
      'fullSlack carrier'],
    ['actual full-cost change',
      'fullMinimum (mask carrier after) - fullMinimum (mask carrier before)', '0'],
    ['quotient minimum is not automatically usable',
      '¬ FullEquivalent carrier (quotientWitness carrier keep)', 'True'],
    ['kept constraints remain active',
      'keep field = true → active field = true', 'True'],
  ]);
});

test('wire-profile exposure: checked transformations retain their real admission premises', async () => {
  await reject0([
    ['complete normalization equality', 'FullEquivalent carrier carrier.normalize', 'True'],
    ['checked open replacement',
      'sameOpen : replacement.semantics =', 'sameOpen : suppliedSemantics ='],
    ['actual compiler result',
      'accepted : carrier.splice records replacement = some result', 'accepted : True'],
    ['Lean section retains the checked premises',
      'include records replacement sameOpen accepted', 'include records replacement sameOpen'],
    ['exact quotient minimum after splice',
      'quotientMinimum result keep = quotientMinimum carrier keep', 'True'],
  ]);
});

test('wire-profile exposure: exact root import and audit name set are prepared together', async () => {
  const [root, audit] = await Promise.all([
    text0('lean/PNP.lean'), text0('lean-audit/PNPWireProfileExposureAxiomAudit.lean'),
  ]);
  assert.ok(root.split('\n').includes('import PNP.NANDWireProfileExposure'));
  assert.match(audit, /^import PNP$/mu);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]), AXIOM_NAMES);
  assert.equal(new Set(AXIOM_NAMES).size, AXIOM_NAMES.length);
});

test('wire-profile exposure: regressions preserve general types and the mode firewall', async () => {
  const regression = await text0('lean-regression/PNPWireProfileExposure.lean');
  assert.match(regression, /^import PNP$/mu);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|unsafe|native_decide)\b|decide\s+\+native|#eval!/u);
  for (const name of [
    'full_iff', 'full_lift_iff', 'quotientMinimum_le_full', 'quotientWitness_matches',
    'exposure_moves_exact_slack_to_defect', 'normalize_fullEquivalent',
    'splice_fullEquivalent', 'fullMinimum_splice', 'quotientMinimum_splice',
    'hidden_values_record_exact_transfer', 'forgotten_field_permits_quotient_comparison',
    'forgotten_field_does_not_permit_full_use', 'retained_field_rejects_wrong_value',
    'ordinary_output_cannot_be_forgotten', 'empty_dimensions_have_zero_minimum',
  ]) assert.ok(regression.includes(name), name);
});
