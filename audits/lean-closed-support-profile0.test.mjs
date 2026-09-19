import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen from successfully kernel-checked leaf sources.
// Root/inventory/publication checks are a separate integration boundary.
const SPECS = [
  {
    "file": "lean/PNP/NANDClosedSupportObservation.lean",
    "sourceContractSha256": "d459d71c08c3eb08fe3f82cde3c14f25a991dfec530094c15db824b749fbf74b",
    "heads": [
      {
        "kind": "def",
        "name": "records"
      },
      {
        "kind": "def",
        "name": "implementation"
      },
      {
        "kind": "def",
        "name": "matchingSources"
      },
      {
        "kind": "def",
        "name": "retained"
      },
      {
        "kind": "def",
        "name": "tableAvailable"
      },
      {
        "kind": "theorem",
        "name": "mem_matchingSources"
      },
      {
        "kind": "theorem",
        "name": "boundary_isInput"
      },
      {
        "kind": "theorem",
        "name": "gate_value"
      },
      {
        "kind": "theorem",
        "name": "lift_retained_source"
      },
      {
        "kind": "theorem",
        "name": "available_of_retained_source"
      },
      {
        "kind": "theorem",
        "name": "retract_support_source"
      },
      {
        "kind": "theorem",
        "name": "available_iff_retained_source"
      },
      {
        "kind": "theorem",
        "name": "tableAvailable_iff"
      },
      {
        "kind": "theorem",
        "name": "available_eq_tableAvailable"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportUnion.lean",
    "sourceContractSha256": "7f5e29074cecbe8100471aa30d4fc81148d4825a95878236db13a94d892b530d",
    "heads": [
      {
        "kind": "theorem",
        "name": "records_mono"
      },
      {
        "kind": "theorem",
        "name": "mem_records_append"
      },
      {
        "kind": "theorem",
        "name": "retained_append"
      },
      {
        "kind": "theorem",
        "name": "tableAvailable_append"
      },
      {
        "kind": "theorem",
        "name": "available_append"
      },
      {
        "kind": "theorem",
        "name": "available_flatten"
      },
      {
        "kind": "theorem",
        "name": "available_mono"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportProfile.lean",
    "sourceContractSha256": "138499adb2d5291d83018d9e8d154e6939e84278b7c54b36ca211fa1ff10e2d4",
    "heads": [
      {
        "kind": "theorem",
        "name": "profile_available"
      },
      {
        "kind": "def",
        "name": "keptFieldSeed"
      },
      {
        "kind": "def",
        "name": "projectedImplementation"
      },
      {
        "kind": "theorem",
        "name": "projected_available"
      },
      {
        "kind": "theorem",
        "name": "projected_tableAvailable"
      },
      {
        "kind": "theorem",
        "name": "projected_fieldValue"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportSquare.lean",
    "sourceContractSha256": "07b4de19ace286ee3b10b8e9d814bdf77730e9accc742a9042bff00f81168e48",
    "heads": [
      {
        "kind": "def",
        "name": "square"
      },
      {
        "kind": "def",
        "name": "cornerImplementation"
      },
      {
        "kind": "theorem",
        "name": "corner_profileMember"
      },
      {
        "kind": "theorem",
        "name": "corner_available"
      },
      {
        "kind": "theorem",
        "name": "corner_fieldValue"
      },
      {
        "kind": "theorem",
        "name": "corners_fieldValue_equal"
      }
    ]
  }
];

const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');
function inspect0(spec, source) {
  const issues = [];
  if (hasLeanAssumptionDeclaration0(source)) issues.push('assumption declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) issues.push('unaudited declaration');
  if (/\b(?:sorry|admit|unsafe|native_decide)\b|decide\s+\+native/u.test(stripLeanCommentsAndStrings0(source)))
    issues.push('unchecked authority');
  const heads = explicitLeanDeclarationHeads0(source).map(({kind, name}) => ({kind, name}));
  if (JSON.stringify(heads) !== JSON.stringify(spec.heads)) issues.push('changed public interface');
  if (digest0(source) !== spec.sourceContractSha256) issues.push('changed reviewed contract');
  return issues;
}
async function reject0(module, mutations) {
  const spec = SPECS.find(row => row.file === 'lean/PNP/' + module + '.lean');
  assert.ok(spec, module);
  const source = await text0(spec.file);
  assert.deepEqual(inspect0(spec, source), []);
  for (const [label, before, after] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor absent: ' + label);
    const changed = source.replace(before, () => after);
    assert.notEqual(changed, source, label);
    assert.ok(inspect0(spec, changed).length > 0, 'accepted mutation: ' + label);
  }
}
test('closed support sources: reviewed general interfaces and comment-only prose', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    assert.deepEqual(inspect0(spec, source), [], spec.file);
    assert.deepEqual(inspect0(spec, source + '\n/- explanatory prose only -/\n'), [], spec.file);
  }
});
test('closed support sources: supplied authority and shortcuts are rejected', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    for (const extra of [
      'axiom suppliedCompleteness : True',
      'private axiom suppliedChoice : True',
      'opaque suppliedFieldFamily : True',
      'private theorem suppliedAuthority : True := by trivial',
      'theorem assumedCompleteness : True := by sorry',
      'example : True := by trivial',
      'variable (suppliedCompatibility : Prop)',
      'import PNP.Main',
    ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length > 0, spec.file + ': ' + extra);
  }
});
test('closed support sources: the observer uses a computed closed support and uniform source table', async () => {
  await reject0('NANDClosedSupportObservation', [
    ['computed dependency closure', '(WireProfileAmbient.model target keep)', 'suppliedModel'],
    ['uniform original-source comparison',
      '(WireProfileAvailability.sourceMatches target target.implementation field)',
      '(fun _ => true)'],
    ['actual gate retention', 'terminalGateSelected (records target keep seed) gate', 'true'],
    ['source alternatives are searched', '(matchingSources target field).any (retained target keep seed)', 'true'],
    ['all target dimensions', '(target : WireCarrier inputs outputs fields)', '(target : WireCarrier 1 outputs fields)'],
  ]);
});
test('closed support sources: union and finite-family laws cannot be replaced by raw-support shortcuts', async () => {
  await reject0('NANDClosedSupportUnion', [
    ['ordinary seed inclusion remains explicit',
      '(within : ∀ record, record ∈ left → record ∈ right)',
      '(within : True)'],
    ['retained-source union is not an intersection',
      '(retained target keep left source || retained target keep right source)',
      '(retained target keep left source && retained target keep right source)'],
    ['unbounded finite family',
      '(family : List (List\n      (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)))',
      '(family : Fin 2)'],
    ['free fields survive the empty family',
      '(WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)\n          (implementation target keep []) field)',
      'false'],
    ['computed square structure is reused', 'square.mem_joinRecords_iff record', 'suppliedJoinCorrectness'],
  ]);
});
test('closed support sources: requested profiles are derived without forcing literal field gates', async () => {
  await reject0('NANDClosedSupportProfile', [
    ['profile-record seed, not literal field-gate seed',
      '((allFin fields).filter keep).map TerminalPrimitiveRecord.profile',
      'WireProfileFieldClosed.fieldGateSeed target'],
    ['requested fields retain an explicit mask guard', '(kept : keep field = true)', '(kept : True)'],
    ['existing locality applied to the actual model',
      '(WireProfileAmbient.model target keep) seed field profileMember',
      'suppliedModel seed field suppliedPreservation'],
    ['field values come from actual binding',
      '(WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)',
      '(suppliedBoundCarrier (WireProfileAmbient.ambientTarget target)'],
  ]);
});
test('closed support sources: all actual square corners share derived requested field values', async () => {
  await reject0('NANDClosedSupportSquare', [
    ['both seed families request the same fields',
      '(left ++ keptFieldSeed target keep) (right ++ keptFieldSeed target keep)',
      '(left ++ keptFieldSeed target keep) right'],
    ['actual selected corner is extracted',
      '((square target keep left right).records corner)',
      '((square target keep left right).records .left)'],
    ['meet membership is an intersection',
      '⟨seeded left, seeded right⟩', 'suppliedMeetMember'],
    ['the corner is actually closed',
      '((square target keep left right).records_closed corner)',
      'suppliedCornerClosure'],
    ['forgotten fields are not claimed preserved',
      '(field : Fin fields) (kept : keep field = true)',
      '(field : Fin fields) (kept : True)'],
  ]);
});
test('closed support sources: the checked public theorem set is fixed without declaration-count credit', async () => {
  assert.equal(SPECS.reduce((sum, spec) => sum + spec.heads.filter(row => row.kind === 'theorem').length, 0), 24);
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    assert.deepEqual(explicitLeanDeclarationHeads0(source).map(({kind, name}) => ({kind, name})),
      spec.heads, spec.file);
  }
});

test('closed support integration: root, theorem producers and combined evidence entrypoints agree', async () => {
  const [root, audit, regression, leanInventory, required] = await Promise.all([
    text0('lean/PNP.lean'),
    text0('lean-audit/PNPClosedSupportProfileSquareAxiomAudit.lean'),
    text0('lean-regression/PNPClosedSupportProfileSquare.lean'),
    text0('lean-audit/PNPTheoremInventory.lean'),
    import('../formal-publication0.mjs'),
  ]);
  const names = SPECS.flatMap(spec => {
    const module = spec.file.replace('lean/PNP/', '').replace('.lean', '');
    assert.equal(root.split('\n').filter(line => line === 'import PNP.' + module).length, 1, module);
    const namespace = 'PNP.DirectWire.' + module.replace(/^NAND/u, '');
    return spec.heads.filter(head => head.kind === 'theorem').map(head => namespace + '.' + head.name);
  }).sort();
  assert.equal(names.length, 24);
  assert.match(audit, /^import PNP\n/u);
  assert.match(regression, /^import PNP\n/u);
  assert.equal((regression.match(/^import /gmu) ?? []).length, 1);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]).sort(), names);
  const leanList = leanInventory.match(/private def reviewedMilestoneTheoremNames : Array Name := #\[([\s\S]*?)\]/mu);
  assert.ok(leanList, 'reviewed Lean theorem-list anchor');
  const leanNames = [...leanList[1].matchAll(/`([^,\s]+)/gu)].map(row => row[1]).sort();
  const jsNames = [...required.REQUIRED_MILESTONE_THEOREMS0].sort();
  assert.deepEqual(leanNames, jsNames, 'Lean inventory and publication consumers');
  assert.equal(new Set(leanNames).size, leanNames.length);
  for (const name of names) assert.ok(leanNames.includes(name), name);
  assert.equal((regression.match(/^example\b/gmu) ?? []).length, 14);
  assert.equal((regression.match(/^theorem\b/gmu) ?? []).length, 25);
  assert.equal((regression.match(/^#print axioms /gmu) ?? []).length, 25);
  assert.match(regression, /closed-support-profile-square-regressions-complete: 14 general type contracts; 25 kernel guards; 10 runtime checks/u);
  for (const guard of ['positive_full_slack', 'no_proper_seed', 'no_proper_positive_seed',
    'sharing_saves_one', 'not_normalization_quiescent', 'normalized_gateCount']) {
    assert.ok(regression.includes('#print axioms PNP.DirectWire.ClosedSupportPositiveObstruction.' + guard), guard);
  }
});
