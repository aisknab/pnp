import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen from independently compiled and assumption-audited source.
// Do not regenerate the reviewed contract during tests.
const SPECS = [
  {
    "file": "lean/PNP/NANDClosedSupportNestedCandidate.lean",
    "namespace": "PNP.DirectWire.ClosedSupportNestedGain",
    "sourceContractSha256": "9c69f27277c2b4f6f614bb3ce796c55f7f032d90365213fa7b46e218b13a96b1",
    "heads": [
      {
        "kind": "def",
        "name": "outputSource"
      },
      {
        "kind": "theorem",
        "name": "ambient_output_absent"
      },
      {
        "kind": "theorem",
        "name": "outputSource_value"
      },
      {
        "kind": "def",
        "name": "extendedImplementation"
      },
      {
        "kind": "theorem",
        "name": "extended_gateCount"
      },
      {
        "kind": "def",
        "name": "extendRealization"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportNestedCost.lean",
    "namespace": "PNP.DirectWire.ClosedSupportNestedGain",
    "sourceContractSha256": "bebbaaf1e591b0542fd81a2027e385218bad5b06b3dc89bf75fc45e47bb13218",
    "heads": [
      {
        "kind": "theorem",
        "name": "full_minimum_extension_bound"
      },
      {
        "kind": "theorem",
        "name": "quotient_minimum_extension_bound"
      },
      {
        "kind": "theorem",
        "name": "full_minimum_cost_balance"
      },
      {
        "kind": "theorem",
        "name": "quotient_minimum_cost_balance"
      },
      {
        "kind": "theorem",
        "name": "full_slack_le"
      },
      {
        "kind": "theorem",
        "name": "quotient_slack_le"
      },
      {
        "kind": "theorem",
        "name": "full_minimum_le_support"
      },
      {
        "kind": "theorem",
        "name": "quotient_minimum_le_full"
      },
      {
        "kind": "theorem",
        "name": "slack_decomposition"
      },
      {
        "kind": "theorem",
        "name": "positive_iff_quotient_slack"
      },
      {
        "kind": "theorem",
        "name": "positive_mono"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportNestedGain.lean",
    "namespace": "PNP.DirectWire.ClosedSupportNestedGain",
    "sourceContractSha256": "687627d179945a674b77a4b1dc29a07269df047760038ff3c4d73f8b5cc4df96",
    "heads": [
      {
        "kind": "theorem",
        "name": "included_of_seed_subset"
      },
      {
        "kind": "theorem",
        "name": "seed_full_cost_balance"
      },
      {
        "kind": "theorem",
        "name": "seed_quotient_cost_balance"
      },
      {
        "kind": "theorem",
        "name": "seed_full_slack_le"
      },
      {
        "kind": "theorem",
        "name": "seed_positive"
      },
      {
        "kind": "theorem",
        "name": "append_positive"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportNestedOrigin.lean",
    "namespace": "PNP.DirectWire.ClosedSupportNestedGain",
    "sourceContractSha256": "5f590f01c4ab80035511f38896cf83541e4f9ca10431cabc225e4480d704ee4e",
    "heads": [
      {
        "kind": "theorem",
        "name": "extended_source_origin"
      },
      {
        "kind": "theorem",
        "name": "available_from_prefix"
      },
      {
        "kind": "theorem",
        "name": "available_to_large"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportNestedProfile.lean",
    "namespace": "PNP.DirectWire.ClosedSupportNestedGain",
    "sourceContractSha256": "17b71570d90687deaa7e898801399d0922bc975fc23b81920806b9e6248d91e2",
    "heads": [
      {
        "kind": "theorem",
        "name": "available_from_large"
      },
      {
        "kind": "theorem",
        "name": "extended_available"
      },
      {
        "kind": "def",
        "name": "extendFullComparison"
      },
      {
        "kind": "def",
        "name": "extendQuotientComparison"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportNestedProgram.lean",
    "namespace": "PNP.DirectWire.ClosedSupportNestedGain",
    "sourceContractSha256": "9b7937e0f194fcd0fbe467e3479d246275c7e7d6aedcf449395ceb8b6861cb77",
    "heads": [
      {
        "kind": "def",
        "name": "boundarySource"
      },
      {
        "kind": "theorem",
        "name": "boundarySource_value"
      },
      {
        "kind": "def",
        "name": "boundaryBinding"
      },
      {
        "kind": "def",
        "name": "program"
      },
      {
        "kind": "theorem",
        "name": "difference_gate_value"
      },
      {
        "kind": "theorem",
        "name": "prefix_source_value"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportNestedSelection.lean",
    "namespace": "PNP.DirectWire.ClosedSupportNestedGain",
    "sourceContractSha256": "7fe215323178dd569f1af5d08dfabcfa1267626ca0a64c76164b7dc85eb963e2",
    "heads": [
      {
        "kind": "abbrev",
        "name": "Seed"
      },
      {
        "kind": "def",
        "name": "Included"
      },
      {
        "kind": "def",
        "name": "snapshot"
      },
      {
        "kind": "def",
        "name": "differenceRecords"
      },
      {
        "kind": "def",
        "name": "difference"
      },
      {
        "kind": "theorem",
        "name": "difference_selected"
      },
      {
        "kind": "theorem",
        "name": "difference_selected_iff"
      },
      {
        "kind": "theorem",
        "name": "support_count_decomposition"
      },
      {
        "kind": "theorem",
        "name": "support_size_le"
      },
      {
        "kind": "theorem",
        "name": "retained_mono"
      },
      {
        "kind": "theorem",
        "name": "available_mono"
      },
      {
        "kind": "theorem",
        "name": "difference_boundary_interface"
      },
      {
        "kind": "theorem",
        "name": "larger_interface_in_smaller"
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

test('nested support sources: reviewed general interfaces and comment-only prose', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    assert.deepEqual(inspect0(spec, source), [], spec.file);
    assert.deepEqual(inspect0(spec, source + '\n/- explanatory prose only -/\n'), [], spec.file);
  }
});
test('nested support sources: supplied authority and unchecked shortcuts reject', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    for (const extra of [
      'axiom suppliedMinimum : True', 'private axiom suppliedBalance : True',
      'opaque suppliedProfile : True', 'private theorem suppliedAuthority : True := by trivial',
      'theorem assumedCorrectness : True := by sorry', 'example : True := by trivial',
      'variable (suppliedCompatibility : Prop)', 'import PNP.Main',
    ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length > 0, spec.file + ': ' + extra);
  }
});
test('nested support sources: actual closed selections and physical inclusion are required', async () => {
  await reject0('NANDClosedSupportNestedSelection', [
    ['computed closure', 'ClosedSupportObservation.records target keep large', 'large'],
    ['arbitrary dimensions', '(target : WireCarrier inputs outputs fields)', '(target : WireCarrier 1 outputs fields)'],
    ['physical inclusion', '(included : Included target keep small large)', '(included : True)'],
    ['physical count', '(snapshot target keep small).supportSize + (difference target keep small large).gateCount', '(snapshot target keep small).supportSize'],
  ]);
});
test('nested support sources: ambient inputs and actual ordinary connections are preserved', async () => {
  await reject0('NANDClosedSupportNestedProgram', [
    ['primary input binding', '| .input input => .input (Fin.castAdd target.implementation.gateCount input)', '| .input input => .constant false'],
    ['actual prefix output', 'prefixImpl.candidate.directWireWord.source producer', 'Source.constant false'],
    ['difference rather than whole target', '(difference target keep small large).extractedCandidate.program', 'target.implementation.candidate.program'],
  ]);
  await reject0('NANDClosedSupportNestedCandidate', [
    ['false padded output', 'else .constant false', 'else .constant true'],
    ['smaller interface proof', 'larger_interface_in_smaller target keep small large included', 'suppliedInterface'],
    ['all ambient valuations', '(valuation : Valuation (inputs + target.implementation.gateCount))', '(valuation : Valuation inputs)'],
  ]);
});
test('nested support sources: field observations include false as well as true values', async () => {
  await reject0('NANDClosedSupportNestedOrigin', [
    ['actual extracted gate origin', 'terminalExtractionOrigin target.implementation.candidate', 'suppliedGateOrigin'],
    ['exact smaller observation', 'fieldEqual.symm.trans priorPresent', 'priorPresent'],
  ]);
  await reject0('NANDClosedSupportNestedProfile', [
    ['both directions of availability', 'bool_eq_of_true_iff _ _', 'suppliedAvailabilityEquality'],
    ['actual retained matching source', 'ClosedSupportObservation.available_iff_retained_source target keep large field', 'suppliedFieldTable'],
    ['full comparison', 'profileEqual := fun field =>', 'profileEqual := fun field => suppliedProfile'],
  ]);
});
test('nested support sources: actual minima and completed-support positivity cannot be weakened', async () => {
  await reject0('NANDClosedSupportNestedCost', [
    ['computed full minimum', 'let full := terminalFullProfileMinimumRealization', 'let full := suppliedFullMinimum'],
    ['computed quotient minimum', 'let comparison := terminalQuotientProfileMinimumComparison', 'let comparison := suppliedQuotientMinimum'],
    ['exact physical partition', 'support_count_decomposition target keep small large included', 'suppliedPhysicalCost'],
    ['full-or-projection positivity', '0 < (snapshot target keep large).projectionDefect', 'True'],
  ]);
  await reject0('NANDClosedSupportNestedGain', [
    ['raw seed inclusion', '(within : ∀ record, record ∈ small → record ∈ large)', '(within : True)'],
    ['derived saturation inclusion', 'terminalSaturate_monotone system', 'suppliedClosureInclusion'],
    ['completed smaller snapshot', '(snapshot target keep small).fullSlack', 'suppliedRawSlack'],
  ]);
});
test('nested support sources: reviewed theorem names are fixed, not progress credit', async () => {
  assert.equal(SPECS.reduce((sum, spec) =>
    sum + spec.heads.filter(row => row.kind === 'theorem').length, 0), 36);
  for (const spec of SPECS) assert.deepEqual(explicitLeanDeclarationHeads0(await text0(spec.file))
    .map(({kind, name}) => ({kind, name})), spec.heads);
});
test('nested support integration: root, audit, both name producers and map keys agree before export', async () => {
  const [root, audit, regression, leanInventory, mapText, required] = await Promise.all([
    text0('lean/PNP.lean'), text0('lean-audit/PNPClosedSupportNestedGainAxiomAudit.lean'),
    text0('lean-regression/PNPClosedSupportNestedGain.lean'), text0('lean-audit/PNPTheoremInventory.lean'),
    text0('publication/FORMAL_PUBLICATION_MAP.json'), import('../formal-publication0.mjs'),
  ]);
  const names = SPECS.flatMap(spec => {
    const module = spec.file.replace('lean/PNP/', '').replace('.lean', '');
    assert.equal(root.split('\n').filter(line => line === 'import PNP.' + module).length, 1, module);
    return spec.heads.filter(head => head.kind === 'theorem').map(head => spec.namespace + '.' + head.name);
  }).sort();
  assert.equal(names.length, 36);
  assert.match(audit, /^import PNP\n/u);
  assert.match(regression, /^import PNP\n/u);
  assert.equal((regression.match(/^import /gmu) ?? []).length, 1);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]).sort(), names);
  const leanList = leanInventory.match(/private def reviewedMilestoneTheoremNames : Array Name := #\[([\s\S]*?)\]/mu);
  assert.ok(leanList);
  const leanNames = [...leanList[1].matchAll(/\x60([^,\s]+)/gu)].map(row => row[1]).sort();
  assert.deepEqual(leanNames, [...required.REQUIRED_MILESTONE_THEOREMS0].sort());
  assert.equal(new Set(leanNames).size, leanNames.length);
  const map = JSON.parse(mapText);
  assert.deepEqual(Object.keys(map.earnedMilestoneTheoremKernelTypeSha256).sort(), leanNames);
  assert.deepEqual(map.milestones.find(row => row.id === 'computed-closed-support-nested-positivity').requiredTheorems, names);
  for (const name of names) assert.ok(leanNames.includes(name), name);
});
test('nested support integration: guards preserve the exact claim boundary', async () => {
  const regression = await text0('lean-regression/PNPClosedSupportNestedGain.lean');
  assert.equal((regression.match(/^example\b/gmu) ?? []).length, 8);
  assert.equal((regression.match(/^theorem\b/gmu) ?? []).length, 6);
  assert.equal((regression.match(/^#print axioms /gmu) ?? []).length, 6);
  assert.match(regression, /closed-support-nested-gain-regressions-complete: 8 general type contracts; 6 kernel guards; 11 runtime checks/u);
  for (const guard of ['hidden_field_nonconstant', 'ambient_field_unavailable',
    'fixing_unused_input_changes_field', 'ambient_observation_is_not_specialization',
    'reverse_inclusion_rejected', 'crossing_wire_has_real_effect'])
    assert.ok(regression.includes('#print axioms PNP.DirectWire.ClosedSupportNestedGainRegression.' + guard), guard);
  for (const boundary of ['projection-only positivity is not mislabeled full slack',
    'proper nesting reconnects a real crossing wire and retains strict improvement',
    'empty-to-whole construction obtains a hidden field from the difference',
    'duplicate seed records do not duplicate physical difference gates',
    'unchanged ambient inputs preserve false availability'])
    assert.ok(regression.includes(boundary), boundary);
});
