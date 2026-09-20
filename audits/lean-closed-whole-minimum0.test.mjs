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
    "file": "lean/PNP/NANDClosedWholeMinimumPrefix.lean",
    "namespace": "PNP.DirectWire.ClosedWholeMinimum",
    "sourceContractSha256": "ef4c022f6642106c73bb8196359c18ab62096c7730f3454ad1bfdce48cac84b7",
    "heads": [
      {
        "kind": "def",
        "name": "seed"
      },
      {
        "kind": "def",
        "name": "records"
      },
      {
        "kind": "def",
        "name": "snapshot"
      },
      {
        "kind": "theorem",
        "name": "gate_selected"
      },
      {
        "kind": "theorem",
        "name": "source_retained"
      },
      {
        "kind": "theorem",
        "name": "available_all"
      },
      {
        "kind": "theorem",
        "name": "support_gateCount"
      },
      {
        "kind": "theorem",
        "name": "result_gateCount"
      },
      {
        "kind": "theorem",
        "name": "global_minimum_le"
      },
      {
        "kind": "theorem",
        "name": "interface_iff_output"
      },
      {
        "kind": "def",
        "name": "outputIndex"
      },
      {
        "kind": "theorem",
        "name": "outputIndex_sound"
      },
      {
        "kind": "theorem",
        "name": "outputIndex_exists"
      },
      {
        "kind": "theorem",
        "name": "outputIndex_none_not_interface"
      },
      {
        "kind": "theorem",
        "name": "ambient_output_absent"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedWholeMinimum.lean",
    "namespace": "PNP.DirectWire.ClosedWholeMinimum",
    "sourceContractSha256": "f3286858d80b1f852bac6dc69be18e37b4ebd9a5408e41d01cb7e12e6bfe556f",
    "heads": [
      {
        "kind": "def",
        "name": "forwardSource"
      },
      {
        "kind": "def",
        "name": "forward"
      },
      {
        "kind": "theorem",
        "name": "forward_gateCount"
      },
      {
        "kind": "theorem",
        "name": "forward_output_some"
      },
      {
        "kind": "theorem",
        "name": "forward_output_none"
      },
      {
        "kind": "theorem",
        "name": "forward_equivalent"
      },
      {
        "kind": "theorem",
        "name": "forward_available"
      },
      {
        "kind": "def",
        "name": "fullComparison"
      },
      {
        "kind": "theorem",
        "name": "support_minimum_le"
      },
      {
        "kind": "theorem",
        "name": "full_minimum"
      },
      {
        "kind": "theorem",
        "name": "result_optimal"
      },
      {
        "kind": "theorem",
        "name": "fullSlack_eq"
      },
      {
        "kind": "theorem",
        "name": "result_zero_fullSlack"
      },
      {
        "kind": "theorem",
        "name": "improvement_none_iff"
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
test('whole minimum sources: reviewed general interfaces and comment-only prose', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    assert.deepEqual(inspect0(spec, source), [], spec.file);
    assert.deepEqual(inspect0(spec, source + '\n/- explanatory prose only -/\n'), [], spec.file);
  }
});
test('whole minimum sources: supplied authority and unchecked shortcuts reject', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    for (const extra of [
      'axiom suppliedMinimum : True', 'private axiom suppliedEquality : True',
      'opaque suppliedReplacement : True', 'private theorem suppliedAuthority : True := by trivial',
      'theorem assumedCorrectness : True := by sorry', 'example : True := by trivial',
      'variable (suppliedCompatibility : Prop)', 'import PNP.Main',
    ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length > 0, spec.file + ': ' + extra);
  }
});
test('whole minimum sources: every real gate and the actual ordinary interface are derived', async () => {
  await reject0('NANDClosedWholeMinimumPrefix', [
    ['whole physical seed', '(allFin target.implementation.gateCount).map TerminalPrimitiveRecord.gate', '[]'],
    ['arbitrary dimensions', '(target : WireCarrier inputs outputs fields)', '(target : WireCarrier 1 outputs fields)'],
    ['computed field availability', 'ClosedSupportObservation.available_of_retained_source', 'suppliedAvailability'],
    ['actual output source', 'target.implementation.candidate.directWireWord.source output = .gate producer', 'True'],
    ['all sources survive whole selection', 'ClosedSupportObservation.retained target keep (seed target) source = true', 'True'],
  ]);
});
test('whole minimum sources: two genuine comparisons and full rather than quotient optimality', async () => {
  await reject0('NANDClosedWholeMinimum', [
    ['output reconstruction', '(offered.implementation.candidate.directWireWord.source output).renameInputs', '(Source.constant false).renameInputs'],
    ['full-field comparison', 'WireProfile.FullEquivalent target offered', 'WireProfile.QuotientEquivalent (fun _ => false) target offered'],
    ['independent minimum', 'WireProfile.fullMinimum target', 'WireProfile.quotientMinimum target keep'],
    ['both inequalities', 'Nat.le_antisymm (support_minimum_le target keep) (global_minimum_le target keep)', 'suppliedMinimumEquality'],
    ['actual computed replacement', '(ClosedSupportFullGain.result target keep (seed target)).implementation.gateCount', 'suppliedOptimalGateCount'],
    ['whole-span no-gain boundary', 'ClosedSupportFullGain.improvement? target keep (seed target) = none', 'True'],
  ]);
});
test('whole minimum sources: the reviewed theorem set is fixed, not proof-completion credit', async () => {
  assert.equal(SPECS.reduce((sum, spec) =>
    sum + spec.heads.filter(row => row.kind === 'theorem').length, 0), 22);
  for (const spec of SPECS) {
    assert.deepEqual(explicitLeanDeclarationHeads0(await text0(spec.file))
      .map(({kind, name}) => ({kind, name})), spec.heads);
  }
});
test('whole minimum integration: root, audit, both name producers and map keys agree before export', async () => {
  const [root, audit, regression, leanInventory, mapText, required] = await Promise.all([
    text0('lean/PNP.lean'), text0('lean-audit/PNPClosedWholeMinimumAxiomAudit.lean'),
    text0('lean-regression/PNPClosedWholeMinimum.lean'), text0('lean-audit/PNPTheoremInventory.lean'),
    text0('publication/FORMAL_PUBLICATION_MAP.json'), import('../formal-publication0.mjs'),
  ]);
  const names = SPECS.flatMap(spec => {
    const module = spec.file.replace('lean/PNP/', '').replace('.lean', '');
    assert.equal(root.split('\n').filter(line => line === 'import PNP.' + module).length, 1, module);
    return spec.heads.filter(head => head.kind === 'theorem')
      .map(head => spec.namespace + '.' + head.name);
  }).sort();
  assert.equal(names.length, 22);
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
  assert.deepEqual(map.milestones.find(row => row.id === 'computed-whole-support-minimum-bridge').requiredTheorems, names);
  for (const name of names) assert.ok(leanNames.includes(name), name);
});
test('whole minimum integration: hidden-field, empty-dimension and improper-local boundaries stay explicit', async () => {
  const regression = await text0('lean-regression/PNPClosedWholeMinimum.lean');
  assert.equal((regression.match(/^example\b/gmu) ?? []).length, 8);
  assert.equal((regression.match(/^theorem\b/gmu) ?? []).length, 6);
  assert.equal((regression.match(/^#print axioms /gmu) ?? []).length, 6);
  assert.match(regression, /closed-whole-minimum-regressions-complete: 8 general type contracts; 6 kernel guards; 8 runtime checks/u);
  for (const guard of ['hidden_field_is_nonconstant', 'dropped_field_has_quotient_equivalence',
    'dropped_field_has_no_full_equivalence', 'field_only_has_no_ordinary_interface',
    'whole_seed_is_not_proper', 'repeated_output_truth_values']) {
    assert.ok(regression.includes('#print axioms PNP.DirectWire.ClosedWholeMinimumRegression.' + guard), guard);
  }
  for (const boundary of ['quotientMinimum = 0', 'empty dimensions have no invented gate or improvement',
    'a hidden field remains required in full mode with a false keep mask',
    'the whole full minimum does not change when a keep mask changes',
    'field-only duplicate gates simplify without an ordinary interface',
    'two independent primary inputs and mixed outputs are preserved']) {
    assert.ok(regression.includes(boundary), boundary);
  }
});
