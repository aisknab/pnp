import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen from the kernel-checked and assumption-audited general construction.
// This source gate does not replace root, inventory or publication checks.
const SPECS = [
  {
    "file": "lean/PNP/NANDClosedSupportFullGainPrefix.lean",
    "namespace": "PNP.DirectWire.ClosedSupportFullGain",
    "sourceContractSha256": "c8dcb63810bf1003ac11a577455e838bfac4321897249c8fe551346fcd095a53",
    "heads": [
      {
        "kind": "def",
        "name": "fullRealization"
      },
      {
        "kind": "def",
        "name": "offered"
      },
      {
        "kind": "def",
        "name": "extendZero"
      },
      {
        "kind": "theorem",
        "name": "restrict_extendZero"
      },
      {
        "kind": "def",
        "name": "inputBinding"
      },
      {
        "kind": "theorem",
        "name": "inputBinding_eval"
      },
      {
        "kind": "def",
        "name": "prefixProgram"
      },
      {
        "kind": "def",
        "name": "prefixSource"
      },
      {
        "kind": "theorem",
        "name": "prefixSource_value"
      },
      {
        "kind": "theorem",
        "name": "offered_available"
      },
      {
        "kind": "def",
        "name": "prefixField"
      },
      {
        "kind": "theorem",
        "name": "prefixField_value"
      },
      {
        "kind": "theorem",
        "name": "interface_index_sound"
      },
      {
        "kind": "theorem",
        "name": "interface_index_exists"
      },
      {
        "kind": "theorem",
        "name": "ambient_output"
      },
      {
        "kind": "def",
        "name": "prefixOutput"
      },
      {
        "kind": "theorem",
        "name": "prefixOutput_value"
      },
      {
        "kind": "theorem",
        "name": "offered_gateCount"
      },
      {
        "kind": "theorem",
        "name": "offered_gateCount_le"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDClosedSupportFullGain.lean",
    "namespace": "PNP.DirectWire.ClosedSupportFullGain",
    "sourceContractSha256": "72a5bb16c92fecfbc35d84ce73ba23aed7417897bfc26d2ad722a4bc445b846c",
    "heads": [
      {
        "kind": "def",
        "name": "complementRecords"
      },
      {
        "kind": "def",
        "name": "complement"
      },
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
        "name": "complement_gate_value"
      },
      {
        "kind": "theorem",
        "name": "retained_source_value"
      },
      {
        "kind": "def",
        "name": "outputSource"
      },
      {
        "kind": "theorem",
        "name": "outputSource_value"
      },
      {
        "kind": "def",
        "name": "fieldSource"
      },
      {
        "kind": "theorem",
        "name": "fieldSource_value"
      },
      {
        "kind": "def",
        "name": "result"
      },
      {
        "kind": "theorem",
        "name": "result_output"
      },
      {
        "kind": "theorem",
        "name": "result_fullEquivalent"
      },
      {
        "kind": "theorem",
        "name": "result_exact_accounting"
      },
      {
        "kind": "theorem",
        "name": "result_gain_balance"
      },
      {
        "kind": "theorem",
        "name": "result_strict_iff"
      },
      {
        "kind": "def",
        "name": "improvement?"
      },
      {
        "kind": "theorem",
        "name": "improvement?_sound"
      },
      {
        "kind": "theorem",
        "name": "improvement?_none_iff"
      },
      {
        "kind": "theorem",
        "name": "result_fullMinimum"
      },
      {
        "kind": "theorem",
        "name": "result_fullSlack_balance"
      },
      {
        "kind": "theorem",
        "name": "localFullSlack_le_global"
      },
      {
        "kind": "theorem",
        "name": "improvement?_strictGain"
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
test('full gain sources: reviewed general interfaces and comment-only prose', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    assert.deepEqual(inspect0(spec, source), [], spec.file);
    assert.deepEqual(inspect0(spec, source + '\n/- explanatory prose only -/\n'), [], spec.file);
  }
});
test('full gain sources: supplied authority and unchecked shortcuts reject', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    for (const extra of [
      'axiom suppliedCompleteness : True', 'private axiom suppliedChoice : True',
      'opaque suppliedReplacement : True', 'private theorem suppliedAuthority : True := by trivial',
      'theorem assumedCorrectness : True := by sorry', 'example : True := by trivial',
      'variable (suppliedCompatibility : Prop)', 'import PNP.Main',
    ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length > 0, spec.file + ': ' + extra);
  }
});
test('full gain sources: the full minimum, input binding and uniform field source are computed', async () => {
  await reject0('NANDClosedSupportFullGainPrefix', [
    ['full rather than quotient minimum', 'terminalFullProfileMinimumRealization',
      'terminalQuotientProfileMinimumComparison'],
    ['computed observer', '(WireProfileAmbient.model target keep).ambientProfileSystem',
      'suppliedModel.ambientProfileSystem'],
    ['all primary inputs are preserved',
      'splitFin (fun index => .input index) (fun _ : Fin extra => .constant false)',
      'fun _ => .constant false'],
    ['arbitrary input dimensions', '(target : WireCarrier inputs outputs fields)',
      '(target : WireCarrier 1 outputs fields)'],
    ['field sources are searched', '((WireProfileAvailability.bind (WireProfileAmbient.ambientTarget target)',
      '((suppliedBinding (WireProfileAmbient.ambientTarget target)'],
  ]);
});
test('full gain sources: physical complement and actual reconnection cannot be supplied or discarded', async () => {
  await reject0('NANDClosedSupportFullGain', [
    ['actual complementary gates',
      'terminalPhysicalComplementRecords (ClosedSupportObservation.records target keep seed)',
      'ClosedSupportObservation.records target keep seed'],
    ['real crossing-edge value', '| .gate producer => prefixOutput target keep seed producer',
      '| .gate producer => .constant false'],
    ['derived external boundary', '(boundaryBinding target keep seed)', '(fun _ => .constant false)'],
    ['retained hidden field',
      'then (prefixField target keep seed field).weakenGates (complement target keep seed).gateCount',
      'then .constant false'],
  ]);
});
test('full gain sources: positive full slack and exact conservation are separate from quotient savings', async () => {
  await reject0('NANDClosedSupportFullGain', [
    ['zero slack does not improve',
      'if 0 < (terminalSaturationCostSnapshot target.implementation.candidate',
      'if 0 ≤ (terminalSaturationCostSnapshot target.implementation.candidate'],
    ['all fields rather than only the keep mask',
      'WireProfile.FullEquivalent target (result target keep seed)',
      'WireProfile.QuotientEquivalent keep target (result target keep seed)'],
    ['real residual descent', 'StrictEquivalentGain target.implementation replacement.implementation',
      'True'],
    ['whole full slack is the conservation target', 'WireProfile.fullSlack target',
      'WireProfile.projectionDefect target keep'],
  ]);
});
test('full gain sources: public theorem interface is fixed without awarding declaration-count credit', async () => {
  assert.equal(SPECS.reduce((sum, spec) =>
    sum + spec.heads.filter(row => row.kind === 'theorem').length, 0), 27);
  for (const spec of SPECS) {
    assert.deepEqual(explicitLeanDeclarationHeads0(await text0(spec.file))
      .map(({kind, name}) => ({kind, name})), spec.heads);
  }
});
test('full gain integration: root and both inventory name producers agree before compiled export', async () => {
  const [root, audit, regression, leanInventory, required] = await Promise.all([
    text0('lean/PNP.lean'), text0('lean-audit/PNPClosedSupportFullGainAxiomAudit.lean'),
    text0('lean-regression/PNPClosedSupportFullGain.lean'), text0('lean-audit/PNPTheoremInventory.lean'),
    import('../formal-publication0.mjs'),
  ]);
  const names = SPECS.flatMap(spec => {
    const module = spec.file.replace('lean/PNP/', '').replace('.lean', '');
    assert.equal(root.split('\n').filter(line => line === 'import PNP.' + module).length, 1, module);
    return spec.heads.filter(head => head.kind === 'theorem')
      .map(head => spec.namespace + '.' + head.name);
  }).sort();
  assert.equal(names.length, 27);
  assert.match(audit, /^import PNP\n/u);
  assert.match(regression, /^import PNP\n/u);
  assert.equal((regression.match(/^import /gmu) ?? []).length, 1);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]).sort(), names);
  const leanList = leanInventory.match(/private def reviewedMilestoneTheoremNames : Array Name := #\[([\s\S]*?)\]/mu);
  assert.ok(leanList);
  const leanNames = [...leanList[1].matchAll(/`([^,\s]+)/gu)].map(row => row[1]).sort();
  assert.deepEqual(leanNames, [...required.REQUIRED_MILESTONE_THEOREMS0].sort());
  assert.equal(new Set(leanNames).size, leanNames.length);
  for (const name of names) assert.ok(leanNames.includes(name), name);
});
test('full gain integration: hostile hidden-field, crossing-edge and no-gain regressions remain explicit', async () => {
  const regression = await text0('lean-regression/PNPClosedSupportFullGain.lean');
  assert.equal((regression.match(/^example\b/gmu) ?? []).length, 8);
  assert.equal((regression.match(/^theorem\b/gmu) ?? []).length, 5);
  assert.equal((regression.match(/^#print axioms /gmu) ?? []).length, 5);
  assert.match(regression, /closed-support-full-gain-regressions-complete: 8 general type contracts; 5 kernel guards; 10 runtime checks/u);
  for (const guard of ['hidden_field_is_nonconstant', 'dropping_field_preserves_ordinary_outputs',
    'dropping_field_is_not_full_equivalence', 'crossing_edge_is_not_optional',
    'exterior_field_is_nonconstant']) {
    assert.ok(regression.includes('#print axioms PNP.DirectWire.ClosedSupportFullGainRegression.' + guard), guard);
  }
  for (const boundary of ['quotientMinimum = 0', 'fullMinimum = 1',
    'field-only improvement retains an internal value absent from all ordinary outputs',
    'reconnection preserves a real support-to-exterior edge',
    'proper gain retains a nonconstant exterior field',
    'duplicate gates give a strict whole-span gain',
    'empty selected support reconstructs all exterior values with no gain']) {
    assert.ok(regression.includes(boundary), boundary);
  }
});
