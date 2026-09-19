import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen from kernel-checked model, cost and coupling evidence before publication.
const SPECS = [
  {
    "file": "lean/PNP/NANDWireProfileAvailability.lean",
    "sourceContractSha256": "61958639a5716c9a96eefe714caa342172136ad1a1d925c7b1952a6a6026c25f",
    "heads": [
      {
        "kind": "def",
        "name": "sourceMatches"
      },
      {
        "kind": "theorem",
        "name": "sourceMatches_iff"
      },
      {
        "kind": "def",
        "name": "findSource"
      },
      {
        "kind": "def",
        "name": "available"
      },
      {
        "kind": "theorem",
        "name": "findSource_sound"
      },
      {
        "kind": "theorem",
        "name": "available_of_source"
      },
      {
        "kind": "theorem",
        "name": "current_available"
      },
      {
        "kind": "def",
        "name": "bind"
      },
      {
        "kind": "theorem",
        "name": "bind_implementation"
      },
      {
        "kind": "theorem",
        "name": "bind_gateCount"
      },
      {
        "kind": "theorem",
        "name": "bind_fieldValue"
      },
      {
        "kind": "def",
        "name": "system"
      },
      {
        "kind": "def",
        "name": "fullComparison"
      },
      {
        "kind": "def",
        "name": "quotientComparison"
      },
      {
        "kind": "theorem",
        "name": "bind_full"
      },
      {
        "kind": "theorem",
        "name": "bind_quotient"
      },
      {
        "kind": "theorem",
        "name": "full_minimum"
      },
      {
        "kind": "theorem",
        "name": "quotient_minimum"
      },
      {
        "kind": "theorem",
        "name": "full_match_iff"
      },
      {
        "kind": "theorem",
        "name": "quotient_match_iff"
      },
      {
        "kind": "theorem",
        "name": "sourceMatches_congr"
      },
      {
        "kind": "theorem",
        "name": "findSource_congr"
      },
      {
        "kind": "theorem",
        "name": "system_congr"
      },
      {
        "kind": "theorem",
        "name": "system_fullEquivalent"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDWireProfileAmbient.lean",
    "sourceContractSha256": "dc381c4230cf1930cdb5abd114019d5b0e52f3e7870950090ca51d75e1bfac6f",
    "heads": [
      {
        "kind": "theorem",
        "name": "available_iff_exists"
      },
      {
        "kind": "def",
        "name": "padImplementation"
      },
      {
        "kind": "def",
        "name": "padCarrier"
      },
      {
        "kind": "theorem",
        "name": "pad_gateCount"
      },
      {
        "kind": "theorem",
        "name": "eval_paddedSource"
      },
      {
        "kind": "theorem",
        "name": "pad_fieldValue"
      },
      {
        "kind": "def",
        "name": "retractSource"
      },
      {
        "kind": "theorem",
        "name": "eval_retractSource"
      },
      {
        "kind": "theorem",
        "name": "available_pad_iff"
      },
      {
        "kind": "theorem",
        "name": "available_pad"
      },
      {
        "kind": "def",
        "name": "rewordImplementation"
      },
      {
        "kind": "def",
        "name": "rewordCarrier"
      },
      {
        "kind": "theorem",
        "name": "available_reword"
      },
      {
        "kind": "def",
        "name": "ambientTarget"
      },
      {
        "kind": "def",
        "name": "ambientImplementation"
      },
      {
        "kind": "def",
        "name": "model"
      },
      {
        "kind": "theorem",
        "name": "model_observe_coherent"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDWireProfileFieldClosed.lean",
    "sourceContractSha256": "0336f36d6dd13e6aae7f0310628b9c30de9d1f2c910c15bc171bd413fc6ca306",
    "heads": [
      {
        "kind": "def",
        "name": "fieldGateSeed"
      },
      {
        "kind": "def",
        "name": "records"
      },
      {
        "kind": "def",
        "name": "implementation"
      },
      {
        "kind": "theorem",
        "name": "source_selected"
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
        "name": "ambient_fieldValue"
      },
      {
        "kind": "theorem",
        "name": "available"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDSemanticGateRetraction.lean",
    "sourceContractSha256": "a390f5ee4f0276e7dd698f9a9862f2d53a94773f90566d311c0bef6b719f38e6",
    "heads": [
      {
        "kind": "abbrev",
        "name": "GateRecords"
      },
      {
        "kind": "def",
        "name": "kept"
      },
      {
        "kind": "def",
        "name": "inducedInput"
      },
      {
        "kind": "def",
        "name": "bindingForWire"
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
        "kind": "def",
        "name": "reboundSource"
      },
      {
        "kind": "def",
        "name": "implementation"
      },
      {
        "kind": "theorem",
        "name": "kept_gate_value"
      },
      {
        "kind": "theorem",
        "name": "reboundSource_value"
      },
      {
        "kind": "theorem",
        "name": "semantics"
      },
      {
        "kind": "theorem",
        "name": "gateCount_partition"
      },
      {
        "kind": "theorem",
        "name": "gateCount_eq_sub"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDFreshFieldCost.lean",
    "sourceContractSha256": "4b956206276019d3d7164b4496077a010ffa3c8e2b0f00162efe3477d501a806",
    "heads": [
      {
        "kind": "def",
        "name": "leftInput"
      },
      {
        "kind": "def",
        "name": "rightInput"
      },
      {
        "kind": "def",
        "name": "freshValue"
      },
      {
        "kind": "def",
        "name": "joinInput"
      },
      {
        "kind": "theorem",
        "name": "freshValue_joinInput"
      },
      {
        "kind": "def",
        "name": "FreshMatches"
      },
      {
        "kind": "def",
        "name": "OriginalMatches"
      },
      {
        "kind": "def",
        "name": "freshCandidate"
      },
      {
        "kind": "theorem",
        "name": "freshCandidate_semantics"
      },
      {
        "kind": "theorem",
        "name": "freshConditions"
      },
      {
        "kind": "def",
        "name": "freshGate"
      },
      {
        "kind": "theorem",
        "name": "freshGate_source"
      },
      {
        "kind": "theorem",
        "name": "freshGate_injective"
      },
      {
        "kind": "theorem",
        "name": "freshGate_value"
      },
      {
        "kind": "def",
        "name": "erased"
      },
      {
        "kind": "theorem",
        "name": "freshGate_selected"
      },
      {
        "kind": "theorem",
        "name": "erased_count_lower_bound"
      },
      {
        "kind": "def",
        "name": "falseBinding"
      },
      {
        "kind": "theorem",
        "name": "restricted_oldInput"
      },
      {
        "kind": "theorem",
        "name": "freshValue_restricted"
      },
      {
        "kind": "theorem",
        "name": "erased_constant"
      },
      {
        "kind": "def",
        "name": "retracted"
      },
      {
        "kind": "def",
        "name": "oldCandidate"
      },
      {
        "kind": "theorem",
        "name": "oldCandidate_semantics"
      },
      {
        "kind": "theorem",
        "name": "gateCount_lower_bound"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDFreshFieldExtension.lean",
    "sourceContractSha256": "c9047e042bc7d6adc251a96a9d03fe39a303d9217d582c81f35058eb5dac780e",
    "heads": [
      {
        "kind": "def",
        "name": "inputNands"
      },
      {
        "kind": "theorem",
        "name": "inputNands_eval"
      },
      {
        "kind": "def",
        "name": "extendedProgram"
      },
      {
        "kind": "def",
        "name": "extendedCandidate"
      },
      {
        "kind": "theorem",
        "name": "extended_fresh"
      },
      {
        "kind": "theorem",
        "name": "extended_old"
      },
      {
        "kind": "def",
        "name": "extend"
      },
      {
        "kind": "theorem",
        "name": "extend_gateCount"
      },
      {
        "kind": "theorem",
        "name": "extended_equivalent"
      },
      {
        "kind": "theorem",
        "name": "referenceMinimum_extend"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDFreshFieldProfile.lean",
    "sourceContractSha256": "96f796564c018d831988ea97a38b1aa6e67b958ac1fa944b79f8e9a77009934b",
    "heads": [
      {
        "kind": "def",
        "name": "padInputs"
      },
      {
        "kind": "theorem",
        "name": "padInputs_semantics"
      },
      {
        "kind": "theorem",
        "name": "referenceMinimum_padInputs"
      },
      {
        "kind": "def",
        "name": "profile"
      },
      {
        "kind": "theorem",
        "name": "profile_gateCount"
      },
      {
        "kind": "theorem",
        "name": "profile_output"
      },
      {
        "kind": "theorem",
        "name": "profile_field"
      },
      {
        "kind": "theorem",
        "name": "profile_fullMinimum"
      },
      {
        "kind": "theorem",
        "name": "profile_quotientMinimum"
      },
      {
        "kind": "theorem",
        "name": "profile_projectionDefect"
      },
      {
        "kind": "theorem",
        "name": "profile_fullSlack"
      },
      {
        "kind": "theorem",
        "name": "profile_materializer_charge_lower_bound"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDComputedWireProfileCost.lean",
    "sourceContractSha256": "f04cb3d20c2dccb9d224f1c5861530df68412a40ec8f80e9213ec7ac3edcf718",
    "heads": [
      {
        "kind": "theorem",
        "name": "full_minimum"
      },
      {
        "kind": "theorem",
        "name": "quotient_minimum"
      },
      {
        "kind": "theorem",
        "name": "minimum_gap"
      }
    ]
  }
];
const AXIOM_NAMES = [
  "PNP.DirectWire.ComputedWireProfileCost.full_minimum",
  "PNP.DirectWire.ComputedWireProfileCost.minimum_gap",
  "PNP.DirectWire.ComputedWireProfileCost.quotient_minimum",
  "PNP.DirectWire.FreshNandCost.erased_constant",
  "PNP.DirectWire.FreshNandCost.erased_count_lower_bound",
  "PNP.DirectWire.FreshNandCost.extend_gateCount",
  "PNP.DirectWire.FreshNandCost.extended_equivalent",
  "PNP.DirectWire.FreshNandCost.extended_fresh",
  "PNP.DirectWire.FreshNandCost.extended_old",
  "PNP.DirectWire.FreshNandCost.freshCandidate_semantics",
  "PNP.DirectWire.FreshNandCost.freshConditions",
  "PNP.DirectWire.FreshNandCost.freshGate_injective",
  "PNP.DirectWire.FreshNandCost.freshGate_selected",
  "PNP.DirectWire.FreshNandCost.freshGate_source",
  "PNP.DirectWire.FreshNandCost.freshGate_value",
  "PNP.DirectWire.FreshNandCost.freshValue_joinInput",
  "PNP.DirectWire.FreshNandCost.freshValue_restricted",
  "PNP.DirectWire.FreshNandCost.gateCount_lower_bound",
  "PNP.DirectWire.FreshNandCost.inputNands_eval",
  "PNP.DirectWire.FreshNandCost.oldCandidate_semantics",
  "PNP.DirectWire.FreshNandCost.padInputs_semantics",
  "PNP.DirectWire.FreshNandCost.profile_field",
  "PNP.DirectWire.FreshNandCost.profile_fullMinimum",
  "PNP.DirectWire.FreshNandCost.profile_fullSlack",
  "PNP.DirectWire.FreshNandCost.profile_gateCount",
  "PNP.DirectWire.FreshNandCost.profile_materializer_charge_lower_bound",
  "PNP.DirectWire.FreshNandCost.profile_output",
  "PNP.DirectWire.FreshNandCost.profile_projectionDefect",
  "PNP.DirectWire.FreshNandCost.profile_quotientMinimum",
  "PNP.DirectWire.FreshNandCost.referenceMinimum_extend",
  "PNP.DirectWire.FreshNandCost.referenceMinimum_padInputs",
  "PNP.DirectWire.FreshNandCost.restricted_oldInput",
  "PNP.DirectWire.SemanticGateRetraction.gateCount_eq_sub",
  "PNP.DirectWire.SemanticGateRetraction.gateCount_partition",
  "PNP.DirectWire.SemanticGateRetraction.kept_gate_value",
  "PNP.DirectWire.SemanticGateRetraction.reboundSource_value",
  "PNP.DirectWire.SemanticGateRetraction.semantics",
  "PNP.DirectWire.WireProfileAmbient.available_iff_exists",
  "PNP.DirectWire.WireProfileAmbient.available_pad",
  "PNP.DirectWire.WireProfileAmbient.available_pad_iff",
  "PNP.DirectWire.WireProfileAmbient.available_reword",
  "PNP.DirectWire.WireProfileAmbient.eval_paddedSource",
  "PNP.DirectWire.WireProfileAmbient.eval_retractSource",
  "PNP.DirectWire.WireProfileAmbient.model_observe_coherent",
  "PNP.DirectWire.WireProfileAmbient.pad_fieldValue",
  "PNP.DirectWire.WireProfileAmbient.pad_gateCount",
  "PNP.DirectWire.WireProfileAvailability.available_of_source",
  "PNP.DirectWire.WireProfileAvailability.bind_fieldValue",
  "PNP.DirectWire.WireProfileAvailability.bind_full",
  "PNP.DirectWire.WireProfileAvailability.bind_gateCount",
  "PNP.DirectWire.WireProfileAvailability.bind_implementation",
  "PNP.DirectWire.WireProfileAvailability.bind_quotient",
  "PNP.DirectWire.WireProfileAvailability.current_available",
  "PNP.DirectWire.WireProfileAvailability.findSource_congr",
  "PNP.DirectWire.WireProfileAvailability.findSource_sound",
  "PNP.DirectWire.WireProfileAvailability.full_match_iff",
  "PNP.DirectWire.WireProfileAvailability.full_minimum",
  "PNP.DirectWire.WireProfileAvailability.quotient_match_iff",
  "PNP.DirectWire.WireProfileAvailability.quotient_minimum",
  "PNP.DirectWire.WireProfileAvailability.sourceMatches_congr",
  "PNP.DirectWire.WireProfileAvailability.sourceMatches_iff",
  "PNP.DirectWire.WireProfileAvailability.system_congr",
  "PNP.DirectWire.WireProfileAvailability.system_fullEquivalent",
  "PNP.DirectWire.WireProfileFieldClosed.ambient_fieldValue",
  "PNP.DirectWire.WireProfileFieldClosed.available",
  "PNP.DirectWire.WireProfileFieldClosed.boundary_isInput",
  "PNP.DirectWire.WireProfileFieldClosed.gate_value",
  "PNP.DirectWire.WireProfileFieldClosed.source_selected",
  "PNP.DirectWire.extractTerminalSupport_gate_evaluation",
  "PNP.DirectWire.extractTerminalSupport_gate_induced",
  "PNP.DirectWire.terminalPhysicalComplementRecords_gateCount_partition",
  "PNP.DirectWire.terminalPhysicalComplementRecords_selected"
];
const REGRESSIONS = [
  {
    "file": "lean-regression/PNPWireProfileAvailability.lean",
    "sourceContractSha256": "186514e49d96ba4de30b94c7072ec6718b9be66dd56b6d2e87ab8e2406ec4665",
    "typeContracts": 7,
    "runtime": true
  },
  {
    "file": "lean-regression/PNPWireProfileObserverBoundary.lean",
    "sourceContractSha256": "52151010a02b1eb08a8a886f4c6188768ceffe336efbef40bec7cc01615d7154",
    "typeContracts": 0,
    "runtime": false
  },
  {
    "file": "lean-regression/PNPWireProfileAmbient.lean",
    "sourceContractSha256": "df2e21ec897e34e6056558d7f46a0cdcbbab898252832d11baa8eea010c3ec29",
    "typeContracts": 8,
    "runtime": true
  },
  {
    "file": "lean-regression/PNPWireProfileFieldClosed.lean",
    "sourceContractSha256": "99c4ec4b94d0d83ea871bdb0541e3b4a99c0793553e150be3c116a7a75525fce",
    "typeContracts": 5,
    "runtime": true
  },
  {
    "file": "lean-regression/PNPSemanticGateRetraction.lean",
    "sourceContractSha256": "90fa4112b48e9760cc102b1c80882e9eecc98f681915f72cda6f1c2189a35dbc",
    "typeContracts": 3,
    "runtime": true
  },
  {
    "file": "lean-regression/PNPFreshFieldCost.lean",
    "sourceContractSha256": "943837f338aed5f8ba95e616292d79fe08fa5bb4d2757d944a8ced157ff9b2b9",
    "typeContracts": 6,
    "runtime": true
  },
  {
    "file": "lean-regression/PNPFreshFieldProfile.lean",
    "sourceContractSha256": "19e1077ba052bd0b2299b6baf55c96a392d8f79f2fe158c368c93f9ff55b67c3",
    "typeContracts": 6,
    "runtime": true
  },
  {
    "file": "lean-regression/PNPComputedWireProfileCost.lean",
    "sourceContractSha256": "eda0dd0522add7404d7fb5555f2e5f369290f9f707dc5a39f20b108dab392ff7",
    "typeContracts": 3,
    "runtime": false
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
test('computed wire-profile models: all reviewed sources and comment-only prose', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    assert.deepEqual(inspect0(spec, source), [], spec.file);
    assert.deepEqual(inspect0(spec, source + '\n/- explanatory prose only -/\n'), [], spec.file);
  }
});
test('computed wire-profile models: assumptions, supplied conclusions and shortcuts reject', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    for (const extra of [
      'axiom suppliedCompleteness : True',
      'private axiom suppliedCost : True',
      'opaque suppliedFieldFamily : True',
      'private theorem suppliedAuthority : True := by trivial',
      'theorem assumedCompleteness : True := by sorry',
      'example : True := by trivial',
      'variable (suppliedMinimum : Nat)',
      'import PNP.Main',
    ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length > 0, spec.file + ': ' + extra);
  }
});
test('computed wire-profile models: one uniform actual source and ordinary outputs remain required', async () => {
  await reject0('NANDWireProfileAvailability', [
    ['computed observer', 'observe := available target', 'observe := fun _ _ => true'],
    ['computed source search', '(allSources inputs offered.gateCount).find? (sourceMatches target offered field)',
      'some (.constant false)'],
    ['all valuations, not one selected assignment', 'allTrue (allBoolTuples inputs) fun tuple =>',
      'allTrue [(BoolTuple.ofFn (fun _ => false))] fun tuple =>'],
    ['ordinary output equivalence', 'equivalent := ((WireProfile.full_iff target offered).mp same).1',
      'equivalent := suppliedOrdinaryOutputEquality'],
    ['implementation width remains general', '(offered : Implementation inputs outputs)',
      '(offered : Implementation 1 outputs)'],
  ]);
});
test('computed wire-profile models: explicit independent-field cost is neither free nor an arbitrary-field claim', async () => {
  await reject0('NANDComputedWireProfileCost', [
    ['exact forced added cost', 'referenceMinimum target + width', 'referenceMinimum target'],
    ['exact quotient minimum', 'referenceMinimum target := by', 'referenceMinimum target + width := by'],
    ['computed actual model', 'WireProfileAmbient.model (FreshNandCost.profile target width) keep',
      'suppliedTerminalModel'],
    ['independent constructed family', 'FreshNandCost.profile target width', 'suppliedArbitraryProfile'],
    ['all widths', '(width : Nat)', '(width : Fin 3)'],
    ['all fields forgotten in quotient', '(fun _ => false)', '(fun _ => true)'],
  ]);
});
test('computed wire-profile models: explicit root, compiled producer and reviewed names stay synchronized', async () => {
  const [root, audit, producer, consumer] = await Promise.all([
    text0('lean/PNP.lean'), text0('lean-audit/PNPComputedWireProfileAxiomAudit.lean'),
    text0('lean-audit/PNPTheoremInventory.lean'), text0('formal-publication0.mjs'),
  ]);
  for (const spec of SPECS) {
    const module = spec.file.replace('lean/', '').replaceAll('/', '.').replace('.lean', '');
    assert.ok(root.split('\n').includes('import ' + module), module);
  }
  assert.match(audit, /^import PNP$/mu);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]), AXIOM_NAMES);
  assert.equal(AXIOM_NAMES.length, 72);
  assert.equal(new Set(AXIOM_NAMES).size, AXIOM_NAMES.length);
  for (const name of AXIOM_NAMES) {
    assert.ok(producer.includes(String.fromCharCode(96) + name + ','), name);
    assert.ok(consumer.includes('"' + name + '"') || consumer.includes("'" + name + "'"), name);
  }
});
test('computed wire-profile models: independent contracts and obstruction fixtures retain reviewed bodies', async () => {
  for (const spec of REGRESSIONS) {
    const source = await text0(spec.file);
    assert.match(source, /^import PNP$/mu);
    assert.equal(digest0(source), spec.sourceContractSha256, spec.file);
    assert.equal([...source.matchAll(/^example\b/gmu)].length, spec.typeContracts, spec.file);
    assert.equal(/^def main\b/mu.test(source), spec.runtime, spec.file);
    assert.doesNotMatch(stripLeanCommentsAndStrings0(source),
      /\b(?:sorry|admit|unsafe|native_decide)\b|decide\s+\+native|#eval!/u);
  }
});
