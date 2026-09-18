import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen reviewed source contracts; these are not compiled theorem fingerprints.
// Kernel proofs, exact-root axiom checks and publication sealing remain separate.
const SPECS = [
  {
    "file": "lean/PNP/NANDZeroCostExposure.lean",
    "sourceContractSha256": "aaaaed896c9b5672e009e02fbc433d40c1cc63a350329d0de094c2e929aad5c1",
    "heads": [
      {
        "kind": "inductive",
        "name": "Reference"
      },
      {
        "kind": "def",
        "name": "Reference.value"
      },
      {
        "kind": "def",
        "name": "Reference.toSource"
      },
      {
        "kind": "theorem",
        "name": "Reference.toSource_eval"
      },
      {
        "kind": "theorem",
        "name": "Reference.value_congr"
      },
      {
        "kind": "def",
        "name": "extend"
      },
      {
        "kind": "def",
        "name": "project"
      },
      {
        "kind": "theorem",
        "name": "extend_gateCount"
      },
      {
        "kind": "theorem",
        "name": "project_gateCount"
      },
      {
        "kind": "theorem",
        "name": "extend_original"
      },
      {
        "kind": "theorem",
        "name": "extend_field"
      },
      {
        "kind": "theorem",
        "name": "project_semantics"
      },
      {
        "kind": "theorem",
        "name": "extend_equivalent"
      },
      {
        "kind": "theorem",
        "name": "project_equivalent"
      },
      {
        "kind": "theorem",
        "name": "project_extend_equivalent"
      },
      {
        "kind": "theorem",
        "name": "referenceMinimum_extend"
      },
      {
        "kind": "theorem",
        "name": "residualSlack_extend"
      },
      {
        "kind": "structure",
        "name": "Recognition"
      },
      {
        "kind": "def",
        "name": "recognize"
      },
      {
        "kind": "def",
        "name": "checkLayout"
      },
      {
        "kind": "structure",
        "name": "LayoutRecognition"
      },
      {
        "kind": "def",
        "name": "compileLayout"
      },
      {
        "kind": "theorem",
        "name": "compileLayout_success_iff"
      },
      {
        "kind": "theorem",
        "name": "compileLayout_sound"
      },
      {
        "kind": "theorem",
        "name": "recognize_success_iff"
      },
      {
        "kind": "theorem",
        "name": "recognize_isSome_iff"
      },
      {
        "kind": "theorem",
        "name": "recognize_none_iff"
      },
      {
        "kind": "theorem",
        "name": "recognize_gate_none_iff"
      },
      {
        "kind": "theorem",
        "name": "checkLayout_iff"
      },
      {
        "kind": "theorem",
        "name": "compileLayout_available_iff"
      }
    ]
  },
  {
    "file": "lean/PNP/NANDWireCarrierZeroCostExposure.lean",
    "sourceContractSha256": "b3b8dd7f6137a4eae305b50dbe7227b700cc5b1b1f7f6e95ca1d3206aa80395b",
    "heads": [
      {
        "kind": "theorem",
        "name": "exposed_referenceMinimum_of_checkLayout"
      },
      {
        "kind": "theorem",
        "name": "exposed_residualSlack_of_checkLayout"
      },
      {
        "kind": "theorem",
        "name": "checked_exposure_preserves_problem"
      }
    ]
  }
];
const AXIOM_NAMES = [
  "PNP.DirectWire.ZeroCostExposure.Reference.toSource_eval",
  "PNP.DirectWire.ZeroCostExposure.extend_gateCount",
  "PNP.DirectWire.ZeroCostExposure.project_gateCount",
  "PNP.DirectWire.ZeroCostExposure.extend_original",
  "PNP.DirectWire.ZeroCostExposure.extend_field",
  "PNP.DirectWire.ZeroCostExposure.project_semantics",
  "PNP.DirectWire.ZeroCostExposure.extend_equivalent",
  "PNP.DirectWire.ZeroCostExposure.project_equivalent",
  "PNP.DirectWire.ZeroCostExposure.project_extend_equivalent",
  "PNP.DirectWire.ZeroCostExposure.referenceMinimum_extend",
  "PNP.DirectWire.ZeroCostExposure.residualSlack_extend",
  "PNP.DirectWire.ZeroCostExposure.compileLayout_success_iff",
  "PNP.DirectWire.ZeroCostExposure.compileLayout_sound",
  "PNP.DirectWire.ZeroCostExposure.recognize_success_iff",
  "PNP.DirectWire.ZeroCostExposure.recognize_isSome_iff",
  "PNP.DirectWire.ZeroCostExposure.recognize_none_iff",
  "PNP.DirectWire.ZeroCostExposure.recognize_gate_none_iff",
  "PNP.DirectWire.ZeroCostExposure.checkLayout_iff",
  "PNP.DirectWire.ZeroCostExposure.compileLayout_available_iff",
  "PNP.DirectWire.WireCarrier.exposed_referenceMinimum_of_checkLayout",
  "PNP.DirectWire.WireCarrier.exposed_residualSlack_of_checkLayout",
  "PNP.DirectWire.WireCarrier.checked_exposure_preserves_problem"
];

const text0 = relative => readFile(new URL('../' + relative, import.meta.url), 'utf8');
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');

function inspect0(source, spec) {
  const issues = [];
  if (hasLeanAssumptionDeclaration0(source)) issues.push('assumption declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) issues.push('unaudited declaration');
  const stripped = stripLeanCommentsAndStrings0(source);
  if (/\b(?:sorry|admit|unsafe|native_decide)\b|decide\s+\+native/u.test(stripped))
    issues.push('unchecked authority');
  const heads = explicitLeanDeclarationHeads0(source).map(({ kind, name }) => ({ kind, name }));
  if (JSON.stringify(heads) !== JSON.stringify(spec.heads)) issues.push('changed public interface');
  if (digest0(source) !== spec.sourceContractSha256) issues.push('changed reviewed contract');
  return issues;
}

async function reject0(part, mutations) {
  const spec = SPECS[part], source = await text0(spec.file);
  assert.deepEqual(inspect0(source, spec), []);
  for (const [label, before, after] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor absent: ' + label);
    const changed = source.replace(before, () => after);
    assert.notEqual(changed, source, label);
    assert.ok(inspect0(changed, spec).length > 0, 'accepted mutation: ' + label);
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

test('zero-cost exposure: general source interfaces retain their reviewed contracts', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    assert.deepEqual(inspect0(source, spec), [], spec.file);
    assert.deepEqual(inspect0(source + '\n/- explanatory prose only -/\n', spec), []);
  }
});

test('zero-cost exposure: added assumptions and hidden proof shortcuts reject', async () => {
  for (const spec of SPECS) {
    const source = await text0(spec.file);
    for (const extra of [
      'axiom suppliedMinimum : True',
      'private axiom suppliedMinimum : True',
      'opaque suppliedMinimum : True',
      'private theorem extraAuthority : True := by trivial',
      'theorem extraAuthority : True := by sorry',
      'example : True := by trivial',
      'variable (suppliedObserver : Nat)',
      'import PNP.Main',
    ]) assert.ok(inspect0(source + '\n' + extra + '\n', spec).length > 0, extra);
  }
});

test('zero-cost exposure: constructors do not execute minima or truth-table enumeration', async () => {
  const source = await text0(SPECS[0].file);
  for (const name of [
    'Reference.value', 'Reference.toSource', 'extend', 'project', 'findOutput',
    'recognize', 'chosenReference', 'checkLayout', 'compileLayout',
  ]) assert.doesNotMatch(definition0(source, name),
    /\b(?:referenceMinimum|allCandidates|allPrograms|allBoolTuples|equivalentBool)\b/u, name);
});

test('zero-cost exposure: literal references and both realization transfers are mandatory', async () => {
  await reject0(0, [
    ['closed aliases', '| output : Fin outputs → Reference inputs outputs',
      '| output : Fin outputs → Reference inputs outputs\n  | gate : Nat → Reference inputs outputs'],
    ['all dimensions', '(layout : Fin added → Reference inputs outputs)',
      '(layout : Fin 1 → Reference inputs outputs)'],
    ['original program', 'Candidate.ofDirectWireWord current.candidate.program',
      'Candidate.ofDirectWireWord suppliedProgram'],
    ['prefix projection', '(Fin.castAdd added output)', '(Fin.natAdd outputs output)'],
    ['semantic minimum not physical size',
      'referenceMinimum (extend current layout) = referenceMinimum current',
      '(extend current layout).gateCount = current.gateCount'],
    ['arbitrary competing realization',
      'extend (referenceMinimumImplementation current)', 'extend current'],
  ]);
});

test('zero-cost exposure: source matching scans actual outputs and all requested fields', async () => {
  await reject0(0, [
    ['literal equality', 'current.candidate.directWireWord.source output = field then',
      'True then'],
    ['actual output scan', 'findOutput current (.gate index) (allFin outputs)',
      'findOutput current (.gate index) []'],
    ['all fields', 'allTrue (allFin added)', 'allTrue []'],
    ['actual field binding', '(recognize current (fields field)).isSome', 'true'],
    ['computed acceptance', 'if checked : checkLayout current fields = true then',
      'if checked : True then'],
    ['exact source receipt', 'source_eq : reference.toSource current = field',
      'source_eq : True'],
  ]);
});

test('zero-cost exposure: refusal and syntactic completeness cannot become semantic overclaims', async () => {
  await reject0(0, [
    ['exact refusal', '∀ output, current.candidate.directWireWord.source output ≠ .gate gate',
      'True'],
    ['literal completeness', 'reference.toSource current = fields field :=',
      'True :='],
  ]);
  const source = await text0(SPECS[0].file);
  assert.match(source, /This is not completeness for all semantic identities/u);
  assert.match(source, /Refusal neither proves a gain nor excludes another semantic encoding/u);
});

test('zero-cost exposure: carrier claims concern actual exposure and computed admission', async () => {
  await reject0(1, [
    ['actual exposed minimum', 'referenceMinimum carrier.exposed = referenceMinimum carrier.implementation',
      'referenceMinimum carrier.implementation = referenceMinimum carrier.implementation'],
    ['computed source admission', 'ZeroCostExposure.checkLayout carrier.implementation carrier.source = true',
      'True'],
    ['actual physical fields', 'rw [← receipt.source_eq field]', 'skip'],
    ['minimum-invariance link', 'referenceMinimum_invariant carrier.exposed',
      'referenceMinimum_invariant carrier.implementation'],
    ['slack contract', 'residualSlack carrier.exposed = residualSlack carrier.implementation',
      'True'],
  ]);
});

test('zero-cost exposure: exact root and axiom probes cover the reviewed general claims', async () => {
  const [root, audit] = await Promise.all([
    text0('lean/PNP.lean'), text0('lean-audit/PNPZeroCostExposureAxiomAudit.lean'),
  ]);
  for (const spec of SPECS) assert.ok(root.split('\n').includes(
    'import ' + spec.file.slice(5, -5).replaceAll('/', '.')));
  assert.match(audit, /^import PNP$/mu);
  assert.deepEqual([...audit.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]), AXIOM_NAMES);
  assert.equal(new Set(AXIOM_NAMES).size, AXIOM_NAMES.length);
  assert.ok(AXIOM_NAMES.every(name => /^PNP\.[A-Za-z0-9_.]+$/u.test(name)));
});

test('zero-cost exposure: regressions retain general contracts and both cost counterexamples', async () => {
  const regression = await text0('lean-regression/PNPZeroCostExposure.lean');
  assert.match(regression, /^import PNP$/mu);
  assert.doesNotMatch(stripLeanCommentsAndStrings0(regression),
    /\b(?:sorry|admit|unsafe|native_decide)\b|decide\s+\+native|#eval!/u);
  for (const name of [
    'referenceMinimum_extend', 'residualSlack_extend', 'recognize_success_iff',
    'recognize_gate_none_iff', 'compileLayout_available_iff', 'checked_exposure_preserves_problem',
    'duplicate_minimum_unchanged', 'hidden_exposure_changes_minimum_without_new_gates',
    'hidden_exposure_destroys_slack', 'mixedAliases', 'fieldsOnly', 'allEmpty', 'semanticallyDuplicate',
  ]) assert.ok(regression.includes(name), name);
  assert.match(regression, /compileLayout hiddenNot\.implementation hiddenNot\.source = none/u);
  assert.match(regression, /checkLayout semanticallyDuplicate\.implementation semanticallyDuplicate\.source = false/u);
});
