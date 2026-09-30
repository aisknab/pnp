import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {
  explicitLeanDeclarationHeads0, hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0, stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

// Frozen reviewed contracts. Tests must never derive these from their input.
const SPECS = [
  {
    "file": "lean/PNP/NANDJointAsymmetricBound.lean",
    "sourceContractSha256": "e56bca2b38225c7893b1f6a30863772addbaeaef7175d5f0109729c8fa5a8103",
    "heads": [
      [
        "theorem",
        "zero_budget_read_once"
      ],
      [
        "theorem",
        "asymmetric_bound"
      ],
      [
        "theorem",
        "two_positions_permutation"
      ],
      [
        "theorem",
        "two_output_positions_bound"
      ]
    ]
  },
  {
    "file": "lean/PNP/NANDGuardedSpineSupportMinimum.lean",
    "sourceContractSha256": "ded5b2b71964f954f460dc38ae5591fbedbda403663720b09ca6e44ea9205229",
    "heads": [
      [
        "theorem",
        "first_only_minimum"
      ],
      [
        "theorem",
        "both_ends_minimum"
      ],
      [
        "theorem",
        "proper_minimum"
      ]
    ]
  },
  {
    "file": "lean/PNP/NANDGuardedSpineBoundedQuiet.lean",
    "sourceContractSha256": "a4d2fbec554ec179fa1e0ec9eb1fc44c7841e163097fde3049fe25165af6eb7f",
    "heads": [
      [
        "theorem",
        "proper_of_small_support"
      ],
      [
        "theorem",
        "bounded_quiet"
      ],
      [
        "theorem",
        "scan_none"
      ],
      [
        "theorem",
        "quiet_with_strict_gain"
      ],
      [
        "theorem",
        "quiet_nonminimum_exists"
      ],
      [
        "theorem",
        "no_uniform_zero_slack_limit"
      ]
    ]
  },
  {
    "file": "lean/PNP/NANDCompleteBoundedWindowSearch.lean",
    "sourceContractSha256": "ae2289b8345bcead97515a9842176e88b1135a76c9dbea95e7cac23f152fbe43",
    "heads": [
      [
        "structure",
        "FoundIn"
      ],
      [
        "def",
        "result"
      ],
      [
        "def",
        "gain"
      ],
      [
        "theorem",
        "strict_residual_descent"
      ],
      [
        "theorem",
        "support_bound"
      ],
      [
        "theorem",
        "proper_of_limit_lt"
      ],
      [
        "def",
        "scan"
      ],
      [
        "theorem",
        "scan_none_iff"
      ],
      [
        "def",
        "BoundedQuiet"
      ],
      [
        "theorem",
        "scan_schedule_none_iff"
      ],
      [
        "inductive",
        "Outcome"
      ],
      [
        "def",
        "run"
      ],
      [
        "def",
        "candidateDemand"
      ],
      [
        "theorem",
        "candidateDemand_le"
      ]
    ]
  },
  {
    "file": "lean/PNP/NANDBoundedPhysicalWindowSearch.lean",
    "sourceContractSha256": "2079a6ccf343f71cb6d8a94fbd78d970b837f47f9b0b1011c597ab454fb6effb",
    "heads": [
      [
        "def",
        "smallerCandidates"
      ],
      [
        "theorem",
        "mem_smallerCandidates"
      ],
      [
        "abbrev",
        "Offered"
      ],
      [
        "def",
        "causalCheck"
      ],
      [
        "theorem",
        "causalCheck_eq_true_iff"
      ],
      [
        "def",
        "check"
      ],
      [
        "def",
        "Valid"
      ],
      [
        "theorem",
        "check_eq_true_iff"
      ],
      [
        "def",
        "candidateUniverse"
      ],
      [
        "def",
        "search"
      ],
      [
        "theorem",
        "search_sound"
      ],
      [
        "theorem",
        "search_none_iff"
      ],
      [
        "theorem",
        "search_complete"
      ],
      [
        "structure",
        "Found"
      ],
      [
        "theorem",
        "valid"
      ],
      [
        "def",
        "compiled"
      ],
      [
        "def",
        "result"
      ],
      [
        "theorem",
        "equivalent"
      ],
      [
        "theorem",
        "exact_cost"
      ],
      [
        "def",
        "gain"
      ],
      [
        "theorem",
        "strict_residual_descent"
      ],
      [
        "inductive",
        "Outcome"
      ],
      [
        "def",
        "run"
      ]
    ]
  },
  {
    "file": "lean/PNP/NANDGuardedSpineFamily.lean",
    "sourceContractSha256": "0c54a0aaf6d6414502c82a4205bb23d13635d035ea5ebea750ccafab2428633f",
    "heads": [
      [
        "def",
        "core"
      ],
      [
        "def",
        "candidate"
      ],
      [
        "def",
        "shortCore"
      ],
      [
        "def",
        "shorter"
      ],
      [
        "def",
        "coreValue"
      ],
      [
        "def",
        "shortValue"
      ],
      [
        "theorem",
        "core_value"
      ],
      [
        "theorem",
        "short_core_value"
      ],
      [
        "theorem",
        "candidate_value"
      ],
      [
        "theorem",
        "shorter_value"
      ],
      [
        "theorem",
        "true_cofactor"
      ],
      [
        "theorem",
        "equivalent"
      ],
      [
        "theorem",
        "strict_gain"
      ],
      [
        "theorem",
        "residual_positive"
      ]
    ]
  },
  {
    "file": "lean/PNP/NANDBoundedWindowSchedule.lean",
    "sourceContractSha256": "bd1e69dca8df5c155b10ab8eb6720c1eeec80d95a1f5a5ce4b2798e0c5b30b9e",
    "heads": [
      [
        "def",
        "windowsFrom"
      ],
      [
        "theorem",
        "windowsFrom_sound"
      ],
      [
        "theorem",
        "windowsFrom_complete"
      ],
      [
        "theorem",
        "windowsFrom_nodup"
      ],
      [
        "theorem",
        "windowsFrom_length_le"
      ],
      [
        "def",
        "recordsOf"
      ],
      [
        "theorem",
        "recordsOf_selected_iff"
      ],
      [
        "theorem",
        "recordsOf_count_le"
      ],
      [
        "theorem",
        "canonical_selected"
      ],
      [
        "theorem",
        "selected_increasing"
      ],
      [
        "theorem",
        "schedule_covers"
      ],
      [
        "theorem",
        "valid_exists_of_selected_eq"
      ]
    ]
  }
];
const STAGES = [
  {
    "source": "lean/PNP/NANDJointAsymmetricBound.lean",
    "namespace": "PNP.DirectWire.JointAsymmetricBound",
    "names": [
      "PNP.DirectWire.JointAsymmetricBound.zero_budget_read_once",
      "PNP.DirectWire.JointAsymmetricBound.asymmetric_bound",
      "PNP.DirectWire.JointAsymmetricBound.two_positions_permutation",
      "PNP.DirectWire.JointAsymmetricBound.two_output_positions_bound"
    ],
    "auditFile": "lean-audit/PNPJointAsymmetricBoundAxiomAudit.lean",
    "fixtureFile": "lean-regression/PNPJointAsymmetricBoundProbe.lean",
    "fixtureNames": [
      "PNP.DirectWire.JointAsymmetricBoundProbe.general_zero_budget_read_once",
      "PNP.DirectWire.JointAsymmetricBoundProbe.general_asymmetric_bound",
      "PNP.DirectWire.JointAsymmetricBoundProbe.general_two_positions_permutation",
      "PNP.DirectWire.JointAsymmetricBoundProbe.general_two_output_positions_bound",
      "PNP.DirectWire.JointAsymmetricBoundProbe.equal_values_keep_two_positions",
      "PNP.DirectWire.JointAsymmetricBoundProbe.one_position_is_not_two",
      "PNP.DirectWire.JointAsymmetricBoundProbe.direct_input_fails_true_at_false"
    ],
    "fixtureContractSha256": "83f17fc27360c255c3e3a882f32306a1da8ea54ab6ce16683006d8f1f9e13581"
  },
  {
    "source": "lean/PNP/NANDGuardedSpineSupportMinimum.lean",
    "namespace": "PNP.DirectWire.GuardedSpineSupportMinimum",
    "names": [
      "PNP.DirectWire.GuardedSpineSupportMinimum.first_only_minimum",
      "PNP.DirectWire.GuardedSpineSupportMinimum.both_ends_minimum",
      "PNP.DirectWire.GuardedSpineSupportMinimum.proper_minimum"
    ],
    "auditFile": "lean-audit/PNPGuardedSpineSupportMinimumAxiomAudit.lean",
    "fixtureFile": "lean-regression/PNPGuardedSpineSupportMinimumProbe.lean",
    "fixtureNames": [
      "PNP.DirectWire.GuardedSpineSupportMinimumProbe.general_first_only_minimum",
      "PNP.DirectWire.GuardedSpineSupportMinimumProbe.general_both_ends_minimum",
      "PNP.DirectWire.GuardedSpineSupportMinimumProbe.general_proper_minimum",
      "PNP.DirectWire.GuardedSpineSupportMinimumProbe.first_only_disconnected",
      "PNP.DirectWire.GuardedSpineSupportMinimumProbe.both_ends_disconnected",
      "PNP.DirectWire.GuardedSpineSupportMinimumProbe.repeated_both_ends",
      "PNP.DirectWire.GuardedSpineSupportMinimumProbe.one_gate_initial_support",
      "PNP.DirectWire.GuardedSpineSupportMinimumProbe.full_selection_excluded_and_nonminimum"
    ],
    "fixtureContractSha256": "83a6d9e698f4840c3c68b45b7d148baa8cfe1c12fe82bcc0df77180af938be09"
  },
  {
    "source": "lean/PNP/NANDGuardedSpineBoundedQuiet.lean",
    "namespace": "PNP.DirectWire.GuardedSpineBoundedQuiet",
    "names": [
      "PNP.DirectWire.GuardedSpineBoundedQuiet.proper_of_small_support",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.bounded_quiet",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.scan_none",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.quiet_with_strict_gain",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.quiet_nonminimum_exists",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.no_uniform_zero_slack_limit"
    ],
    "auditFile": "lean-audit/PNPGuardedSpineBoundedQuietAxiomAudit.lean",
    "fixtureFile": "lean-regression/PNPGuardedSpineBoundedQuietProbe.lean",
    "fixtureNames": [
      "PNP.DirectWire.GuardedSpineBoundedQuietProbe.general_proper_count",
      "PNP.DirectWire.GuardedSpineBoundedQuietProbe.all_records_bounded_quiet",
      "PNP.DirectWire.GuardedSpineBoundedQuietProbe.actual_schedule_none",
      "PNP.DirectWire.GuardedSpineBoundedQuietProbe.every_cap_strict_counterexample",
      "PNP.DirectWire.GuardedSpineBoundedQuietProbe.every_cap_nonminimum_exists",
      "PNP.DirectWire.GuardedSpineBoundedQuietProbe.no_uniform_cap",
      "PNP.DirectWire.GuardedSpineBoundedQuietProbe.zero_cap_counterexample",
      "PNP.DirectWire.GuardedSpineBoundedQuietProbe.disconnected_support_cap"
    ],
    "fixtureContractSha256": "12ea21f14ecaa34eb99d04a9fb9aef8429e02d4a797402629df56bce10b8ac7a"
  }
];
const read0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const digest0 = source => createHash('sha256')
  .update(stripLeanCommentsAndStrings0(source).replace(/\s+/gu, ' ').trim()).digest('hex');
const printed0 = source => [...source.matchAll(/^#print axioms (\S+)$/gmu)].map(row => row[1]);

function inspect0(spec, source) {
  const issues = [];
  const clean = stripLeanCommentsAndStrings0(source);
  if (hasLeanAssumptionDeclaration0(source)) issues.push('assumption declaration');
  if (hasUnauditedLeanDeclarationForm0(source)) issues.push('unaudited declaration');
  if (/\b(?:sorry|admit|unsafe|native_decide|Classical|noncomputable|implemented_by|csimp)\b|decide\s+\+native/u.test(clean))
    issues.push('unchecked authority');
  if (JSON.stringify(explicitLeanDeclarationHeads0(source).map(({kind, name}) => [kind, name])) !==
      JSON.stringify(spec.heads)) issues.push('changed public interface');
  if (digest0(source) !== spec.sourceContractSha256) issues.push('changed reviewed contract');
  return issues;
}
async function reject0(module, mutations) {
  const spec = SPECS.find(row => row.file === 'lean/PNP/' + module + '.lean');
  assert.ok(spec, module);
  const source = await read0(spec.file);
  assert.deepEqual(inspect0(spec, source), []);
  for (const [label, before, after] of mutations) {
    assert.ok(source.includes(before), 'mutation anchor absent: ' + label);
    const changed = source.replace(before, () => after);
    assert.notEqual(changed, source, label);
    assert.ok(inspect0(spec, changed).length > 0, 'accepted mutation: ' + label);
  }
}
test('fixed-window obstruction retains reviewed general sources and allows prose-only changes', async () => {
  for (const spec of SPECS) {
    const source = await read0(spec.file);
    assert.deepEqual(inspect0(spec, source), [], spec.file);
    assert.deepEqual(inspect0(spec, source + '\n/- explanatory prose -/\n'), [], spec.file);
  }
});
test('fixed-window obstruction rejects assumptions, native authority and added public premises', async () => {
  for (const spec of SPECS) {
    const source = await read0(spec.file);
    for (const extra of [
      'axiom suppliedMinimum : True', 'private axiom suppliedCoverage : True',
      'opaque suppliedMinimum : True', 'theorem invented : True := by sorry',
      'theorem nativeAuthority : True := by native_decide', 'variable (suppliedMinimum : Prop)',
    ]) assert.ok(inspect0(spec, source + '\n' + extra + '\n').length > 0, spec.file);
  }
});
test('fixed-window obstruction keeps arbitrary proper supports and arbitrary competitor sizes', async () => {
  await reject0('NANDGuardedSpineSupportMinimum', [
    ['all family sizes', 'theorem proper_minimum (n : Nat)', 'theorem proper_minimum (n : Fin 10)'],
    ['all record widths', 'variable {profileWidth : Nat}', 'abbrev profileWidth := 0'],
    ['all candidate sizes', '(gates : Nat)', '(gates : Fin 10)'],
    ['proper selection, not an interval', '(proper : ∃ node, terminalGateSelected records node = false)',
      '(proper : ∃ node, terminalGateSelected records node = false) (contiguous : records.length = 1)'],
    ['no supplied minimum', 'theorem proper_minimum (n : Nat)',
      'theorem proper_minimum (n : Nat) (suppliedMinimum : False)'],
    ['exact gate lower bound', ').gateCount ≤ gates := by', ').gateCount ≤ gates + 1 := by'],
  ]);
});
test('fixed-window obstruction keeps output occurrences and the joint two-extra bound', async () => {
  await reject0('NANDJointAsymmetricBound', [
    ['two positions, not two different values', '(different : first ≠ second)',
      '(different : items.get first ≠ items.get second)'],
    ['all demanded occurrences', '(List.ofFn word.source)', '(List.ofFn word.source).dedup'],
    ['full joint lower bound', 'inputs + 2 ≤ outputs + gates', 'inputs + 1 ≤ outputs + gates'],
  ]);
});
test('fixed-window obstruction rejects finite-cap substitution and weaker residual claims', async () => {
  await reject0('NANDGuardedSpineBoundedQuiet', [
    ['unbounded cap', 'theorem quiet_with_strict_gain (limit : Nat)', 'theorem quiet_with_strict_gain (limit : Fin 10)'],
    ['all source dimensions', '∀ (inputs gates outputs : Nat)', '∀ (inputs gates outputs : Fin 10)'],
    ['strict residual witness', '0 < residualSlack', '0 ≤ residualSlack'],
    ['strict physical gain', 'StrictEquivalentGain', 'Equivalent'],
    ['literal scheduled scan', 'scan (candidate n) (windowsFrom (n + 2) limit 0) = none', '(none : Option Nat) = none'],
    ['no uniform limit', '¬ ∃ limit : Nat', '¬ ∃ limit : Fin 10'],
    ['no supplied coverage', 'theorem no_uniform_zero_slack_limit :', 'theorem no_uniform_zero_slack_limit (coverage : False) :'],
  ]);
});
test('fixed-window obstruction protects all-record quietness and actual acceptance', async () => {
  await reject0('NANDCompleteBoundedWindowSearch', [
    ['all record widths', '∀ (width : Nat) (records : List', '∀ (width : Fin 1) (records : List'],
    ['complete bounded class', '.gateCount ≤ limit →', '.gateCount = limit →'],
    ['actual validity predicate', '¬PhysicalWindowSearch.Valid candidate records offered', 'False'],
    ['exact scheduled silence', '= none ↔ BoundedQuiet candidate limit', '= none → BoundedQuiet candidate limit'],
  ]);
  await reject0('NANDBoundedPhysicalWindowSearch', [
    ['strict replacement size', 'offered.gateCount < (extractTerminalSupport', 'offered.gateCount ≤ (extractTerminalSupport'],
    ['independent-boundary semantics', 'Equivalent offered.candidate.program', 'True ∧ Equivalent offered.candidate.program'],
    ['actual original interface', 'ArbitrarySupportSplice.CausalInterfaceBound candidate records offered.candidate', 'True'],
  ]);
  await reject0('NANDGuardedSpineFamily', [
    ['literal guarded construction', '⟨.input 0, (core n).2⟩', '⟨.constant false, (core n).2⟩'],
    ['all-input semantic equivalence', 'theorem equivalent (n : Nat)', 'theorem equivalent (n : Fin 3)'],
    ['whole saving', 'n + 2 < (n + 2) + 2', 'n + 2 ≤ (n + 2) + 2'],
  ]);
});
test('fixed-window obstruction audits every conclusion and retains general and hostile kernel probes', async () => {
  const root = await read0('lean/PNP.lean');
  assert.equal(root.split('\n').filter(line => line === 'import PNP.NANDGuardedSpineBoundedQuiet').length, 1);
  assert.equal(STAGES.reduce((count, stage) => count + stage.names.length, 0), 13);
  assert.equal(STAGES.reduce((count, stage) => count + stage.fixtureNames.length, 0), 23);
  for (const stage of STAGES) {
    const spec = SPECS.find(row => row.file === stage.source);
    assert.deepEqual(spec.heads.filter(([kind]) => kind === 'theorem')
      .map(([, name]) => stage.namespace + '.' + name).sort(), stage.names.slice().sort());
    const audit = await read0(stage.auditFile), fixture = await read0(stage.fixtureFile);
    assert.match(audit, /^import PNP\n/u);
    assert.match(fixture, /^import PNP\n/u);
    assert.deepEqual(printed0(audit).sort(), stage.names.slice().sort());
    assert.deepEqual(printed0(fixture).sort(), stage.fixtureNames.slice().sort());
    assert.equal(digest0(fixture), stage.fixtureContractSha256, stage.fixtureFile);
    assert.doesNotMatch(stripLeanCommentsAndStrings0(fixture),
      /\b(?:sorry|admit|native_decide|unsafe|Classical)\b|decide\s+\+native|#(?:eval|reduce)/u);
  }
});
test('fixed-window obstruction remains in durable read-only verification', async () => {
  const workflow = await read0('.github/workflows/lean-bridge.yml');
  const verifier = await import('../scripts/pnp-verify-all.mjs');
  for (const file of [
    'audits/lean-fixed-window-coverage-obstruction0.test.mjs',
    'audits/lean-fixed-window-coverage-obstruction-publication0.test.mjs',
  ]) assert.ok(verifier.CURRENT_VERIFICATION_TESTS0.includes(file), file);
  for (const command of [
    'for name in JointAsymmetricBound GuardedSpineSupportMinimum GuardedSpineBoundedQuiet GrowingWindowUniverseBound; do',
    'node scripts/check-lean-axioms.mjs "lean-audit/PNP${name}AxiomAudit.lean"',
    'lake env lean -DwarningAsError=true "lean-regression/PNP${name}Probe.lean"',
    'node --test audits/lean-{fixed-window-coverage-obstruction,growing-window-universe-bound}{0,-publication0}.test.mjs',
  ]) assert.ok(workflow.includes(command), command);
});
test('fixed-window obstruction documentation preserves the exact limitation and awards no credit', async () => {
  const doc = (await read0('docs/lean_fixed_window_coverage_obstruction.md')).replace(/\s+/gu, ' ');
  for (const text of [
    'every fixed circuit-independent support cap', 'every proper extracted support',
    'No positive publication row or fixed checkpoint is awarded',
    'does not decide P versus NP', 'does not exclude growing windows or global transformations',
    'not a complete polynomial-runtime theorem',
    'Formal artefact coverage:', 'Risk-weighted proof completion estimate:',
    'Uncertainty range:', 'Global gates closed:',
  ]) assert.ok(doc.includes(text), text);
});

test('fixed-window obstruction active documentation and report template retain the correction', async () => {
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md']) {
    const source = (await read0(file)).replace(/\s+/gu, ' ');
    assert.ok(source.includes('No fixed circuit-independent support cap certifies global minimality'), file);
    assert.ok(source.includes('lean_fixed_window_coverage_obstruction.md'), file);
    assert.ok(source.includes('This does not decide P versus NP or exclude growing windows'), file);
  }
  const template = (await read0('publication/canonical_proof_report.template.tex')).replace(/\s+/gu, ' ');
  assert.ok(template.includes('\\subsection{Fixed windows do not certify global minimality}'));
  assert.ok(template.includes('every proper extracted support is minimum'));
  assert.ok(template.includes('not a complete polynomial-runtime theorem'));
  assert.ok(template.includes('No positive publication row or fixed checkpoint is awarded'));
});
