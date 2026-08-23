import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  explicitLeanDeclarationHeads0,
  hasLeanAssumptionDeclaration0,
  hasUnauditedLeanDeclarationForm0,
  stripLeanCommentsAndStrings0,
} from './lean-source-declarations0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const MODULE = 'lean/PNP/Concrete/CNFToNAND.lean';
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteCNFToNANDAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCNFToNAND.lean';
const DOCS =
  'docs/lean_concrete_cnf_to_nand_semantic_compiler.md';
const TEST = 'audits/lean-concrete-cnf-to-nand0.test.mjs';
const NAMESPACE = 'PNP.Concrete.CNFToNAND';

const REUSED_DECLARATIONS = Object.freeze([
  'PNP.Concrete.CNFFormula',
  'PNP.Concrete.CNFFormula.Satisfied',
  'PNP.Concrete.CNFFormula.Satisfiable',
  'PNP.Concrete.CNFSAT',
  'PNP.Concrete.encodeCNF',
  'PNP.Concrete.decodeEncodedCNF',
  'PNP.Concrete.decodeEncodedCNF_canonical',
  'PNP.Concrete.checkCNF_eq_true_iff',
  'PNP.Concrete.LockedNAND.RawCircuit',
  'PNP.Concrete.LockedNAND.encodeCircuit',
  'PNP.Concrete.LockedNAND.decodeValidCircuit',
  'PNP.Concrete.LockedNAND.EncodedNANDSAT',
  'PNP.Concrete.LockedNAND.EncodedLockedNANDThreshold',
  'PNP.Concrete.LockedNAND.buildLockedNANDInstance',
  'PNP.Concrete.LockedNAND.buildLockedNANDInstance_correct',
  'PNP.Concrete.NatPolynomial',
]);

const PUBLIC_DECLARATIONS = Object.freeze([
  `${NAMESPACE}.literalCount`,
  `${NAMESPACE}.validNegativeLiteralCount`,
  `${NAMESPACE}.encodeCNF_of_decodeEncodedCNF`,
  `${NAMESPACE}.compiledFormulaCircuit`,
  `${NAMESPACE}.compileFormula`,
  `${NAMESPACE}.CompilationAction`,
  `${NAMESPACE}.CompilationState`,
  `${NAMESPACE}.CompilationAction.step`,
  `${NAMESPACE}.runCompilationPlan`,
  `${NAMESPACE}.literalPlan`,
  `${NAMESPACE}.literalPlan_of_out_of_range`,
  `${NAMESPACE}.clausePlan`,
  `${NAMESPACE}.clausePlan_empty`,
  `${NAMESPACE}.clausePlan_cons`,
  `${NAMESPACE}.clausesPlan`,
  `${NAMESPACE}.clausesPlan_empty`,
  `${NAMESPACE}.clausesPlan_cons`,
  `${NAMESPACE}.formulaPlan`,
  `${NAMESPACE}.formulaPlan_empty`,
  `${NAMESPACE}.formulaPlan_single_empty_clause`,
  `${NAMESPACE}.formulaPlan_length_exact`,
  `${NAMESPACE}.formulaPlan_length_le`,
  `${NAMESPACE}.formulaPlan_length_le_encoded_bits`,
  `${NAMESPACE}.finalizeCompilation`,
  `${NAMESPACE}.executeFormulaPlan`,
  `${NAMESPACE}.emitFormulaPlan`,
  `${NAMESPACE}.executeFormulaPlan_exact`,
  `${NAMESPACE}.emitFormulaPlan_exact`,
  `${NAMESPACE}.executeFormulaPlan_empty_formula`,
  `${NAMESPACE}.executeFormulaPlan_single_empty_clause`,
  `${NAMESPACE}.compileFormula_inputCount`,
  `${NAMESPACE}.compileFormula_output_is_gate`,
  `${NAMESPACE}.compileFormula_wellFormed`,
  `${NAMESPACE}.decodeValidCircuit_encode_compileFormula`,
  `${NAMESPACE}.compiledFormulaCircuit_eval_eq_true_iff`,
  `${NAMESPACE}.compiledFormulaCircuit_satisfiable_iff`,
  `${NAMESPACE}.compileFormula_satisfiable_iff`,
  `${NAMESPACE}.formula_satisfiable_iff_encoded_compileFormula`,
  `${NAMESPACE}.compileFormula_gateCount_exact`,
  `${NAMESPACE}.executeFormulaPlan_gateCount_exact`,
  `${NAMESPACE}.compileFormula_gateCount_le`,
  `${NAMESPACE}.cnfToNANDOutputSizePolynomial`,
  `${NAMESPACE}.cnfToNANDOutputSizePolynomial_eval`,
  `${NAMESPACE}.compileEncodedCNFToNAND`,
  `${NAMESPACE}.compileEncodedCNFToNAND_of_decoded`,
  `${NAMESPACE}.emitFormulaPlan_eq_compileEncodedCNFToNAND_of_decoded`,
  `${NAMESPACE}.compileEncodedCNFToNAND_of_malformed`,
  `${NAMESPACE}.compileEncodedCNFToNAND_size_le`,
  `${NAMESPACE}.empty_not_encodedNANDSAT`,
  `${NAMESPACE}.compileEncodedCNFToNAND_correct`,
  `${NAMESPACE}.buildLockedNANDFromCNF`,
  `${NAMESPACE}.buildLockedNANDFromCNF_correct`,
]);

const MILESTONE_THEOREMS = Object.freeze([
  `${NAMESPACE}.encodeCNF_of_decodeEncodedCNF`,
  `${NAMESPACE}.compileFormula_inputCount`,
  `${NAMESPACE}.compileFormula_output_is_gate`,
  `${NAMESPACE}.compileFormula_wellFormed`,
  `${NAMESPACE}.decodeValidCircuit_encode_compileFormula`,
  `${NAMESPACE}.compiledFormulaCircuit_eval_eq_true_iff`,
  `${NAMESPACE}.compiledFormulaCircuit_satisfiable_iff`,
  `${NAMESPACE}.compileFormula_satisfiable_iff`,
  `${NAMESPACE}.formula_satisfiable_iff_encoded_compileFormula`,
  `${NAMESPACE}.compileFormula_gateCount_exact`,
  `${NAMESPACE}.compileFormula_gateCount_le`,
  `${NAMESPACE}.cnfToNANDOutputSizePolynomial_eval`,
  `${NAMESPACE}.compileEncodedCNFToNAND_of_decoded`,
  `${NAMESPACE}.compileEncodedCNFToNAND_of_malformed`,
  `${NAMESPACE}.compileEncodedCNFToNAND_size_le`,
  `${NAMESPACE}.empty_not_encodedNANDSAT`,
  `${NAMESPACE}.compileEncodedCNFToNAND_correct`,
  `${NAMESPACE}.buildLockedNANDFromCNF_correct`,
]);

async function text0(relativePath) {
  return readFile(path.join(ROOT, relativePath), 'utf8');
}

function imports0(source) {
  return [...source.matchAll(/^\s*import\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function printed0(source) {
  return [...source.matchAll(/^#print axioms\s+([^\s]+)\s*$/gmu)]
    .map((match) => match[1]);
}

function compact0(source) {
  return stripLeanCommentsAndStrings0(source)
    .replace(/\s+/gu, ' ')
    .trim();
}

function declarationBody0(source, name) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const startPattern = new RegExp(
    `^[ \\t]*(?:private[ \\t]+)?def[ \\t]+${name.replaceAll('.', '\\.')}\\b`,
    'mu',
  );
  const start = stripped.search(startPattern);
  if (start < 0) return '';
  const after = stripped.slice(start + 1);
  const next = after.search(
    /^(?:private\s+)?(?:def|theorem|inductive|structure|abbrev)\s+/mu,
  );
  return next < 0 ? stripped.slice(start) : stripped.slice(start, start + 1 + next);
}

function validateSource0(source) {
  const failures = [];
  const stripped = stripLeanCommentsAndStrings0(source);
  const compact = compact0(source);

  if (hasLeanAssumptionDeclaration0(source)) failures.push('assumption');
  if (hasUnauditedLeanDeclarationForm0(source)) {
    failures.push('declaration-form');
  }
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|bv_decide|sat_decide|SATOracle|Classical(?:\.choice)?|choice)\b/u
    .test(stripped)) {
    failures.push('shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)
      || /\b(?:hostLookup|hostSideLookup|scheduleLookup|hostDecoder|hostSchedule|scheduleOracle|precomputedSchedule)\b/u
        .test(stripped)) {
    failures.push('host-lookup');
  }
  if (/\b(?:callerCertificate|executionCertificate|traceCertificate|proofCertificate|trustFlag)\b/u
    .test(stripped)) {
    failures.push('caller-certificate');
  }
  if (/\b(?:PolynomialReduction|PolynomialTimeFunction|RawRefinement|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(stripped)) {
    failures.push('overclaim');
  }

  for (const name of [
    'literalExpression',
    'clauseExpression',
    'clausesExpression',
    'compileExpression',
    'compiledFormulaCircuit',
    'compileFormula',
    'compileEncodedCNFToNAND',
  ]) {
    const body = declarationBody0(source, name);
    if (body === ''
        || /\b(?:CNFSAT|EncodedNANDSAT|Satisfiable|referenceMinimum|decide)\b/u
          .test(body)) {
      failures.push('answer-independent-compiler');
    }
  }

  if (!compact.includes(
    'private def literalExpression (inputs : Nat) (literal : CNFLiteral) : BoolExpression inputs := if valid : literal.variableIndex < inputs then')
      || !compact.includes('else .constant false')) {
    failures.push('out-of-range-false');
  }
  if (!compact.includes(
    'private def clauseExpression (inputs : Nat) : List CNFLiteral → BoolExpression inputs | [] => .constant false')
      || !compact.includes(
        'private def clausesExpression (inputs : Nat) : List (List CNFLiteral) → BoolExpression inputs | [] => .constant true')) {
    failures.push('cnf-identities');
  }
  if (!compact.includes(
    '| .neg body => (compileExpression body).negate')
      || !compact.includes(
        '(compileExpression left) (compileExpression right)).nand.negate')
      || !compact.includes(
        '(compileExpression left).negate (compileExpression right).negate).nand')
      || !compact.includes('appendSubstituted')) {
    failures.push('nand-construction');
  }
  if (!compact.includes(
    'def compileEncodedCNFToNAND (bits : BitString) : BitString := match decodeEncodedCNF bits with | none => [] | some formula => LockedNAND.encodeCircuit (compileFormula formula)')) {
    failures.push('fail-closed-codec');
  }
  if (!compact.includes(
    'theorem compileFormula_gateCount_exact (formula : CNFFormula) : (compileFormula formula).gates.length = validNegativeLiteralCount formula + 3 * literalCount formula + 2 * formula.clauses.length + (if formula.clauses.isEmpty then 1 else 0)')) {
    failures.push('exact-gate-count');
  }
  if (!compact.includes(
    '4 * ((5 * (bitLength + 1)) * (15 * (bitLength + 1)) + 19 * (bitLength + 1))')) {
    failures.push('polynomial-bound');
  }
  if (!compact.includes(
    'theorem compileEncodedCNFToNAND_correct (bits : BitString) : CNFSAT bits ↔ LockedNAND.EncodedNANDSAT (compileEncodedCNFToNAND bits)')) {
    failures.push('semantic-equivalence');
  }
  if (!compact.includes(
    'theorem buildLockedNANDFromCNF_correct (bits : BitString) : CNFSAT bits ↔ LockedNAND.EncodedLockedNANDThreshold (buildLockedNANDFromCNF bits)')) {
    failures.push('threshold-composition');
  }
  return [...new Set(failures)];
}

test('module is a universal typed NAND compiler with the exact public surface',
  async () => {
    const source = await text0(MODULE);
    assert.deepEqual(imports0(source), [
      'PNP.Concrete.CNF',
      'PNP.Concrete.LockedNANDReduction',
      'PNP.NANDComposition',
    ]);
    assert.deepEqual(validateSource0(source), []);
    assert.deepEqual(
      explicitLeanDeclarationHeads0(source)
        .map(({ kind, name }) => [kind, name]),
      [
        ['def', 'literalCount'],
        ['def', 'validNegativeLiteralCount'],
        ['theorem', 'encodeCNF_of_decodeEncodedCNF'],
        ['def', 'compiledFormulaCircuit'],
        ['def', 'compileFormula'],
        ['inductive', 'CompilationAction'],
        ['structure', 'CompilationState'],
        ['def', 'CompilationAction.step'],
        ['def', 'runCompilationPlan'],
        ['def', 'literalPlan'],
        ['theorem', 'literalPlan_of_out_of_range'],
        ['def', 'clausePlan'],
        ['theorem', 'clausePlan_empty'],
        ['theorem', 'clausePlan_cons'],
        ['def', 'clausesPlan'],
        ['theorem', 'clausesPlan_empty'],
        ['theorem', 'clausesPlan_cons'],
        ['def', 'formulaPlan'],
        ['theorem', 'formulaPlan_empty'],
        ['theorem', 'formulaPlan_single_empty_clause'],
        ['theorem', 'formulaPlan_length_exact'],
        ['theorem', 'formulaPlan_length_le'],
        ['theorem', 'formulaPlan_length_le_encoded_bits'],
        ['def', 'finalizeCompilation'],
        ['def', 'executeFormulaPlan'],
        ['def', 'emitFormulaPlan'],
        ['theorem', 'executeFormulaPlan_exact'],
        ['theorem', 'emitFormulaPlan_exact'],
        ['theorem', 'executeFormulaPlan_empty_formula'],
        ['theorem', 'executeFormulaPlan_single_empty_clause'],
        ['theorem', 'compileFormula_inputCount'],
        ['theorem', 'compileFormula_output_is_gate'],
        ['theorem', 'compileFormula_wellFormed'],
        ['theorem', 'decodeValidCircuit_encode_compileFormula'],
        ['theorem', 'compiledFormulaCircuit_eval_eq_true_iff'],
        ['theorem', 'compiledFormulaCircuit_satisfiable_iff'],
        ['theorem', 'compileFormula_satisfiable_iff'],
        ['theorem', 'formula_satisfiable_iff_encoded_compileFormula'],
        ['theorem', 'compileFormula_gateCount_exact'],
        ['theorem', 'executeFormulaPlan_gateCount_exact'],
        ['theorem', 'compileFormula_gateCount_le'],
        ['def', 'cnfToNANDOutputSizePolynomial'],
        ['theorem', 'cnfToNANDOutputSizePolynomial_eval'],
        ['def', 'compileEncodedCNFToNAND'],
        ['theorem', 'compileEncodedCNFToNAND_of_decoded'],
        ['theorem',
          'emitFormulaPlan_eq_compileEncodedCNFToNAND_of_decoded'],
        ['theorem', 'compileEncodedCNFToNAND_of_malformed'],
        ['theorem', 'compileEncodedCNFToNAND_size_le'],
        ['theorem', 'empty_not_encodedNANDSAT'],
        ['theorem', 'compileEncodedCNFToNAND_correct'],
        ['def', 'buildLockedNANDFromCNF'],
        ['theorem', 'buildLockedNANDFromCNF_correct'],
      ],
    );
  });

test('axiom transcript covers every new and reused boundary declaration',
  async () => {
    const audit = await text0(AXIOM_AUDIT);
    assert.deepEqual(imports0(audit), ['PNP.Concrete.CNFToNAND']);
    assert.deepEqual(printed0(audit), [
      ...REUSED_DECLARATIONS,
      ...PUBLIC_DECLARATIONS,
    ]);
    assert.equal(new Set(printed0(audit)).size, 68);

    const inventory = JSON.parse(
      await text0('status/LEAN_THEOREM_INVENTORY.json'),
    );
    const rows = new Map(
      inventory.declarations.map((entry) => [entry.name, entry]),
    );
    for (const name of [...REUSED_DECLARATIONS, ...PUBLIC_DECLARATIONS]) {
      const row = rows.get(name);
      assert.notEqual(row, undefined, name);
      assert.equal(
        row.axioms.every((axiom) =>
          ['Quot.sound', 'propext'].includes(axiom)),
        true,
        `${name}:${row.axioms.join(',')}`,
      );
    }
  });

test('regression fixes edge semantics, exact counts, and universal boundaries',
  async () => {
    const regression = await text0(REGRESSION);
    for (const fragment of [
      'emptyFormula',
      'emptyClauseFormula',
      'positiveFormula',
      'negativeFormula',
      'outOfRangePositiveFormula',
      'outOfRangeNegativeFormula',
      'tautologyFormula',
      'contradictionFormula',
      'duplicateMultiClauseFormula',
      '(compileFormula emptyFormula).gates.length = 1',
      '(compileFormula emptyClauseFormula).gates.length = 2',
      '(compileFormula positiveFormula).gates.length = 5',
      '(compileFormula negativeFormula).gates.length = 6',
      'formulaPlan emptyFormula',
      'executeFormulaPlan_exact',
      'emitFormulaPlan_exact',
      'executeFormulaPlan_gateCount_exact',
      'emitFormulaPlan_eq_compileEncodedCNFToNAND_of_decoded',
      'decodeEncodedCNF_canonical',
      'encodeCNF_of_decodeEncodedCNF',
      'decodeValidCircuit_encode_compileFormula',
      'compileEncodedCNFToNAND [] = []',
      'compileEncodedCNFToNAND_size_le',
      'compileEncodedCNFToNAND_correct',
      'buildLockedNANDFromCNF_correct',
    ]) assert.equal(regression.includes(fragment), true, fragment);
    assert.doesNotMatch(
      stripLeanCommentsAndStrings0(regression),
      /\b(?:sorry|admit|axiom|unsafe|native_decide|bv_decide|sat_decide|SATOracle|Classical(?:\.choice)?|choice)\b/u,
    );
  });

test('root, status, milestone, workflow, and documentation publish only the semantic boundary',
  async () => {
    const [root, status, map, workflow, docs, packageJson, verifier] =
      await Promise.all([
        text0('lean/PNP.lean'),
        text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
        text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
        text0('.github/workflows/lean-bridge.yml'),
        text0(DOCS),
        text0('package.json').then(JSON.parse),
        text0('scripts/pnp-verify-all.mjs'),
      ]);

    assert.match(root, /^import PNP\.Concrete\.CNFToNAND$/mu);
    for (const field of [
      'leanConcreteCNFToNANDSemanticCompilerFormalized',
      'leanConcreteCNFToNANDSemanticCompilerAxiomAuditPassed',
      'leanConcreteCNFToNANDExactCodecCanonicalityFormalized',
      'leanConcreteCNFToNANDTypedTopologicalCompilationFormalized',
      'leanConcreteCNFToNANDWellFormedOutputFormalized',
      'leanConcreteCNFToNANDExactSemanticsFormalized',
      'leanConcreteCNFToNANDEdgeSemanticsFormalized',
      'leanConcreteCNFToNANDExactGateCountFormalized',
      'leanConcreteCNFToNANDPolynomialOutputSizeBoundFormalized',
      'leanConcreteCNFToNANDAllBitstringFailClosedFormalized',
      'leanConcreteCNFToNANDLockedThresholdCompositionFormalized',
    ]) assert.equal(status[field], true, field);
    assert.equal(
      status.leanConcreteCNFToNANDSemanticCompilerAuditedDeclarationCount,
      68,
    );
    assert.equal(
      status.leanConcreteCNFToNANDSemanticCompilerScope,
      'strict-canonical-cnf-to-intrinsically-topological-nand-semantic-compiler-with-exact-gate-count-quadratic-output-bound-and-all-bitstring-fail-closed-equivalence',
    );
    assert.equal(
      status.leanConcreteCNFToNANDFiniteMachineFormalized,
      true,
    );
    assert.equal(
      status.leanConcreteCNFToNANDPolynomialTimeFunctionFormalized,
      true,
    );
    assert.equal(status.projectSpecificAxiomInventory.length > 0, status.projectSpecificAxiomsRemaining);
    assert.equal(status.remainingBlockers.length, 5);
    assert.equal(status.rootLeanTheoremPresent, false);
    assert.equal(status.concretePublicationGate.passed, false);

    const milestone = status.formalPublicationMilestones.find(
      ({ id }) => id === 'concrete-cnf-to-nand-semantic-compiler',
    );
    assert.equal(milestone?.earned, true);
    assert.equal(milestone.status, 'formalized-semantic-boundary');
    assert.deepEqual(milestone.requiredTheorems, MILESTONE_THEOREMS);
    for (const name of MILESTONE_THEOREMS) {
      assert.match(
        map.earnedMilestoneTheoremKernelTypeSha256[name],
        /^[0-9a-f]{64}$/u,
        name,
      );
    }
    assert.equal(status.formalPublicationMilestones.find(
      (row) => row.id === 'global-locked-nand-threshold',
    )?.earned, true);
    for (const id of [
      'global-zeroslack-pccmin',
      'concrete-publication-root',
    ]) {
      assert.equal(
        status.formalPublicationMilestones.find(
          (row) => row.id === id,
        )?.earned,
        false,
        id,
      );
    }

    for (const fragment of [
      'PNPConcreteCNFToNANDAxiomAudit.lean',
      'PNPConcreteCNFToNAND.lean',
      'lean-concrete-cnf-to-nand0.test.mjs',
    ]) assert.equal(workflow.includes(fragment), true, fragment);
    assert.equal(packageJson.scripts.test.includes(TEST), true);
    assert.equal(verifier.includes(TEST), true);

    const compactDocs = docs.replaceAll(/\s+/gu, ' ');
    for (const fragment of [
      'generated inventory',
      'publication map',
      'status payload',
      'canonical report artifacts',
      'CNFSAT',
      'EncodedNANDSAT',
      'empty formula',
      'empty clause',
      'out-of-range',
      'quadratic',
      'legacy',
      'finite work machine',
      'P = NP',
    ]) assert.equal(compactDocs.includes(fragment), true, fragment);
  });

test('hostile mutations revoke semantic-compiler credit', async () => {
  const source = await text0(MODULE);

  assert.ok(validateSource0(
    `${source}\naxiom hidden : True\n`,
  ).includes('assumption'));
  assert.ok(validateSource0(
    source.replace('| [] => .constant true', '| [] => .constant false'),
  ).includes('cnf-identities'));
  assert.ok(validateSource0(
    source.replace(
      'private def clauseExpression (inputs : Nat)',
      'private def clauseExpressionAltered (inputs : Nat)',
    ),
  ).includes('cnf-identities'));
  assert.ok(validateSource0(
    source.replace('else\n    .constant false', 'else\n    .constant true'),
  ).includes('out-of-range-false'));
  assert.ok(validateSource0(
    source.replace(')).nand.negate', ')).nand'),
  ).includes('nand-construction'));
  assert.ok(validateSource0(
    source.replace(
      'def compileEncodedCNFToNAND (bits : BitString) : BitString :=\n'
        + '  match decodeEncodedCNF bits with\n'
        + '  | none => []',
      'def compileEncodedCNFToNAND (bits : BitString) : BitString :=\n'
        + '  match decodeEncodedCNF bits with\n'
        + '  | none => [false]',
    ),
  ).includes('fail-closed-codec'));
  assert.ok(validateSource0(
    source.replaceAll('3 * literalCount formula', '2 * literalCount formula'),
  ).includes('exact-gate-count'));
  assert.ok(validateSource0(
    source.replace('15 * (bitLength + 1)', '14 * (bitLength + 1)'),
  ).includes('polynomial-bound'));
  assert.ok(validateSource0(
    source.replace('CNFSAT bits ↔', 'CNFSAT bits →'),
  ).includes('semantic-equivalence'));
  assert.ok(validateSource0(
    `${source}\ndef hostLookup := true\n`,
  ).includes('host-lookup'));
  assert.ok(validateSource0(
    `${source}\ndef callerCertificate := true\n`,
  ).includes('caller-certificate'));
  assert.ok(validateSource0(
    `${source}\ndef PolynomialTimeFunction := True\n`,
  ).includes('overclaim'));
  assert.ok(validateSource0(
    `${source}\ntheorem fake : True := by native_decide\n`,
  ).includes('shortcut'));
});
