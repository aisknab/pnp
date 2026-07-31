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
const AUDIT =
  'lean-audit/PNPConcreteCNFToNANDPolynomialReductionAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteCNFToNANDPolynomialReduction.lean';
const DOCS =
  'docs/lean_concrete_cnf_to_nand_polynomial_reduction.md';
const TEST =
  'audits/lean-concrete-cnf-to-nand-polynomial-reduction0.test.mjs';

const MODULE_STEMS = Object.freeze([
  'CNFSourceParserSpec',
  'CNFSourceParserMachine',
  'CNFSourceParserCorrectness',
  'CNFSourceParserCompiled',
  'CNFToNANDEmitterPlan',
  'CNFToNANDCarrierTokenReader',
  'CNFToNANDCarrierEncoder',
  'CNFToNANDWorkspace',
  'CNFToNANDControllerBlocks',
  'CNFToNANDController',
  'CNFToNANDControllerCanonicalTrace',
  'CNFToNANDControllerCountTrace',
  'CNFToNANDControllerCompletionTrace',
  'CNFToNANDControllerPolynomialBound',
  'CNFToNANDControllerTotalBound',
  'CNFToNANDControllerTotalTrace',
  'CNFToNANDCompilerMachine',
  'CNFToNANDCompilerTrace',
  'CNFToNANDCompilerPolynomialBound',
  'CNFToNANDCompilerTotalTrace',
  'CNFToNANDCompilerCompiled',
  'CNFToNANDPolynomialReduction',
]);

const SOURCE_FILES = Object.freeze(
  MODULE_STEMS.map((stem) => `lean/PNP/Concrete/${stem}.lean`),
);

const MODULE_NAMES = Object.freeze(
  MODULE_STEMS.map((stem) => `PNP.Concrete.${stem}`),
);

const REUSED_DECLARATIONS = Object.freeze([
  'PNP.Concrete.PolynomialReduction',
  'PNP.Concrete.PolynomialReduction.compose',
  'PNP.Concrete.ReducesTo',
  'PNP.Concrete.PolynomialTimeMachine',
  'PNP.Concrete.PolynomialTimeFunction',
  'PNP.Concrete.FunctionProgram.RawRefinement',
  'PNP.Concrete.FunctionProgram.RawRefinement.ofMachine',
  'PNP.Concrete.FunctionProgram.RawRefinement.compose',
  'PNP.Concrete.CNFSAT',
  'PNP.Concrete.LockedNAND.EncodedNANDSAT',
  'PNP.Concrete.LockedNAND.EncodedLockedNANDThreshold',
  'PNP.Concrete.CNFToNAND.cnfToNANDOutputSizePolynomial',
  'PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND',
  'PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_size_le',
  'PNP.Concrete.CNFToNAND.compileEncodedCNFToNAND_correct',
  'PNP.Concrete.CNFToNAND.buildLockedNANDFromCNF',
  'PNP.Concrete.LockedNAND.strictLockedNANDPolynomialReduction',
  'PNP.Concrete.LockedNAND.strictLockedNANDPolynomialReduction_output',
  'PNP.Concrete.LockedNAND.strictLockedNANDPolynomialReduction_correct',
  'PNP.Concrete.LockedNAND.strictLockedNANDPolynomialReduction_rawRefinement',
]);

const MILESTONE_THEOREMS = Object.freeze([
  'PNP.Concrete.CNFSourceParser.allInput_exact',
  'PNP.Concrete.CNFSourceParser.compiledMachineOutput_eq_validatedCNFBytes',
  'PNP.Concrete.CNFSourceParser.compiledBoundedDecide_ne_timeout',
  'PNP.Concrete.CNFToNANDCarrierEncoder.canonical_exact',
  'PNP.Concrete.CNFToNANDCarrierEncoder.canonicalWorkSteps_polynomial_bound',
  'PNP.Concrete.CNFToNANDWorkspace.exact_execution_output',
  'PNP.Concrete.CNFToNANDController.rules_length_literal',
  'PNP.Concrete.CNFToNANDControllerTotalTrace.canonical_path',
  'PNP.Concrete.CNFToNANDControllerTotalTrace.canonical_bounded_exact',
  'PNP.Concrete.CNFToNANDCompilerMachine.rules_length_literal',
  'PNP.Concrete.CNFToNANDCompilerTotalTrace.malformed_bounded_exact',
  'PNP.Concrete.CNFToNANDCompilerTotalTrace.decoded_bounded_exact',
  'PNP.Concrete.CNFToNANDCompilerTotalTrace.allInput_bounded_exact',
  'PNP.Concrete.CNFToNANDCompilerPolynomialBound.allInputWorkTimePolynomial_eval',
  'PNP.Concrete.CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial_eval',
  'PNP.Concrete.CNFToNANDCompilerCompiled.compiledMachineOutput_eq_compileEncodedCNFToNAND',
  'PNP.Concrete.CNFToNANDCompilerCompiled.compiledBoundedDecide_accept_iff',
  'PNP.Concrete.CNFToNANDCompilerCompiled.compiledBoundedDecide_ne_timeout',
  'PNP.Concrete.CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output',
  'PNP.Concrete.CNFToNAND.cnfToNANDPolynomialReduction_function',
  'PNP.Concrete.CNFToNAND.cnfToNANDPolynomialReduction_output',
  'PNP.Concrete.CNFToNAND.cnfToNANDPolynomialReduction_correct',
  'PNP.Concrete.CNFToNAND.cnfSAT_reducesTo_encodedNANDSAT',
  'PNP.Concrete.CNFToNAND.cnfToNANDPolynomialReduction_hasRawRefinement',
  'PNP.Concrete.CNFToNAND.cnfToLockedNANDPolynomialReduction_output',
  'PNP.Concrete.CNFToNAND.cnfToLockedNANDPolynomialReduction_correct',
  'PNP.Concrete.CNFToNAND.cnfSAT_reducesTo_encodedLockedNANDThreshold',
  'PNP.Concrete.CNFToNAND.cnfToLockedNANDPolynomialReduction_hasRawRefinement',
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

function declarationKind0(kind) {
  if (kind === 'theorem') return 'theorem';
  if (kind === 'inductive' || kind === 'structure') return 'inductive';
  return 'definition';
}

function qualifiedSourceHeads0(source) {
  const stripped = stripLeanCommentsAndStrings0(source);
  const declarations = explicitLeanDeclarationHeads0(source);
  const blocks = [...stripped.matchAll(
    /^[ \t]*(namespace|section|end)(?:[ \t]+([^\s]+))?[ \t]*$/gmu,
  )].map((match) => ({
    index: match.index,
    command: match[1],
    name: match[2] ?? null,
  }));
  const events = [
    ...blocks.map((entry) => ({ ...entry, event: 'block' })),
    ...declarations.map((entry) => ({ ...entry, event: 'declaration' })),
  ].sort((left, right) => left.index - right.index);
  const stack = [];
  let currentNamespace = '';
  const out = [];
  for (const event of events) {
    if (event.event === 'declaration') {
      const localName = event.name.replaceAll('«', '').replaceAll('»', '');
      out.push({
        kind: declarationKind0(event.kind),
        name: localName.startsWith('PNP.')
          ? localName
          : `${currentNamespace}.${localName}`,
      });
      continue;
    }
    if (event.command === 'end') {
      const frame = stack.pop();
      assert.notEqual(frame, undefined, `unmatched end ${event.name ?? ''}`);
      currentNamespace = frame.previousNamespace;
      continue;
    }
    stack.push({ previousNamespace: currentNamespace });
    if (event.command === 'namespace') {
      assert.notEqual(event.name, null);
      currentNamespace = event.name.startsWith('PNP.')
        ? event.name
        : currentNamespace === ''
          ? event.name
          : `${currentNamespace}.${event.name}`;
    }
  }
  assert.equal(stack.length, 0, 'unclosed namespace or section');
  return out;
}

function validateSources0(sources) {
  const failures = [];
  for (const [relative, source] of sources) {
    const stripped = stripLeanCommentsAndStrings0(source);
    if (hasLeanAssumptionDeclaration0(source)) {
      failures.push(`${relative}:assumption`);
    }
    if (hasUnauditedLeanDeclarationForm0(source)) {
      failures.push(`${relative}:declaration-form`);
    }
    if (/\b(?:sorry|admit|axiom|unsafe|native_decide|bv_decide|sat_decide|SATOracle|Classical(?:\.choice)?|choice)\b/u
      .test(stripped)) {
      failures.push(`${relative}:shortcut`);
    }
    if (/#(?:eval|reduce|guard|synth)\b/u.test(stripped)
        || /\b(?:hostLookup|hostSideLookup|scheduleLookup|hostDecoder|hostSchedule|scheduleOracle|precomputedSchedule)\b/u
          .test(stripped)) {
      failures.push(`${relative}:host-lookup`);
    }
    if (/\b(?:callerCertificate|executionCertificate|traceCertificate|proofCertificate|trustFlag)\b/u
      .test(stripped)) {
      failures.push(`${relative}:caller-certificate`);
    }
    if (/\b(?:NPComplete|cnfSATInP|p_eq_np)\b/u.test(stripped)) {
      failures.push(`${relative}:overclaim`);
    }
  }

  const byStem = new Map(MODULE_STEMS.map((stem, index) =>
    [stem, compact0(sources[index][1])]));
  const carrier = byStem.get('CNFToNANDCarrierEncoder');
  const controller = byStem.get('CNFToNANDController');
  const machine = byStem.get('CNFToNANDCompilerMachine');
  const polynomial = byStem.get('CNFToNANDCompilerPolynomialBound');
  const total = byStem.get('CNFToNANDCompilerTotalTrace');
  const compiled = byStem.get('CNFToNANDCompilerCompiled');
  const reduction = byStem.get('CNFToNANDPolynomialReduction');

  if (!carrier.includes(
    'theorem rules_length : machine.rules.length = 13844')
      || !controller.includes('def ruleCount : Nat := 121073')
      || !controller.includes(
        'theorem rules_length_literal : machine.rules.length = ruleCount')) {
    failures.push('component-rule-counts');
  }
  if (!machine.includes(
    'def parserRef : NodeRef := { name := 0')
      || !machine.includes(
        'def carrierRef : NodeRef := { name := 1')
      || !machine.includes(
        'def controllerRef : NodeRef := { name := 2')
      || !machine.includes(
        'def parserNode : Node := { name := parserRef.name program := CNFSourceParser.machine onAccept := .node carrierRef onReject := .reject }')
      || !machine.includes(
        'def carrierNode : Node := { name := carrierRef.name program := CNFToNANDCarrierEncoder.machine onAccept := .node controllerRef onReject := .reject }')
      || !machine.includes(
        'def controllerNode : Node := { name := controllerRef.name program := CNFToNANDController.machine onAccept := .accept onReject := .reject }')) {
    failures.push('outer-state-and-bridges');
  }
  if (!machine.includes(
    'def nodes : List Node := [parserNode, carrierNode, controllerNode]')) {
    failures.push('outer-three-node-graph');
  }
  if (!machine.includes('def ruleCount : Nat := 135070')
      || !machine.includes(
        'theorem rules_length_literal : machine.rules.length = ruleCount')) {
    failures.push('outer-rule-count');
  }
  if (!polynomial.includes(
    'CNFToNANDCarrierEncoder.canonicalWorkSteps')
      || polynomial.includes('CNFToNANDCarrierEncoder.plannedWorkSteps')
      || !polynomial.includes(
        'def allInputWorkBound (bitLength : Nat) : Nat := CNFSourceParser.parserWorkBound bitLength + CNFToNANDCarrierEncoder.workPolynomial.eval bitLength + CNFToNANDControllerPolynomialBound.controllerWorkBound bitLength + 3')) {
    failures.push('carrier-exact-cost-boundary');
  }
  if (!total.includes('theorem allInput_bounded_exact')
      || !total.includes(
        '(final.state = machine.acceptState ↔ CNFSourceParser.ValidEncodedCNF bits)')
      || !total.includes(
        '(encodeWorkTape final.tape).outputBits = CNFToNAND.compileEncodedCNFToNAND bits')) {
    failures.push('all-input-exact-boundary');
  }
  if (!compiled.includes(
    'def cnfToNANDPolynomialTimeFunction : PolynomialTimeFunction :=')
      || !compiled.includes(
        'theorem cnfToNANDPolynomialTimeFunction_output')
      || !compiled.includes(
        'def cnfToNANDRawRefinement : FunctionProgram.RawRefinement')) {
    failures.push('compiled-function-boundary');
  }
  if (!reduction.includes(
    'def cnfToNANDPolynomialReduction : PolynomialReduction CNFSAT LockedNAND.EncodedNANDSAT :=')
      || !reduction.includes(
        'rw [ CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output ] exact compileEncodedCNFToNAND_correct bits')) {
    failures.push('direct-reduction-boundary');
  }
  if (!reduction.includes(
    'def cnfToLockedNANDPolynomialReduction : PolynomialReduction CNFSAT LockedNAND.EncodedLockedNANDThreshold := PolynomialReduction.compose cnfToNANDPolynomialReduction LockedNAND.strictLockedNANDPolynomialReduction')
      || !reduction.includes(
        'FunctionProgram.RawRefinement.compose cnfToNANDPolynomialReduction_rawRefinement LockedNAND.strictLockedNANDPolynomialReduction_rawRefinement')) {
    failures.push('composed-reduction-boundary');
  }
  return [...new Set(failures)];
}

test('fixed all-input compiler sources retain the reviewed literal boundary',
  async () => {
    const sources = await Promise.all(SOURCE_FILES.map(async (relative) =>
      [relative, await text0(relative)]));
    assert.deepEqual(validateSources0(sources), []);
    assert.deepEqual(
      imports0(sources.at(-1)[1]),
      [
        'PNP.Concrete.CNFToNANDCompilerCompiled',
        'PNP.Concrete.LockedNANDPolynomialReduction',
      ],
    );
  });

test('axiom transcript covers every new explicit public declaration',
  async () => {
    const [audit, inventory, ...sources] = await Promise.all([
      text0(AUDIT),
      text0('status/LEAN_THEOREM_INVENTORY.json').then(JSON.parse),
      ...SOURCE_FILES.map(text0),
    ]);
    assert.deepEqual(imports0(audit), [
      'PNP.Concrete.CNFToNANDPolynomialReduction',
    ]);
    const printed = printed0(audit);
    assert.deepEqual(
      printed.slice(0, REUSED_DECLARATIONS.length),
      REUSED_DECLARATIONS,
    );
    assert.equal(new Set(printed).size, printed.length);

    const inventoryRows = new Map(
      inventory.declarations.map((entry) => [entry.name, entry]),
    );
    const moduleSet = new Set(MODULE_NAMES);
    const printedNewRows = printed.slice(REUSED_DECLARATIONS.length)
      .map((name) => inventoryRows.get(name));
    assert.equal(printedNewRows.includes(undefined), false);
    assert.equal(
      printedNewRows.every((row) => moduleSet.has(row.module)),
      true,
    );

    let sourceDeclarationCount = 0;
    for (let index = 0; index < MODULE_NAMES.length; index += 1) {
      const expected = qualifiedSourceHeads0(sources[index]);
      sourceDeclarationCount += expected.length;
      const actual = printedNewRows
        .filter((row) => row.module === MODULE_NAMES[index]);
      assert.deepEqual(
        actual
          .map(({ kind, name }) => ({ kind, name }))
          .sort((left, right) => left.name.localeCompare(right.name)),
        expected.sort((left, right) => left.name.localeCompare(right.name)),
        MODULE_NAMES[index],
      );
    }
    assert.equal(
      printed.length,
      REUSED_DECLARATIONS.length + sourceDeclarationCount,
    );
    for (const name of printed) {
      const row = inventoryRows.get(name);
      assert.notEqual(row, undefined, name);
      assert.equal(
        row.axioms.every((axiom) =>
          ['Quot.sound', 'propext'].includes(axiom)),
        true,
        `${name}:${row.axioms.join(',')}`,
      );
    }
  });

test('regression pins totality, edge formulas, compilation, and both reductions',
  async () => {
    const regression = await text0(REGRESSION);
    for (const fragment of [
      'CNFToNANDCompilerMachine.machine.rules.length = 135070',
      'allInputWorkTimePolynomial.eval',
      'compiledRawTimePolynomial.eval',
      'allInput_bounded_exact bits',
      'rawInputWorkTape []',
      'rawInputWorkTape [false]',
      'rawInputWorkTape [true]',
      '[false, false, false]',
      '[false, false, false, false]',
      '[true, true, true, true]',
      'emptyFormula',
      'emptyClauseFormula',
      'positiveFormula',
      'negativeFormula',
      'outOfRangeFormula',
      'mixedFormula',
      'compiledMachineOutput_eq_compileEncodedCNFToNAND',
      'compiledBoundedDecide_accept_iff',
      'compiledBoundedDecide_ne_timeout',
      'cnfToNANDRawRefinement',
      'cnfToNANDPolynomialReduction_function',
      'cnfToNANDPolynomialReduction_output',
      'cnfToNANDPolynomialReduction_correct',
      'cnfSAT_reducesTo_encodedNANDSAT',
      'cnfToNANDPolynomialReduction_rawRefinement',
      'cnfToLockedNANDPolynomialReduction_output',
      'cnfToLockedNANDPolynomialReduction_correct',
      'cnfSAT_reducesTo_encodedLockedNANDThreshold',
      'cnfToLockedNANDPolynomialReduction_rawRefinement',
      'cnfToLockedNANDPolynomialReduction_hasRawRefinement',
    ]) assert.equal(regression.includes(fragment), true, fragment);
    assert.doesNotMatch(
      stripLeanCommentsAndStrings0(regression),
      /\b(?:sorry|admit|axiom|unsafe|native_decide|bv_decide|sat_decide|SATOracle|Classical(?:\.choice)?|choice)\b/u,
    );
  });

test('root, status, workflow, verifier, publication, and docs expose the milestone',
  async () => {
    const [
      root, status, map, workflow, docs, packageJson, verifier, audit,
    ] = await Promise.all([
      text0('lean/PNP.lean'),
      text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
      text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
      text0('.github/workflows/lean-bridge.yml'),
      text0(DOCS),
      text0('package.json').then(JSON.parse),
      text0('scripts/pnp-verify-all.mjs'),
      text0(AUDIT),
    ]);
    assert.match(
      root,
      /^import PNP\.Concrete\.CNFToNANDPolynomialReduction$/mu,
    );
    for (const field of [
      'leanConcreteCNFToNANDFiniteMachineFormalized',
      'leanConcreteCNFToNANDPolynomialTimeFunctionFormalized',
      'leanConcreteCNFToNANDPolynomialReductionFormalized',
      'leanConcreteCNFToNANDPolynomialReductionAxiomAuditPassed',
      'leanConcreteCNFToNANDAllInputExactFormalized',
      'leanConcreteCNFToNANDExactMachineOutputFormalized',
      'leanConcreteCNFToNANDCompiledNonTimeoutFormalized',
      'leanConcreteCNFToNANDRawRefinementFormalized',
      'leanConcreteCNFToNANDDirectReductionFormalized',
      'leanConcreteCNFToNANDLockedReductionCompositionFormalized',
    ]) assert.equal(status[field], true, field);
    assert.equal(
      status.leanConcreteCNFToNANDPolynomialReductionAuditedDeclarationCount,
      printed0(audit).length,
    );
    assert.equal(status.projectSpecificAxiomInventory.length, 4);
    assert.equal(status.remainingBlockers.length, 6);
    assert.equal(status.rootLeanTheoremPresent, false);
    assert.equal(status.concretePublicationGate.passed, false);

    const milestone = status.formalPublicationMilestones.find(
      ({ id }) => id === 'concrete-cnf-to-nand-polynomial-reduction',
    );
    assert.equal(milestone?.earned, true);
    assert.equal(milestone.status, 'formalized-polynomial-reduction');
    assert.deepEqual(milestone.requiredTheorems, MILESTONE_THEOREMS);
    for (const name of MILESTONE_THEOREMS) {
      assert.match(
        map.earnedMilestoneTheoremKernelTypeSha256[name],
        /^[0-9a-f]{64}$/u,
        name,
      );
    }

    assert.equal(
      packageJson.scripts.test.includes(TEST),
      true,
    );
    assert.equal(verifier.includes(TEST), true);
    for (const relative of [AUDIT, REGRESSION, TEST]) {
      assert.equal(workflow.includes(relative), true, relative);
    }
    for (const command of [
      `lake env lean -DwarningAsError=true ${AUDIT}`,
      `lake env lean -DwarningAsError=true ${REGRESSION}`,
      `node --test ${TEST}`,
    ]) {
      assert.equal(
        status.verificationCommands.includes(command),
        true,
        command,
      );
    }
    const compactDocs = compact0(docs);
    for (const phrase of [
      'fixed three-node',
      'every bitstring',
      'PolynomialTimeFunction',
      'PolynomialReduction',
      'RawRefinement',
      'does not itself decide CNF-SAT',
    ]) assert.equal(compactDocs.includes(phrase), true, phrase);
  });

test('hostile mutations revoke all-input compiler and reduction credit',
  async () => {
    const originals = await Promise.all(SOURCE_FILES.map(async (relative) =>
      [relative, await text0(relative)]));
    assert.deepEqual(validateSources0(originals), []);

    const mutate0 = (stem, transform) => originals.map(([relative, source]) =>
      relative.endsWith(`/${stem}.lean`)
        ? [relative, transform(source)]
        : [relative, source]);
    const failures0 = (sources) => validateSources0(sources);

    for (const [label, mutated] of [
      ['axiom', mutate0('CNFToNANDPolynomialReduction',
        (source) => `${source}\naxiom injected : True\n`)],
      ['choice', mutate0('CNFToNANDCompilerCompiled',
        (source) => source.replace(
          'namespace PNP.Concrete.CNFToNANDCompilerCompiled',
          'namespace PNP.Concrete.CNFToNANDCompilerCompiled\n#check Classical.choice',
        ))],
      ['host lookup', mutate0('CNFToNANDCompilerMachine',
        (source) => `${source}\ndef hostLookup := true\n`)],
      ['caller certificate', mutate0('CNFToNANDCompilerTotalTrace',
        (source) => `${source}\ndef callerCertificate := true\n`)],
      ['overclaim', mutate0('CNFToNANDPolynomialReduction',
        (source) => `${source}\ntheorem p_eq_np : True := True.intro\n`)],
      ['outer node removal', mutate0('CNFToNANDCompilerMachine',
        (source) => source.replace(
          '[parserNode, carrierNode, controllerNode]',
          '[parserNode, controllerNode]',
        ))],
      ['state collision', mutate0('CNFToNANDCompilerMachine',
        (source) => source.replace(
          'def controllerRef : NodeRef :=\n  { name := 2',
          'def controllerRef : NodeRef :=\n  { name := 1',
        ))],
      ['bridge shadow', mutate0('CNFToNANDCompilerMachine',
        (source) => source.replace(
          'onAccept := .node controllerRef',
          'onAccept := .node carrierRef',
        ))],
      ['rule-count substitution', mutate0('CNFToNANDCompilerMachine',
        (source) => source.replace('135070', '135069'))],
      ['noncanonical carrier cost',
        mutate0('CNFToNANDCompilerPolynomialBound',
          (source) => source.replaceAll(
            'CNFToNANDCarrierEncoder.canonicalWorkSteps',
            'CNFToNANDCarrierEncoder.plannedWorkSteps',
          ))],
      ['bound component removal',
        mutate0('CNFToNANDCompilerPolynomialBound',
          (source) => source.replace(
            'CNFToNANDControllerPolynomialBound.controllerWorkBound bitLength +\n    3',
            '3',
          ))],
      ['output substitution', mutate0('CNFToNANDCompilerTotalTrace',
        (source) => source.replaceAll(
          'CNFToNAND.compileEncodedCNFToNAND bits',
          'bits',
        ))],
      ['function removal', mutate0('CNFToNANDCompilerCompiled',
        (source) => source.replace(
          'def cnfToNANDPolynomialTimeFunction',
          'def alteredCNFToNANDPolynomialTimeFunction',
        ))],
      ['direct target swap', mutate0('CNFToNANDPolynomialReduction',
        (source) => source.replaceAll(
          'LockedNAND.EncodedNANDSAT',
          'LockedNAND.EncodedLockedNANDThreshold',
        ))],
      ['composition removal', mutate0('CNFToNANDPolynomialReduction',
        (source) => source.replace(
          'PolynomialReduction.compose',
          'PolynomialReduction',
        ))],
      ['raw refinement removal', mutate0('CNFToNANDPolynomialReduction',
        (source) => source.replace(
          'FunctionProgram.RawRefinement.compose',
          'FunctionProgram.RawRefinement',
        ))],
    ]) {
      assert.notDeepEqual(failures0(mutated), [], label);
    }
  });
