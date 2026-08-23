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
const MODULES = Object.freeze([
  'lean/PNP/Concrete/LockedNANDSourceParserSpec.lean',
  'lean/PNP/Concrete/LockedNANDSourceParserSemantics.lean',
  'lean/PNP/Concrete/LockedNANDSourceParserMachine.lean',
  'lean/PNP/Concrete/LockedNANDSourceParserFailureShapes.lean',
  'lean/PNP/Concrete/LockedNANDSourceParserValidTrace.lean',
  'lean/PNP/Concrete/LockedNANDSourceParserTotalTrace.lean',
  'lean/PNP/Concrete/LockedNANDSourceParserCorrectness.lean',
  'lean/PNP/Concrete/LockedNANDSourceParserCompiled.lean',
]);
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteLockedNANDSourceParserAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteLockedNANDSourceParser.lean';
const TEST =
  'audits/lean-concrete-locked-nand-source-parser0.test.mjs';
const PARSER_PREFIX = 'PNP.Concrete.LockedNAND.SourceParser.';

const MILESTONE_THEOREMS = Object.freeze([
  `${PARSER_PREFIX}acceptedTape_outputBits`,
  `${PARSER_PREFIX}allInput_exact`,
  `${PARSER_PREFIX}canonicalSteps_le_validWorkBound`,
  `${PARSER_PREFIX}compiledBoundedDecide_accept_iff`,
  `${PARSER_PREFIX}compiledBoundedDecide_ne_timeout`,
  `${PARSER_PREFIX}compiledMachineOutput_eq_validatedSourceBytes`,
  `${PARSER_PREFIX}compiledStart_blankEquivalent`,
  `${PARSER_PREFIX}decodeCircuitTokens_eq_none_iff_failure`,
  `${PARSER_PREFIX}illFormed_exact`,
  `${PARSER_PREFIX}machine_acceptState_ne_rejectState`,
  `${PARSER_PREFIX}malformed_exact`,
  `${PARSER_PREFIX}rules_length`,
  `${PARSER_PREFIX}rules_pairwise_query_distinct`,
  `${PARSER_PREFIX}statePrograms_length`,
  `${PARSER_PREFIX}validFinalConfiguration_isHalted`,
  `${PARSER_PREFIX}validFinalConfiguration_state`,
  `${PARSER_PREFIX}validRawBound_eq`,
  `${PARSER_PREFIX}validRawTimePolynomial_eval`,
  `${PARSER_PREFIX}validatedSourceBytesPolynomialTimeFunction_output`,
  `${PARSER_PREFIX}wellFormed_exact`,
]);

const MACHINE_INTERFACES = Object.freeze([
  'statePrograms_length',
  'rules_length',
  'rules_pairwise_query_distinct',
  'machine_startState_ne_acceptState',
  'machine_startState_ne_rejectState',
  'machine_acceptState_ne_rejectState',
]);

const FAILURE_INTERFACES = Object.freeze([
  'decodeTokens_eq_none_iff_failure',
  'packedRawBits',
  'boolPairWorkCell',
  'danglingWorkCell',
  'SourcePackedCell',
  'MalformedWorkTail',
  'packedRawBits_encodeTokens_append',
  'TokenDecodeFailure.packedShape',
  'MalformedWorkTail.workTail_eq_packedRawBits',
  'packedRawBits_first_ne_blank',
  'packedRawBits_allSourcePacked',
  'MalformedWorkTail.nonempty',
  'MalformedWorkTail.first_ne_blank',
  'MalformedWorkTail.nonblank',
  'MalformedWorkTail.noBlankZero',
  'MalformedWorkTail.allSourcePacked',
  'packedRawBits_length_le',
  'MalformedWorkTail.length_le_rawTail',
  'decodeNatTokens_eq_none_iff_failure',
  'decodeSourceTokens_eq_none_iff_failure',
  'decodeNGatesTokens_eq_none_iff_failure',
  'decodeCircuitTokens_eq_none_iff_failure',
]);

const TRACE_INTERFACES = Object.freeze([
  'canonicalHeader_exact',
  'canonicalHeader_fixed_exact',
  'constantSource_exact',
  'constantGate_exact',
  'referenceIndexFirst_exact',
  'referenceIndexUnitLaunch_exact',
  'referenceIndexFinishLaunch_exact',
  'referenceConsumeSeekGuard_scan_exact',
  'referenceConsumeGuard_exact',
  'referenceFinishSeekGuard_scan_exact',
  'referenceFinishGuard_exact',
  'inputConsumeCount_exact',
  'inputConsumeCountExhausted_exact',
  'inputReferenceConsumeUnit_exact',
  'inputFinishCheck_exact',
  'inputFinishCheckExhaustedRun_exact',
  'inputFinishReturnGuard_scan_exact',
  'inputFinishRestoreCount_exact',
  'validFinalConfiguration_state',
  'validFinalConfiguration_isHalted',
  'acceptedTape_outputBits',
  'sourceRemainder_exact',
  'source_exact',
  'gateLeftRemainder_exact',
  'gate_exact',
  'gates_exact',
  'programEnd_exact',
  'finalRestore_exact',
  'canonical_exact',
  'cleanupSeekGuard_exact',
  'cleanupRight_erase_exact',
  'cleanupRight_reject_exact',
  'cleanupRight_exact',
  'cleanupRightFinite_exact',
  'guardedCleanup_exact',
  'guardedCleanupFinite_exact',
  'guardedCleanupExplicit_exact',
  'restoredBoundary_exact',
  'workStep_to_accept_predecessor',
  'inputReferenceInRangeSteps_bound',
  'gateReferenceInRangeSteps_bound',
  'sourceSpan',
  'sourceRemainderSteps_bound',
  'sourceSteps_bound',
  'gateWorkspace',
  'gateWorkspace_step',
  'gateSteps_bound',
  'gatesSteps_bound',
  'canonicalSteps_le_validWorkBound',
  'wellFormed_exact',
  'malformed_exact',
  'illFormed_exact',
  'allInput_exact',
]);

const COMPILED_INTERFACES = Object.freeze([
  'validWorkBound',
  'validRawBound',
  'validRawBound_eq',
  'validRawTimePolynomial',
  'validRawTimePolynomial_eval',
  'compiledStart_blankEquivalent',
  'compiledMachineOutput_eq_validatedSourceBytes',
  'compiledBoundedDecide_accept_iff',
  'compiledBoundedDecide_ne_timeout',
  'polynomialTimeMachine',
  'validatedSourceBytesPolynomialTimeFunction',
  'validatedSourceBytesPolynomialTimeFunction_output',
  'validatedSourceBytesRawRefinement',
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

function publicDeclarations0(sources) {
  return sources.flatMap((source, moduleIndex) =>
    explicitLeanDeclarationHeads0(source)
      .map((entry) => ({ ...entry, moduleIndex })));
}

function qualifiedPublicDeclarations0(sources) {
  return sources.flatMap((source, moduleIndex) => {
    const stripped = stripLeanCommentsAndStrings0(source);
    const declarations = explicitLeanDeclarationHeads0(source);
    const namespaceEvents = [
      ...[...stripped.matchAll(
        /^[ \t]*namespace[ \t]+([A-Za-z_][\w.]*)[ \t]*$/gmu,
      )].map((match) => ({
        index: match.index,
        kind: 'namespace',
        name: match[1],
      })),
      ...[...stripped.matchAll(
        /^[ \t]*end(?:[ \t]+[A-Za-z_][\w.]*)?[ \t]*$/gmu,
      )].map((match) => ({
        index: match.index,
        kind: 'end',
      })),
    ].sort((left, right) => left.index - right.index);
    const namespaceStack = [];
    let eventIndex = 0;
    return declarations.map((declaration) => {
      while (eventIndex < namespaceEvents.length
          && namespaceEvents[eventIndex].index < declaration.index) {
        const event = namespaceEvents[eventIndex];
        if (event.kind === 'namespace') namespaceStack.push(event.name);
        else namespaceStack.pop();
        eventIndex += 1;
      }
      const localName = declaration.name.replace(/^«|»$/gu, '');
      const namespace = namespaceStack.join('.');
      return {
        ...declaration,
        moduleIndex,
        qualifiedName: localName.startsWith('PNP.') || namespace === ''
          ? localName
          : `${namespace}.${localName}`,
      };
    });
  });
}

function validateSources0(sources) {
  const failures = [];
  const combined = stripLeanCommentsAndStrings0(sources.join('\n'));
  const compact = compact0(sources.join('\n'));
  const machineSource = sources[2];
  const strippedMachineSource =
    stripLeanCommentsAndStrings0(machineSource);
  const declarationNames = new Set(
    publicDeclarations0(sources).map(({ name }) => name),
  );

  if (sources.some(hasLeanAssumptionDeclaration0)) {
    failures.push('assumption');
  }
  if (sources.some(hasUnauditedLeanDeclarationForm0)) {
    failures.push('declaration-form');
  }
  if (/\b(?:sorry|admit|axiom|unsafe|native_decide|bv_decide|sat_decide|SATOracle|Classical(?:\.choice)?|choice)\b/u
    .test(combined)) {
    failures.push('shortcut');
  }
  if (/#(?:eval|reduce|guard|synth)\b/u.test(combined)
      || /\b(?:hostLookup|hostSideLookup|scheduleLookup|hostDecoder|hostSchedule|scheduleOracle|precomputedSchedule)\b/u
        .test(combined)) {
    failures.push('host-lookup');
  }
  if (/\b(?:callerCertificate|executionCertificate|traceCertificate|proofCertificate|trustFlag)\b/u
    .test(combined)) {
    failures.push('caller-certificate');
  }
  if (/\b(?:PolynomialReduction|NPComplete|cnfSATInP|p_eq_np|LockedNANDThreshold|ResidualBandExactMinimization)\b/u
    .test(combined)) {
    failures.push('overclaim');
  }
  if (/\b(?:decodeTokens|decodeCircuit|decodeElaboratedCircuit|decodeValidCircuit|RawCircuit\.wellFormed|ValidEncodedCircuit|validatedSourceBytes)\b/u
    .test(strippedMachineSource)) {
    failures.push('decoder-in-rule-construction');
  }
  if (!compact.includes('statePrograms.length = 228')
      || !compact.includes('def ruleCount : Nat := 2052')
      || !compact.includes(
        '(programs.flatMap stateRules).length = 9 * programs.length')
      || !compact.includes(
        'def workAlphabet : List WorkSymbol := [cellBlank, leftGuard, cursorMark, countMark, cell00, cell01, gateMark, cell10, cell11]')) {
    failures.push('literal-rule-table');
  }
  for (const name of [
    ...MACHINE_INTERFACES,
    ...FAILURE_INTERFACES,
    ...TRACE_INTERFACES,
    ...COMPILED_INTERFACES,
  ]) {
    if (!declarationNames.has(name)) failures.push('exact-interface');
  }
  if (!compact.includes('.mul (.constant 6)')
      || !compact.includes('(.mul (.constant 4096) shifted)')
      || !compact.includes('validRawBound bitLength')) {
    failures.push('compiled-bound');
  }
  if (!compact.includes(
    'machineOutput compiledMachine (validRawTimePolynomial.eval bits.length) bits = validatedSourceBytes bits')
      || !compact.includes(
        'boundedDecide compiledMachine (validRawTimePolynomial.eval bits.length) bits = .accept ↔ ValidEncodedCircuit bits')
      || !compact.includes(
        'boundedDecide compiledMachine (validRawTimePolynomial.eval bits.length) bits ≠ .timeout')
      || !compact.includes(
        'FunctionProgram.RawRefinement validatedSourceBytesPolynomialTimeFunction.program')) {
    failures.push('compiled-interface');
  }
  if (!compact.includes('cleanupRejectConfiguration_output_empty')
      || !compact.includes('emptyRejectConfiguration_output_empty')
      || !compact.includes('oneBitRejectConfiguration_output_empty')
      || !compact.includes('twoCellRejectConfiguration_output_empty')) {
    failures.push('fail-closed-output');
  }
  return [...new Set(failures)];
}

test('literal source parser is finite, direct, and shortcut-free',
  async () => {
    const sources = await Promise.all(MODULES.map(text0));
    assert.deepEqual(validateSources0(sources), []);
  });

test('axiom transcript follows every current public declaration in source order',
  async () => {
    const [sources, audit] = await Promise.all([
      Promise.all(MODULES.map(text0)),
      text0(AXIOM_AUDIT),
    ]);
    const declarations = publicDeclarations0(sources);
    const qualifiedDeclarations =
      qualifiedPublicDeclarations0(sources);
    const printed = printed0(audit);

    assert.deepEqual(imports0(audit), MODULES.map((relativePath) =>
      relativePath
        .replace(/^lean\//u, '')
        .replace(/\.lean$/u, '')
        .replaceAll('/', '.')));
    assert.equal(printed.length, declarations.length);
    assert.equal(new Set(printed).size, printed.length);
    assert.deepEqual(
      printed,
      qualifiedDeclarations.map(({ qualifiedName }) => qualifiedName),
    );
    assert.equal(printed.every((name) =>
      name.startsWith('PNP.Concrete.LockedNAND.')), true);
  });

test('root, publication, status, workflow, and documentation bind the parser',
  async () => {
    const [
      sources,
      audit,
      root,
      aggregate,
      inventory,
      map,
      status,
      workflow,
      docs,
    ] = await Promise.all([
      Promise.all(MODULES.map(text0)),
      text0(AXIOM_AUDIT),
      text0('lean/PNP.lean'),
      text0('lean/PNP/Concrete/LockedNANDSourceParser.lean'),
      text0('status/LEAN_THEOREM_INVENTORY.json').then(JSON.parse),
      text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
      text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
      text0('.github/workflows/lean-bridge.yml'),
      text0('docs/lean_concrete_locked_nand_source_parser.md'),
    ]);
    const printed = printed0(audit);
    const rows = new Map(
      inventory.declarations.map((entry) => [entry.name, entry]),
    );

    assert.match(
      root,
      /^import PNP\.Concrete\.LockedNANDSourceParser$/mu,
    );
    assert.deepEqual(
      imports0(aggregate),
      MODULES.map((relativePath) =>
        relativePath
          .replace(/^lean\//u, '')
          .replace(/\.lean$/u, '')
          .replaceAll('/', '.')),
    );
    assert.deepEqual(
      printed,
      qualifiedPublicDeclarations0(sources)
        .map(({ qualifiedName }) => qualifiedName),
    );
    for (const name of printed) {
      const row = rows.get(name);
      assert.notEqual(row, undefined, name);
      assert.equal(
        row.axioms.every((axiom) =>
          ['Quot.sound', 'propext'].includes(axiom)),
        true,
        `${name}:${row.axioms.join(',')}`,
      );
    }

    for (const field of [
      'leanConcreteLockedNANDParserMachineFormalized',
      'leanConcreteLockedNANDParserAxiomAuditPassed',
      'leanConcreteLockedNANDParserAllInputExactFormalized',
      'leanConcreteLockedNANDParserExactOutputFormalized',
      'leanConcreteLockedNANDParserCompiledNonTimeoutFormalized',
      'leanConcreteLockedNANDParserPolynomialTimeMachineFormalized',
      'leanConcreteLockedNANDParserPolynomialTimeFunctionFormalized',
      'leanConcreteLockedNANDParserRawRefinementFormalized',
    ]) assert.equal(status[field], true, field);
    assert.equal(
      status.leanConcreteLockedNANDParserAuditedDeclarationCount,
      printed.length,
    );
    assert.equal(status.projectSpecificAxiomInventory.length > 0, status.projectSpecificAxiomsRemaining);
    assert.equal(status.remainingBlockers.length, 5);
    assert.equal(status.rootLeanTheoremPresent, false);
    assert.equal(status.concretePublicationGate.passed, false);

    const milestone = status.formalPublicationMilestones.find(
      ({ id }) => id === 'concrete-locked-nand-source-parser',
    );
    assert.notEqual(milestone, undefined);
    assert.equal(milestone.earned, true);
    assert.deepEqual(milestone.requiredTheorems, MILESTONE_THEOREMS);
    for (const name of MILESTONE_THEOREMS) {
      assert.match(
        map.earnedMilestoneTheoremKernelTypeSha256[name],
        /^[0-9a-f]{64}$/u,
        name,
      );
    }

    const closureCounts = {
      empty: 0,
      propext: 0,
      propextQuot: 0,
    };
    for (const name of printed) {
      const axioms = rows.get(name).axioms;
      if (axioms.length === 0) closureCounts.empty += 1;
      else if (axioms.length === 1 && axioms[0] === 'propext') {
        closureCounts.propext += 1;
      } else if (axioms.length === 2
          && axioms.includes('propext')
          && axioms.includes('Quot.sound')) {
        closureCounts.propextQuot += 1;
      } else {
        assert.fail(`${name}:unexpected closure:${axioms.join(',')}`);
      }
    }
    assert.ok(workflow.includes(
      `grep -Ec "^'PNP\\.Concrete\\.LockedNAND\\."`
        + `)" -eq ${printed.length}`,
    ));
    assert.ok(workflow.includes(
      `grep -Fc 'does not depend on any axioms')" -eq `
        + closureCounts.empty,
    ));
    assert.ok(workflow.includes(
      `grep -Fc 'depends on axioms: [propext]')" -eq `
        + closureCounts.propext,
    ));
    assert.ok(workflow.includes(
      `grep -Fc 'depends on axioms: [propext, Quot.sound]')" -eq `
        + closureCounts.propextQuot,
    ));

    const compactDocs = docs.replaceAll(/\s+/gu, ' ');
    for (const token of [
      'canonical generated artifacts',
      '20 reviewed theorem types',
      `${printed.length.toLocaleString('en-US')} audited declarations`,
      `${closureCounts.empty.toLocaleString('en-US')} have empty axiom closure`,
      `${closureCounts.propext.toLocaleString('en-US')} use only \`propext\``,
      `${closureCounts.propextQuot.toLocaleString('en-US')} use only \`propext\` and \`Quot.sound\``,
      'Mechanically generated publication evidence',
      'does not emit the locked-NAND target',
      'P = NP',
    ]) assert.equal(compactDocs.includes(token), true, token);
  });

test('constructive regression covers framing and every grammar boundary',
  async () => {
    const source = await text0(REGRESSION);
    for (const fragment of [
      'TokenDecodeFailure [false]',
      'TokenDecodeFailure [true, false]',
      'TokenDecodeFailure [false, true, false]',
      'TokenDecodeFailure [true, true, false, true]',
      'NatTokenFailure [.unit, .unit, .unit]',
      'SourceTokenFailure [.input, .unit, .unit]',
      'NGatesTokenFailure 1 []',
      '.missingGateEnd',
      '.wrongGateEnd',
      '.missingVersion',
      '.wrongVersion',
      '.inputCount',
      '.gateCount',
      '.missingProgramEnd',
      '.wrongProgramEnd',
      '.missingOutputsEnd',
      '.wrongOutputsEnd',
      '.missingInstanceEnd',
      '.wrongInstanceEnd',
      '.trailingToken',
      'decodeCircuitTokens_eq_none_iff_failure',
      'malformed_exact gateStartPositiveZeroZeroBits',
      'malformed_exact gateStartPositiveZeroOneBits',
      'malformed_exact gateStartExhaustedZeroZeroBits',
      'malformed_exact gateStartExhaustedZeroOneBits',
      'malformed_exact gateLeftInputIndexTailBits',
      'malformed_exact gateRightSourceTailBits',
      'malformed_exact gateRightGateIndexTailBits',
      'malformed_exact gateEndTailBits',
      'malformed_exact outputSourceTailBits',
      'malformed_exact outputInputIndexTailBits',
      'malformed_exact outputsEndTailBits',
      'malformed_exact instanceEndTailBits',
      'malformed_exact finalEofTailBits',
    ]) {
      assert.ok(source.includes(fragment), fragment);
    }
    assert.doesNotMatch(
      stripLeanCommentsAndStrings0(source),
      /\b(?:sorry|admit|axiom|unsafe|native_decide|bv_decide|sat_decide|SATOracle|Classical(?:\.choice)?|choice)\b/u,
    );
  });

test('regression pins literal, compiled, polynomial, and rejection interfaces',
  async () => {
    const source = await text0(REGRESSION);
    for (const fragment of [
      'SourceParser.statePrograms.length = 228',
      'SourceParser.rules.length = 2052',
      'SourceParser.rules_pairwise_query_distinct',
      'SourceParser.machine_startState_ne_acceptState',
      'SourceParser.machine_startState_ne_rejectState',
      'SourceParser.machine_acceptState_ne_rejectState',
      'compiledStart_blankEquivalent bits',
      'PolynomialTimeMachine ValidEncodedCircuit',
      'validatedSourceBytesPolynomialTimeFunction_output bits',
      '(validRawTimePolynomial.eval 0) [] = .reject',
    ]) assert.ok(source.includes(fragment), fragment);
  });

test('hostile machine, bound, cleanup, and trust mutations are rejected',
  async () => {
    const sources = await Promise.all(MODULES.map(text0));

    const decoderMachine = [...sources];
    decoderMachine[2] = decoderMachine[2].replace(
      'rules := rules',
      'rules := (let leaked := decodeCircuit []; rules)',
    );
    assert.ok(validateSources0(decoderMachine)
      .includes('decoder-in-rule-construction'));

    const semanticOracleMachine = [...sources];
    semanticOracleMachine[2] = semanticOracleMachine[2].replace(
      'rules := rules',
      'rules := (let leaked := validatedSourceBytes []; rules)',
    );
    assert.ok(validateSources0(semanticOracleMachine)
      .includes('decoder-in-rule-construction'));

    const privateDecoderHelper = [...sources];
    privateDecoderHelper[2] = privateDecoderHelper[2].replace(
      'private def corePrograms',
      'private def leakedDecoder := decodeCircuit\n'
        + 'private def corePrograms',
    );
    assert.ok(validateSources0(privateDecoderHelper)
      .includes('decoder-in-rule-construction'));

    const wrongStateCount = [...sources];
    wrongStateCount[2] = wrongStateCount[2]
      .replace('statePrograms.length = 228', 'statePrograms.length = 227');
    assert.ok(validateSources0(wrongStateCount)
      .includes('literal-rule-table'));

    const wrongRuleCount = [...sources];
    wrongRuleCount[2] = wrongRuleCount[2]
      .replace('def ruleCount : Nat := 2052', 'def ruleCount : Nat := 2051');
    assert.ok(validateSources0(wrongRuleCount)
      .includes('literal-rule-table'));

    const removedCleanup = [...sources];
    removedCleanup[5] = removedCleanup[5]
      .replaceAll('guardedCleanupExplicit_exact', 'mutatedCleanupExact');
    assert.ok(validateSources0(removedCleanup).includes('exact-interface'));

    const wrongBound = [...sources];
    wrongBound[7] = wrongBound[7]
      .replace('(.mul (.constant 4096) shifted)',
        '(.mul (.constant 2048) shifted)');
    assert.ok(validateSources0(wrongBound).includes('compiled-bound'));

    const wrongCompiledOutput = [...sources];
    wrongCompiledOutput[7] = wrongCompiledOutput[7]
      .replace('validatedSourceBytes bits := by',
        'bits := by');
    assert.ok(validateSources0(wrongCompiledOutput)
      .includes('compiled-interface'));

    const removedRawRefinement = [...sources];
    removedRawRefinement[7] = removedRawRefinement[7]
      .replaceAll('validatedSourceBytesRawRefinement',
        'mutatedValidatedSourceBytesRawRefinement');
    assert.ok(validateSources0(removedRawRefinement)
      .includes('exact-interface'));

    const admitted = [...sources];
    admitted[0] = admitted[0]
      .replace('def ValidEncodedCircuit',
        'axiom injected : False\ndef ValidEncodedCircuit');
    assert.ok(validateSources0(admitted).includes('assumption'));

    const bitvectorShortcut = [...sources];
    bitvectorShortcut[0] = bitvectorShortcut[0]
      .replace('def ValidEncodedCircuit',
        'theorem injectedShortcut : True := by bv_decide\n'
          + 'def ValidEncodedCircuit');
    assert.ok(validateSources0(bitvectorShortcut).includes('shortcut'));

    const satOracle = [...sources];
    satOracle[0] = satOracle[0]
      .replace('def ValidEncodedCircuit',
        'def SATOracle := True\ndef ValidEncodedCircuit');
    assert.ok(validateSources0(satOracle).includes('shortcut'));

    const hostLookup = [...sources];
    hostLookup[2] = hostLookup[2]
      .replace('def statePrograms',
        'def hostLookup := decodeCircuit\ndef statePrograms');
    assert.ok(validateSources0(hostLookup).includes('host-lookup'));

    const certified = [...sources];
    certified[6] = certified[6]
      .replace('def emptyRejectConfiguration',
        'def callerCertificate := True\ndef emptyRejectConfiguration');
    assert.ok(validateSources0(certified).includes('caller-certificate'));

    const overclaim = [...sources];
    overclaim[7] = overclaim[7]
      .replace('def validRawTimePolynomial',
        'theorem p_eq_np : True := True.intro\n'
          + 'def validRawTimePolynomial');
    assert.ok(validateSources0(overclaim).includes('overclaim'));
  });

export { MODULES, AXIOM_AUDIT, REGRESSION, TEST };
