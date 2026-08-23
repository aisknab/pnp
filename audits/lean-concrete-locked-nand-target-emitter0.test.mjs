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
  'lean/PNP/Concrete/LockedNANDRawBuilder.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitter.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterBlockCompiler.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterCapacity.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterCheckStack.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterController.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerCheckTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerCompiled.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerCompletionTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerGateBound.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerGateListTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerGateTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerHeaderBound.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerHeaderTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerInitialTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerNormalizationBound.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerNormalizationTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerOutputBound.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerOutputTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerPolynomialBound.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerPrefixBound.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerPrefixTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerSourceTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerTotalTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterControllerTrace.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterCursorAppender.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterCursorControl.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterCursorFinalizer.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterCursorNatLoop.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterFinalizer.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterGrammarScanner.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterLedger.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterMachine.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterMarkedSourceReload.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterNatLoop.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterNavigator.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterPlan.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterPrimitiveCompiler.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterProgramSemantics.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterRuntime.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterRuntimeCheckStack.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterRuntimeLayout.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterRuntimePrimitives.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterRuntimeProgram.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterRuntimeProgramBound.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterRuntimeProgramSafety.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterRuntimeSourceControl.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSchedule.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterScratchAddSlot.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterScratchCompareSlot.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterScratchCompareSlotExact.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterScratchIncrement.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterScratchReset.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSemanticCompletion.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSemanticFinal.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSemanticNormalization.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSemanticOutput.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSemanticPrefix.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSemanticPrefixBridge.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSemanticSchedule.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSlotIncrement.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSourceCapture.lean',
  'lean/PNP/Concrete/LockedNANDTargetEmitterSpec.lean',
  'lean/PNP/Concrete/WorkMachineBlankEquivalence.lean',
  'lean/PNP/Concrete/WorkMachineChain.lean',
  'lean/PNP/Concrete/WorkMachineProgramGraph.lean',
  'lean/PNP/Concrete/WorkMachineProgramPath.lean',
  'lean/PNP/Concrete/WorkMachineProgramPathBlankEquivalence.lean',
]);
const AXIOM_AUDIT =
  'lean-audit/PNPConcreteLockedNANDTargetEmitterAxiomAudit.lean';
const REGRESSION =
  'lean-regression/PNPConcreteLockedNANDTargetEmitter.lean';
const TEST =
  'audits/lean-concrete-locked-nand-target-emitter0.test.mjs';

const MILESTONE_THEOREMS = Object.freeze([
  'PNP.Concrete.LockedNAND.RawBuilder.rawLockedInstance_of_elaborate',
  'PNP.Concrete.LockedNAND.RawBuilder.targetBytes_of_elaborated',
  'PNP.Concrete.LockedNAND.TargetEmitterSpec.targetBytes_validatedSourceBytes_eq_buildLockedNANDInstance',
  'PNP.Concrete.LockedNAND.TargetEmitterSpec.targetBytes_size_le',
  'PNP.Concrete.LockedNAND.TargetEmitterController.rules_length_literal',
  'PNP.Concrete.LockedNAND.TargetEmitterController.rules_pairwise',
  'PNP.Concrete.LockedNAND.TargetEmitterController.machine_accept_ne_reject',
  'PNP.Concrete.LockedNAND.TargetEmitterController.graph_wellFormed',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerTotalTrace.malformed_bounded_exact',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerTotalTrace.decoded_bounded_exact',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerTotalTrace.allInput_bounded_exact',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.controllerWorkTimePolynomial_eval',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.allInputWorkTimePolynomial_eval',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial_eval',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.controller_complete_path_polynomial',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerPolynomialBound.controllerUniformEnvelope_le_workBound',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.compiledStart_blankEquivalent',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.compiledMachineOutput_eq_targetBytes',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.compiledBoundedDecide_accept_iff',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.compiledBoundedDecide_ne_timeout',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.rawTargetBytesPolynomialTimeFunction_output',
  'PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled.strictLockedNANDPolynomialTimeFunction_output',
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

function declarationBlock0(source, name) {
  const heads = explicitLeanDeclarationHeads0(source);
  const index = heads.findIndex((head) => head.name === name);
  if (index === -1) return '';
  const end = heads[index + 1]?.index ?? source.length;
  return source.slice(heads[index].index, end);
}

function validateSources0(sources) {
  const failures = [];
  const combined = stripLeanCommentsAndStrings0(sources.join('\n'));
  const controller = sources[5];
  const compiled = sources[7];
  const polynomial = sources[19];
  const totalTrace = sources[23];
  const scanner = sources[30];
  const ledger = sources[31];
  const rawBuilder = sources[0];
  const spec = sources[62];

  if (sources.length !== 68) failures.push('module-set');
  if (publicDeclarations0(sources).length !== 3295) {
    failures.push('declaration-count');
  }
  if (sources.some(hasLeanAssumptionDeclaration0)) failures.push('assumption');
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
  if (/\b(?:PolynomialReduction|NPComplete|cnfSATInP|p_eq_np)\b/u
    .test(combined)) {
    failures.push('overclaim');
  }

  const scannerTraceBoundary = scanner.indexOf('def tapeAtWord');
  const executableBlocks = [
    controller,
    scanner.slice(0, scannerTraceBoundary),
    declarationBlock0(controller, 'nodes'),
    declarationBlock0(controller, 'graph'),
    declarationBlock0(controller, 'machine'),
    declarationBlock0(scanner, 'statePrograms'),
    declarationBlock0(scanner, 'rules'),
    declarationBlock0(scanner, 'machine'),
  ].map((block) => stripLeanCommentsAndStrings0(block)).join('\n');
  if (/\b(?:decodeCircuit|decodeElaboratedCircuit|RawBuilder|targetBytes|rawLockedInstance|SemanticSchedule|scheduleLookup|callerCertificate)\b/u
    .test(executableBlocks)) {
    failures.push('semantic-or-decoder-in-table');
  }

  const compactController = compact0(controller);
  const compactScanner = compact0(scanner);
  const compactLedger = compact0(ledger);
  if (!compactController.includes(
    'def controlNodeName (code : Nat) : Nat := 2 * code')
      || !compactController.includes(
        'def graph : Graph := { nodes := nodes entry := scannerRef }')
      || !compactController.includes(
        'def machine : WorkMachine := WorkMachineProgramGraph.machine graph')
      || !compactController.includes('def ruleCount : Nat := 1387921')
      || !compactController.includes(
        'theorem rules_length_literal : machine.rules.length = ruleCount')) {
    failures.push('controller-table');
  }
  if (!compactScanner.includes(
    'theorem statePrograms_length : statePrograms.length = 60')
      || !compactScanner.includes('def ruleCount : Nat := 540')
      || !compactScanner.includes(
        'theorem rules_pairwise_query_distinct')) {
    failures.push('scanner-table');
  }
  if (!compactLedger.includes('def ruleCount : Nat := 20556')
      || !compactLedger.includes('theorem rules_pairwise_query_distinct')) {
    failures.push('ledger-table');
  }

  const compactRawBuilder = compact0(rawBuilder);
  const compactSpec = compact0(spec);
  if (!compactRawBuilder.includes(
    'def targetBytes (bits : BitString) : BitString := match decodeCircuit bits with | none => [] | some raw => encodeLockedInstance (rawLockedInstance raw)')
      || !compactRawBuilder.includes('theorem rawLockedInstance_of_elaborate')
      || !compactRawBuilder.includes('theorem targetBytes_of_elaborated')) {
    failures.push('exact-target');
  }
  if (!compactSpec.includes(
    'targetBytes_validatedSourceBytes_eq_buildLockedNANDInstance')
      || !compactSpec.includes(
        'def rawTargetOutputSizePolynomial : NatPolynomial')
      || !compactSpec.includes('theorem targetBytes_size_le')) {
    failures.push('target-boundary');
  }

  const compactPolynomial = compact0(polynomial);
  if (!compactPolynomial.includes(
    'def allInputWorkBound (bitLength : Nat) : Nat := 512 * shiftedSize bitLength * phaseUnit bitLength')
      || !compactPolynomial.includes(
        'def compiledRawTimePolynomial : NatPolynomial := .mul (.constant 6) allInputWorkTimePolynomial')
      || !compactPolynomial.includes(
        'compiledRawTimePolynomial.eval bitLength = 6 * allInputWorkBound bitLength')) {
    failures.push('polynomial-bound');
  }

  const compactTotal = compact0(totalTrace);
  const compactCompiled = compact0(compiled);
  for (const fragment of [
    'theorem malformed_bounded_exact',
    'theorem decoded_bounded_exact',
    'theorem allInput_bounded_exact',
  ]) {
    if (!compactTotal.includes(fragment)) failures.push('total-trace');
  }
  for (const fragment of [
    'compiledMachineOutput_eq_targetBytes',
    'compiledBoundedDecide_accept_iff',
    'compiledBoundedDecide_ne_timeout',
    'rawTargetBytesPolynomialTimeFunction_output',
    'strictLockedNANDPolynomialTimeFunction_output',
    'rawTargetBytesRawRefinement',
    'strictLockedNANDRawRefinement',
    'buildLockedNANDInstance bits',
  ]) {
    if (!compactCompiled.includes(fragment)) failures.push('compiled-interface');
  }
  if (!compactCompiled.includes(
    'theorem compiledMachineOutput_eq_targetBytes (bits : BitString) : machineOutput compiledMachine (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval bits.length) bits = RawBuilder.targetBytes bits := by')
      || !compactCompiled.includes(
        'theorem strictLockedNANDPolynomialTimeFunction_output (bits : BitString) : strictLockedNANDPolynomialTimeFunction.output bits = buildLockedNANDInstance bits := by')) {
    failures.push('compiled-interface');
  }
  return [...new Set(failures)];
}

test('target emitter source set is finite, literal, and shortcut-free',
  async () => {
    const sources = await Promise.all(MODULES.map(text0));
    assert.deepEqual(validateSources0(sources), []);
  });

test('axiom transcript covers all 3,295 declarations in exact source order',
  async () => {
    const [sources, audit] = await Promise.all([
      Promise.all(MODULES.map(text0)),
      text0(AXIOM_AUDIT),
    ]);
    const qualified = qualifiedPublicDeclarations0(sources)
      .map(({ qualifiedName }) => qualifiedName);
    const printed = printed0(audit);
    assert.deepEqual(imports0(audit), [
      'PNP.Concrete.LockedNANDTargetEmitter',
    ]);
    assert.equal(qualified.length, 3295);
    assert.deepEqual(printed, qualified);
    assert.equal(new Set(printed).size, 3295);
  });

test('root, generated evidence, workflow, and documentation bind the emitter',
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
      text0('lean/PNP/Concrete/LockedNANDTargetEmitter.lean'),
      text0('status/LEAN_THEOREM_INVENTORY.json').then(JSON.parse),
      text0('publication/FORMAL_PUBLICATION_MAP.json').then(JSON.parse),
      text0('status/FORMAL_RECONSTRUCTION_STATUS.json').then(JSON.parse),
      text0('.github/workflows/lean-bridge.yml'),
      text0('docs/lean_concrete_locked_nand_target_emitter.md'),
    ]);
    const printed = printed0(audit);
    const rows = new Map(
      inventory.declarations.map((entry) => [entry.name, entry]),
    );

    assert.match(root,
      /^import PNP\.Concrete\.LockedNANDTargetEmitter$/mu);
    assert.deepEqual(imports0(aggregate), [
      'PNP.Concrete.LockedNANDTargetEmitterSpec',
      'PNP.Concrete.LockedNANDTargetEmitterControllerCompiled',
    ]);
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
      'leanConcreteLockedNANDEmitterMachineFormalized',
      'leanConcreteLockedNANDEmitterAxiomAuditPassed',
      'leanConcreteLockedNANDEmitterAllInputExactFormalized',
      'leanConcreteLockedNANDEmitterExactTargetBytesFormalized',
      'leanConcreteLockedNANDEmitterCompiledNonTimeoutFormalized',
      'leanConcreteLockedNANDEmitterPolynomialTimeMachineFormalized',
      'leanConcreteLockedNANDEmitterPolynomialTimeFunctionFormalized',
      'leanConcreteLockedNANDEmitterRawRefinementFormalized',
      'leanConcreteLockedNANDEmitterStrictParserCompositionFormalized',
      'leanConcreteLockedNANDEmitterOutputSizeBoundFormalized',
    ]) assert.equal(status[field], true, field);
    assert.equal(
      status.leanConcreteLockedNANDEmitterAuditedDeclarationCount,
      3295,
    );
    assert.equal(status.leanConcreteLockedNANDPolynomialReductionFormalized,
      true);
    assert.equal(status.projectSpecificAxiomInventory.length > 0, status.projectSpecificAxiomsRemaining);
    assert.equal(status.remainingBlockers.length, 5);
    assert.equal(status.rootLeanTheoremPresent, false);
    assert.equal(status.concretePublicationGate.passed, false);

    const milestone = status.formalPublicationMilestones.find(
      ({ id }) => id === 'concrete-locked-nand-target-emitter',
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

    assert.match(workflow,
      /PNPConcreteLockedNANDTargetEmitterAxiomAudit\.lean/u);
    assert.match(workflow,
      /PNPConcreteLockedNANDTargetEmitter\.lean/u);
    assert.match(workflow,
      /lean-concrete-locked-nand-target-emitter0\.test\.mjs/u);
    for (const fragment of [
      '-eq 3295',
      '-eq 2224',
      '-eq 429',
      '-eq 642',
    ]) assert.equal(workflow.includes(fragment), true, fragment);

    const compactDocs = docs.replaceAll(/\s+/gu, ' ');
    for (const token of [
      '`status/LEAN_THEOREM_INVENTORY.json`',
      '`publication/FORMAL_PUBLICATION_MAP.json`',
      '`status/FORMAL_RECONSTRUCTION_STATUS.json`',
      'root report artifacts',
      '3,295 audited declarations',
      '22 theorem types',
      '2,224 have empty axiom closure',
      '429 use only `propext`',
      '642 use only `propext` and `Quot.sound`',
      'grammar-only',
      'decoded but intrinsically invalid',
      'strict parser',
      'PolynomialReduction',
      'P = NP',
    ]) assert.equal(compactDocs.includes(token), true, token);
  });

test('constructive regression pins malformed, decoded, strict, and compiled cases',
  async () => {
    const source = await text0(REGRESSION);
    for (const fragment of [
      'runsTotallyExactly []',
      'runsTotallyExactly [false]',
      'runsTotallyExactly [true]',
      'runsTotallyExactly [false, false, false]',
      'runsTotallyExactly [true, true, true, true, true]',
      'rejectsExactly []',
      'constantFalseCircuit',
      'constantTrueCircuit',
      'oneGateCircuit',
      'decodedInvalidReferenceCircuit',
      'RawBuilder.targetBytes (encodeCircuit inputOutOfRangeCircuit) ≠ []',
      'strictLockedNANDPolynomialTimeFunction.output',
      'TargetEmitterController.ruleCount = 1387921',
      'compiledRawTimePolynomial.eval n =',
      'compiledBoundedDecide_ne_timeout bits',
      'rawTargetBytesRawRefinement',
      'strictLockedNANDRawRefinement',
    ]) assert.equal(source.includes(fragment), true, fragment);
    assert.doesNotMatch(
      stripLeanCommentsAndStrings0(source),
      /\b(?:sorry|admit|axiom|unsafe|native_decide|bv_decide|sat_decide|SATOracle|Classical(?:\.choice)?|choice)\b/u,
    );
  });

test('hostile table, bridge, target, trust, and overclaim mutations are rejected',
  async () => {
    const sources = await Promise.all(MODULES.map(text0));

    const stateCollision = [...sources];
    stateCollision[5] = stateCollision[5]
      .replace('2 * code', 'code');
    assert.ok(validateSources0(stateCollision).includes('controller-table'));

    const removedEntryBridge = [...sources];
    removedEntryBridge[5] = removedEntryBridge[5]
      .replace('entry := scannerRef', 'entry := ledgerRef');
    assert.ok(validateSources0(removedEntryBridge)
      .includes('controller-table'));

    const shadowedTable = [...sources];
    shadowedTable[5] = shadowedTable[5]
      .replace('nodes := nodes', 'nodes := nodes.reverse');
    assert.ok(validateSources0(shadowedTable).includes('controller-table'));

    const decoderInTable = [...sources];
    decoderInTable[5] = decoderInTable[5]
      .replace('def machine : WorkMachine :=',
        'def leaked := decodeCircuit []\ndef machine : WorkMachine :=');
    assert.ok(validateSources0(decoderInTable)
      .includes('semantic-or-decoder-in-table'));

    const semanticInTable = [...sources];
    semanticInTable[30] = semanticInTable[30]
      .replace('def rules : List WorkRule :=',
        'def leaked := RawBuilder.targetBytes []\ndef rules : List WorkRule :=');
    assert.ok(validateSources0(semanticInTable)
      .includes('semantic-or-decoder-in-table'));

    const wrongRuleCount = [...sources];
    wrongRuleCount[5] = wrongRuleCount[5]
      .replace('def ruleCount : Nat := 1387921',
        'def ruleCount : Nat := 1387920');
    assert.ok(validateSources0(wrongRuleCount)
      .includes('controller-table'));

    const wrongScannerCount = [...sources];
    wrongScannerCount[30] = wrongScannerCount[30]
      .replace('def ruleCount : Nat := 540', 'def ruleCount : Nat := 539');
    assert.ok(validateSources0(wrongScannerCount)
      .includes('scanner-table'));

    const wrongLedgerCount = [...sources];
    wrongLedgerCount[31] = wrongLedgerCount[31]
      .replace('def ruleCount : Nat := 20556',
        'def ruleCount : Nat := 20555');
    assert.ok(validateSources0(wrongLedgerCount)
      .includes('ledger-table'));

    const replacedTarget = [...sources];
    replacedTarget[0] = replacedTarget[0]
      .replace('encodeLockedInstance (rawLockedInstance raw)', 'bits');
    assert.ok(validateSources0(replacedTarget).includes('exact-target'));

    const wrongCompiledOutput = [...sources];
    wrongCompiledOutput[7] = wrongCompiledOutput[7]
      .replace('RawBuilder.targetBytes bits := by', 'bits := by');
    assert.ok(validateSources0(wrongCompiledOutput)
      .includes('compiled-interface'));

    const wrongBound = [...sources];
    wrongBound[19] = wrongBound[19]
      .replace('.mul (.constant 6) allInputWorkTimePolynomial',
        '.mul (.constant 5) allInputWorkTimePolynomial');
    assert.ok(validateSources0(wrongBound).includes('polynomial-bound'));

    const assumption = [...sources];
    assumption[62] = assumption[62]
      .replace('def totalTargetBytes',
        'axiom injected : False\ndef totalTargetBytes');
    assert.ok(validateSources0(assumption).includes('assumption'));

    const choice = [...sources];
    choice[62] = choice[62]
      .replace('def totalTargetBytes',
        'noncomputable def injected := Classical.choice\n'
          + 'def totalTargetBytes');
    assert.ok(validateSources0(choice).includes('shortcut'));

    const hostLookup = [...sources];
    hostLookup[5] = hostLookup[5]
      .replace('def graph : Graph :=',
        'def hostLookup := true\ndef graph : Graph :=');
    assert.ok(validateSources0(hostLookup).includes('host-lookup'));

    const callerCertificate = [...sources];
    callerCertificate[7] = callerCertificate[7]
      .replace('def GrammarDecodableCircuit',
        'def callerCertificate := True\n'
          + 'def GrammarDecodableCircuit');
    assert.ok(validateSources0(callerCertificate)
      .includes('caller-certificate'));

    const overclaim = [...sources];
    overclaim[7] = overclaim[7]
      .replace('def GrammarDecodableCircuit',
        'theorem p_eq_np : True := True.intro\n'
          + 'def GrammarDecodableCircuit');
    assert.ok(validateSources0(overclaim).includes('overclaim'));

    const printed = printed0(await text0(AXIOM_AUDIT));
    assert.notDeepEqual(
      qualifiedPublicDeclarations0([
        ...sources.slice(0, 62),
        `${sources[62]}\ntheorem extra : True := True.intro\n`,
        ...sources.slice(63),
      ]).map(({ qualifiedName }) => qualifiedName),
      printed,
    );
    assert.notDeepEqual(printed.slice(0, -1),
      qualifiedPublicDeclarations0(sources)
        .map(({ qualifiedName }) => qualifiedName));
  });

export {
  AXIOM_AUDIT,
  MILESTONE_THEOREMS,
  MODULES,
  REGRESSION,
  TEST,
};
