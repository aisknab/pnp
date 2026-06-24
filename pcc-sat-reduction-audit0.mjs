import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckGPack0,
  LOCKED_NAND_MACRO_SIGNATURES0,
  computeLockedNANDBaseline0,
  makeSyntheticGPack0,
} from './pcc-gpack0.mjs';

import {
  CheckFinalFrameworkMatch0,
  CheckFinalIntegration0,
  CheckSATBounds0,
  CheckSATDecision0,
  makeSyntheticFinalIntegration0,
} from './pcc-final-framework0.mjs';

const CHECKER_VERSION = 0;

export const SAT_REDUCTION_AUDIT_LIMITS0 = Object.freeze({
  kind: 'SATReductionAuditLimits0',
  version: CHECKER_VERSION,
  maxInputCount: 3,
  maxGateCount: 3,
  maxPrefixCheckCount: 9,
  maxCandidateExtensionsPerInput: 512,
  maxTotalCandidateExtensions: 4096,
});

export const SAT_REDUCTION_DIRECT_WIRE_MODEL0 = Object.freeze({
  kind: 'SATReductionDirectWireModel0',
  version: CHECKER_VERSION,
  gate: 'NAND',
  gateArity: 2,
  orderedSources: true,
  outputsMayReferenceInputs: true,
  outputsMayReferenceConstants: true,
  repeatedOutputCoordinatesFree: true,
  constantOutputCoordinatesFree: true,
  gateCountOnly: true,
  oneGateOutputComputesOneBooleanFunction: true,
  nonconstantNonprojectionOutputRequiresGate: true,
});

export const SAT_REDUCTION_AUDIT_POLICY0 = Object.freeze({
  kind: 'SATReductionAuditPolicy0',
  version: CHECKER_VERSION,
  independentlyEvaluateNANDCircuits: true,
  independentlyCheckDistinguishedMacroRelations: true,
  independentlyRecomputeBaselineInventory: true,
  independentlyEnumerateTraceExtensions: true,
  independentlyCheckSATAndUNSATDirections: true,
  independentlyCheckFinalLockSeparation: true,
  independentlyCheckDecisionExtractionInterface: true,
  independentlyCheckConstructionSizeLedger: true,
  positiveAndNegativeCheckerProbesRequired: true,
  callerReadinessAssertionsForbidden: true,
  boundedFiniteAuditOnly: true,
  uniformReductionSoundnessNotEstablished: true,
  uniformExactMinimizerSoundnessNotEstablished: true,
  uniformPolynomialRuntimeNotEstablished: true,
  satInPNotEstablished: true,
  pEqualsNPNotEstablished: true,
});

export const SAT_REDUCTION_REQUIRED_MACRO_RELATIONS0 = Object.freeze([
  Object.freeze({
    macroId: 'Equality10',
    distinguished: 'a8',
    relation: 'lock-and-equality',
  }),
  Object.freeze({
    macroId: 'ConstOne2',
    distinguished: 'b2',
    relation: 'lock-and-one',
  }),
  Object.freeze({
    macroId: 'ConstZero3',
    distinguished: 'd3',
    relation: 'lock-and-zero',
  }),
  Object.freeze({
    macroId: 'NANDTrace18',
    distinguished: 'q16',
    relation: 'lock-and-nand-equation',
  }),
]);

export function makeBoundedSATReductionWitnessCircuits0() {
  return Object.freeze([
    Object.freeze({
      kind: 'PreNAND0',
      version: CHECKER_VERSION,
      auditId: 'sat.single-nand',
      inputs: Object.freeze(['x0', 'x1']),
      gates: Object.freeze([
        Object.freeze({
          id: 'g0',
          op: 'NAND',
          sources: Object.freeze(['x0', 'x1']),
        }),
      ]),
      output: 'g0',
      sourceOccurrences: Object.freeze({
        equality: 2,
        const0: 0,
        const1: 0,
      }),
    }),
    Object.freeze({
      kind: 'PreNAND0',
      version: CHECKER_VERSION,
      auditId: 'unsat.constant-zero',
      inputs: Object.freeze(['x']),
      gates: Object.freeze([
        Object.freeze({
          id: 'g0',
          op: 'NAND',
          sources: Object.freeze(['x', 'x']),
        }),
        Object.freeze({
          id: 'g1',
          op: 'NAND',
          sources: Object.freeze(['x', 'g0']),
        }),
        Object.freeze({
          id: 'g2',
          op: 'NAND',
          sources: Object.freeze(['g1', 'g1']),
        }),
      ]),
      output: 'g2',
      sourceOccurrences: Object.freeze({
        equality: 6,
        const0: 0,
        const1: 0,
      }),
    }),
  ]);
}

export function makeSATReductionAuditInput0({
  GPack = makeSyntheticGPack0(),
  FinalIntegration = makeSyntheticFinalIntegration0({ gpack: GPack }),
  WitnessCircuits = makeBoundedSATReductionWitnessCircuits0(),
  Limits = SAT_REDUCTION_AUDIT_LIMITS0,
  DirectWireModel = SAT_REDUCTION_DIRECT_WIRE_MODEL0,
} = {}) {
  return Object.freeze({
    kind: 'SATReductionAuditInput0',
    version: CHECKER_VERSION,
    GPack,
    FinalIntegration,
    WitnessCircuits,
    Limits: { ...Limits },
    DirectWireModel: { ...DirectWireModel },
    Policy: { ...SAT_REDUCTION_AUDIT_POLICY0 },
  });
}

export async function CheckSATReductionAudit0(input) {
  const checker = 'CheckSATReductionAudit0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const gpackCall = await callChecker0(
    'CheckGPack0',
    () => CheckGPack0(input.GPack),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGPack0',
    gpackCall.ok && gpackCall.record.tag === 'accept',
    gpackCall.ok ? gpackCall.record : gpackCall.witness,
  ));
  if (!gpackCall.ok || gpackCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.GPack`,
      path: ['GPack'],
      witness: {
        reason: 'bounded SAT-reduction audit requires an accepted GPack',
        inner: gpackCall.ok ? compactRecord0(gpackCall.record) : gpackCall.witness,
      },
      ledger,
    });
  }

  const integrationCall = await callChecker0(
    'CheckFinalIntegration0',
    () => CheckFinalIntegration0(input.FinalIntegration),
  );
  ledger.push(makeLedgerEntry0(
    'CheckFinalIntegration0',
    integrationCall.ok && integrationCall.record.tag === 'accept',
    integrationCall.ok ? integrationCall.record : integrationCall.witness,
  ));
  if (!integrationCall.ok || integrationCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.FinalIntegration`,
      path: ['FinalIntegration'],
      witness: {
        reason: 'bounded SAT-reduction audit requires an accepted final-integration record',
        inner: integrationCall.ok
          ? compactRecord0(integrationCall.record)
          : integrationCall.witness,
      },
      ledger,
    });
  }

  const alignment = validateIntegrationAlignment0(input);
  ledger.push(makeLedgerEntry0(
    'integrationAlignment',
    alignment.ok,
    alignment.nf ?? alignment.witness,
  ));
  if (!alignment.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.integrationAlignment`,
      alignment,
      ledger,
    );
  }

  const macroAudit = deriveMacroRelationAudit0(input.GPack.MacroTables);
  ledger.push(makeLedgerEntry0(
    'macroRelations',
    macroAudit.ok,
    macroAudit.nf ?? macroAudit.witness,
  ));
  if (!macroAudit.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.macroRelations`,
      macroAudit,
      ledger,
    );
  }

  const activeCircuit = {
    ...deepClone0(input.GPack.PreNAND),
    auditId: 'gpack.active',
  };
  const circuits = [activeCircuit, ...input.WitnessCircuits.map(deepClone0)];
  const circuitAudits = [];
  for (let index = 0; index < circuits.length; index += 1) {
    const circuit = circuits[index];
    const result = deriveCircuitAudit0({
      circuit,
      macroAudit: macroAudit.nf,
      limits: input.Limits,
      directWireModel: input.DirectWireModel,
      baselineConstCounts: index === 0
        ? {
            const0: input.GPack.PreNAND.sourceOccurrences.const0,
            const1: input.GPack.PreNAND.sourceOccurrences.const1,
          }
        : {
            const0: circuit.sourceOccurrences?.const0 ?? 0,
            const1: circuit.sourceOccurrences?.const1 ?? 0,
          },
    });
    ledger.push(makeLedgerEntry0(
      `circuit.${circuit.auditId ?? index}`,
      result.ok,
      result.nf ?? result.witness,
    ));
    if (!result.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.circuit.${safeCoord0(circuit.auditId ?? index)}`,
        result,
        ledger,
      );
    }
    circuitAudits.push(result.nf);
  }

  const directionCoverage = validateDirectionCoverage0(circuitAudits);
  ledger.push(makeLedgerEntry0(
    'directionCoverage',
    directionCoverage.ok,
    directionCoverage.nf ?? directionCoverage.witness,
  ));
  if (!directionCoverage.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.directionCoverage`,
      directionCoverage,
      ledger,
    );
  }

  const baselineAudit = deriveActiveBaselineInventoryAudit0({
    gpack: input.GPack,
    macroAudit: macroAudit.nf,
    circuitAudit: circuitAudits[0],
    limits: input.Limits,
    directWireModel: input.DirectWireModel,
  });
  ledger.push(makeLedgerEntry0(
    'activeBaselineInventory',
    baselineAudit.ok,
    baselineAudit.nf ?? baselineAudit.witness,
  ));
  if (!baselineAudit.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.activeBaselineInventory`,
      baselineAudit,
      ledger,
    );
  }

  const decisionAudit = await deriveDecisionInterfaceAudit0({
    integration: input.FinalIntegration,
    gpack: input.GPack,
    activeCircuitAudit: circuitAudits[0],
    baselineAudit: baselineAudit.nf,
  });
  ledger.push(makeLedgerEntry0(
    'decisionInterface',
    decisionAudit.ok,
    decisionAudit.nf ?? decisionAudit.witness,
  ));
  if (!decisionAudit.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.decisionInterface`,
      decisionAudit,
      ledger,
    );
  }

  const constructionLedger = deriveConstructionLedger0({
    circuitAudit: circuitAudits[0],
    baselineAudit: baselineAudit.nf,
    integration: input.FinalIntegration,
  });
  ledger.push(makeLedgerEntry0(
    'constructionLedger',
    constructionLedger.ok,
    constructionLedger.nf ?? constructionLedger.witness,
  ));
  if (!constructionLedger.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.constructionLedger`,
      constructionLedger,
      ledger,
    );
  }

  const gpackNF = gpackCall.record.NF ?? gpackCall.record.nf ?? {};
  const integrationNF = integrationCall.record.NF ?? integrationCall.record.nf ?? {};
  const totalCandidateExtensions = circuitAudits.reduce(
    (sum, entry) => sum + entry.totalCandidateExtensions,
    0,
  );
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SATReductionAudit0NF',
      checker,
      version: CHECKER_VERSION,
      boundedSATReductionAuditReady: true,
      distinguishedMacroRelationsReady: true,
      activeBaselineInventoryAuditReady: true,
      boundedTraceEquivalenceAuditReady: true,
      boundedSATDirectionAuditReady: true,
      boundedUNSATDirectionAuditReady: true,
      boundedFinalLockSeparationAuditReady: true,
      decisionExtractionInterfaceAuditReady: true,
      constructionPolynomialLedgerReady: true,

      gpackAccepted: true,
      gpackDigest: gpackCall.record.Digest ?? gpackCall.record.digest,
      gpackObjectDigest: digestCanonical0(input.GPack),
      gpackBaseline: gpackNF.baseline,
      gpackFullWordSize: gpackNF.fullWordSize,
      finalIntegrationAccepted: true,
      finalIntegrationDigest:
        integrationCall.record.Digest ?? integrationCall.record.digest,
      finalIntegrationObjectDigest: digestCanonical0(input.FinalIntegration),
      finalIntegrationNFKind: integrationNF.kind,

      macroAudit: macroAudit.nf,
      activeBaselineAudit: baselineAudit.nf,
      circuitAuditCount: circuitAudits.length,
      circuitAuditIds: circuitAudits.map((entry) => entry.auditId),
      circuitAudits,
      totalCandidateExtensions,
      directionCoverage: directionCoverage.nf,
      decisionInterfaceAudit: decisionAudit.nf,
      constructionLedger: constructionLedger.nf,

      boundedFiniteAuditOnly: true,
      boundedGateLimit: input.Limits.maxGateCount,
      boundedInputLimit: input.Limits.maxInputCount,
      auditEnumerationIsNotSATAlgorithm: true,
      uniformReductionSoundnessReady: false,
      uniformExactMinimizerSoundnessReady: false,
      uniformPolynomialRuntimeReady: false,
      globalFinalSATReductionDerivationReady: false,
      satInPReady: false,
      pEqualsNPReady: false,
      exactRemainingObligations: [
        'UniformLockedNANDEncodingSoundness',
        'UniformExactPCCMinSoundness',
        'UniformPolynomialPCCMinRuntime',
      ],
      DirectWireModel: { ...SAT_REDUCTION_DIRECT_WIRE_MODEL0 },
      directWireModelDigest: digestCanonical0(input.DirectWireModel),
      limitsDigest: digestCanonical0(input.Limits),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function deriveMacroRelationAudit0(macroTables) {
  const actualMacros = macroTables?.macros ?? macroTables;
  if (!isPlainObject0(actualMacros)) {
    return validationReject0(
      ['GPack', 'MacroTables'],
      'SAT-reduction audit requires concrete locked-NAND macro tables',
      { actual: typeof actualMacros },
    );
  }

  const relationResults = [];
  let outputCount = 0;
  for (const relationSpec of SAT_REDUCTION_REQUIRED_MACRO_RELATIONS0) {
    const expectedMacro = LOCKED_NAND_MACRO_SIGNATURES0[relationSpec.macroId];
    const actualMacro = actualMacros[relationSpec.macroId]
      ?? actualMacros[expectedMacro?.name];
    if (!isPlainObject0(expectedMacro) || !isPlainObject0(actualMacro)) {
      return validationReject0(
        ['GPack', 'MacroTables', 'macros', relationSpec.macroId],
        'SAT-reduction audit is missing a required macro relation',
        { macroId: relationSpec.macroId },
      );
    }
    if (!sameCanonical0(actualMacro.inputs, expectedMacro.inputs)
        || actualMacro.gateCount !== expectedMacro.gateCount
        || actualMacro.distinguished !== expectedMacro.distinguished
        || !sameCanonical0(actualMacro.outputs, expectedMacro.outputs)) {
      return validationReject0(
        ['GPack', 'MacroTables', 'macros', relationSpec.macroId],
        'SAT-reduction audit requires the exact version-zero macro table',
        { expected: expectedMacro, actual: actualMacro },
      );
    }

    const signatures = Object.entries(actualMacro.outputs ?? {});
    const projectionSet = new Set(makeProjectionSignatures0(actualMacro.inputs.length));
    const seen = new Set();
    for (const [outputName, signature] of signatures) {
      if (!isTruthSignature0(signature, actualMacro.inputs.length)) {
        return validationReject0(
          ['GPack', 'MacroTables', 'macros', relationSpec.macroId, 'outputs', outputName],
          'macro output truth signature has invalid shape',
          { outputName, signature },
        );
      }
      if (isConstantSignature0(signature)) {
        return validationReject0(
          ['GPack', 'MacroTables', 'macros', relationSpec.macroId, 'outputs', outputName],
          'macro output truth signature must be nonconstant',
          { outputName, signature },
        );
      }
      if (projectionSet.has(signature)) {
        return validationReject0(
          ['GPack', 'MacroTables', 'macros', relationSpec.macroId, 'outputs', outputName],
          'macro output truth signature must be nonprojection',
          { outputName, signature },
        );
      }
      if (!signatureDependsOnVariable0(
        signature,
        actualMacro.inputs.length,
        0,
      )) {
        return validationReject0(
          ['GPack', 'MacroTables', 'macros', relationSpec.macroId, 'outputs', outputName],
          'every counted macro output must depend on its private lock coordinate',
          { outputName, signature },
        );
      }
      if (seen.has(signature)) {
        return validationReject0(
          ['GPack', 'MacroTables', 'macros', relationSpec.macroId, 'outputs', outputName],
          'counted macro outputs must be pairwise distinct within each instance',
          { outputName, signature },
        );
      }
      seen.add(signature);
    }

    const distinguishedSignature = actualMacro.outputs[relationSpec.distinguished];
    const relationCheck = checkDistinguishedRelation0({
      relation: relationSpec.relation,
      signature: distinguishedSignature,
      inputCount: actualMacro.inputs.length,
    });
    if (!relationCheck.ok) {
      return validationReject0(
        ['GPack', 'MacroTables', 'macros', relationSpec.macroId, 'outputs', relationSpec.distinguished],
        'distinguished macro output does not implement its declared Boolean relation',
        relationCheck.witness,
      );
    }

    outputCount += signatures.length;
    relationResults.push(Object.freeze({
      macroId: relationSpec.macroId,
      macroName: actualMacro.name,
      inputCount: actualMacro.inputs.length,
      gateCount: actualMacro.gateCount,
      outputCount: signatures.length,
      distinguished: relationSpec.distinguished,
      relation: relationSpec.relation,
      relationTruthTableDigest: digestCanonical0(relationCheck.nf),
      allOutputsNonconstant: true,
      allOutputsNonprojection: true,
      allOutputsDependOnPrivateLock: true,
      allOutputsPairwiseDistinctWithinInstance: true,
      macroDigest: digestCanonical0(actualMacro),
    }));
  }

  return validationAccept0({
    kind: 'SATReductionMacroRelationAudit0NF',
    version: CHECKER_VERSION,
    relationCount: relationResults.length,
    countedOutputCountAcrossMacroKinds: outputCount,
    relations: relationResults,
    exactVersionZeroTables: true,
  });
}

function deriveCircuitAudit0({
  circuit,
  macroAudit,
  limits,
  directWireModel,
  baselineConstCounts,
}) {
  const shape = validateCircuit0(circuit, limits);
  if (!shape.ok) return shape;
  const m = circuit.gates.length;
  const n = circuit.inputs.length;
  const equalityOccurrences = 2 * m;
  const constZeroOccurrences = baselineConstCounts.const0;
  const constOneOccurrences = baselineConstCounts.const1;
  if (circuit.sourceOccurrences?.equality !== equalityOccurrences) {
    return validationReject0(
      ['circuit', circuit.auditId, 'sourceOccurrences', 'equality'],
      'bounded trace audit requires exactly two source-equality occurrences per NAND gate',
      {
        expected: equalityOccurrences,
        actual: circuit.sourceOccurrences?.equality,
      },
    );
  }
  for (const [field, value] of Object.entries({
    const0: constZeroOccurrences,
    const1: constOneOccurrences,
  })) {
    if (!Number.isInteger(value) || value < 0) {
      return validationReject0(
        ['circuit', circuit.auditId, 'sourceOccurrences', field],
        'bounded baseline occurrence counts must be non-negative integers',
        { field, actual: value },
      );
    }
  }

  const inputVectors = enumerateBitVectors0(n);
  const extensionWidth = 3 * m;
  const extensionsPerInput = 2 ** extensionWidth;
  const totalCandidateExtensions = inputVectors.length * extensionsPerInput;
  if (extensionsPerInput > limits.maxCandidateExtensionsPerInput
      || totalCandidateExtensions > limits.maxTotalCandidateExtensions) {
    return validationReject0(
      ['circuit', circuit.auditId],
      'bounded trace audit exceeds the declared finite enumeration limit',
      {
        extensionWidth,
        extensionsPerInput,
        totalCandidateExtensions,
        limits,
      },
    );
  }

  const relationSignatures = getDistinguishedSignatures0();
  const gateIndex = new Map(circuit.gates.map((gate, index) => [gate.id, index]));
  const inputIndex = new Map(circuit.inputs.map((name, index) => [name, index]));
  let satisfiableAssignmentCount = 0;
  let acceptedExtensionCount = 0;
  let finalTrueStateCount = 0;
  let finalFalseWithZOneStateCount = 0;
  let satWitness = null;
  let unsatWitness = null;
  const acceptedExtensionsPerInput = [];

  for (const inputVector of inputVectors) {
    const canonical = evaluateCircuit0(circuit, inputVector);
    if (!canonical.ok) return canonical;
    if (canonical.nf.output === true) {
      satisfiableAssignmentCount += 1;
      if (satWitness === null) {
        satWitness = {
          input: bitVectorObject0(circuit.inputs, inputVector),
          gates: canonical.nf.gates,
        };
      }
    } else if (unsatWitness === null) {
      unsatWitness = {
        input: bitVectorObject0(circuit.inputs, inputVector),
        gates: canonical.nf.gates,
      };
    }

    let acceptedForInput = 0;
    for (const extension of enumerateBitVectors0(extensionWidth)) {
      const traceBits = extension.slice(0, m);
      const occurrenceBits = extension.slice(m);
      const checks = [];
      let occurrenceIndex = 0;
      for (let gatePosition = 0; gatePosition < m; gatePosition += 1) {
        const gate = circuit.gates[gatePosition];
        const leftOccurrence = occurrenceBits[occurrenceIndex];
        const rightOccurrence = occurrenceBits[occurrenceIndex + 1];
        const leftSource = sourceValue0({
          source: gate.sources[0],
          inputVector,
          traceBits,
          inputIndex,
          gateIndex,
        });
        const rightSource = sourceValue0({
          source: gate.sources[1],
          inputVector,
          traceBits,
          inputIndex,
          gateIndex,
        });
        checks.push(evaluateSignature0(
          relationSignatures.equality,
          [true, leftOccurrence, leftSource],
        ));
        checks.push(evaluateSignature0(
          relationSignatures.equality,
          [true, rightOccurrence, rightSource],
        ));
        checks.push(evaluateSignature0(
          relationSignatures.nandTrace,
          [true, traceBits[gatePosition], leftOccurrence, rightOccurrence],
        ));
        occurrenceIndex += 2;
      }

      const accepted = checks.every(Boolean);
      const coherent = isCoherentExtension0({
        circuit,
        inputVector,
        traceBits,
        occurrenceBits,
        inputIndex,
        gateIndex,
      });
      if (accepted !== coherent) {
        return validationReject0(
          ['circuit', circuit.auditId, 'traceEquivalence'],
          'distinguished macro conjunction and direct NAND coherence disagree',
          {
            input: inputVector,
            traceBits,
            occurrenceBits,
            accepted,
            coherent,
          },
        );
      }
      if (accepted) {
        acceptedForInput += 1;
        acceptedExtensionCount += 1;
        const outputValue = outputValue0({
          circuit,
          inputVector,
          traceBits,
          inputIndex,
          gateIndex,
        });
        if (outputValue !== canonical.nf.output) {
          return validationReject0(
            ['circuit', circuit.auditId, 'outputTrace'],
            'accepted trace output must equal the independently evaluated NAND-circuit output',
            {
              input: inputVector,
              expected: canonical.nf.output,
              actual: outputValue,
            },
          );
        }
        if (outputValue) {
          finalTrueStateCount += 1;
        } else {
          finalFalseWithZOneStateCount += 1;
        }
      } else {
        finalFalseWithZOneStateCount += 1;
      }
    }
    if (acceptedForInput !== 1) {
      return validationReject0(
        ['circuit', circuit.auditId, 'acceptedExtensionCount'],
        'each primary-input assignment must have exactly one accepted coherent trace extension',
        { input: inputVector, acceptedForInput },
      );
    }
    acceptedExtensionsPerInput.push(acceptedForInput);
  }

  const satisfiable = satisfiableAssignmentCount > 0;
  const baseline = computeLockedNANDBaseline0({
    gateCount: m,
    equalityOccurrences,
    constZeroOccurrences,
    constOneOccurrences,
  });
  const finalPredicateIdenticallyZero = finalTrueStateCount === 0;
  if (satisfiable === finalPredicateIdenticallyZero) {
    return validationReject0(
      ['circuit', circuit.auditId, 'finalPredicate'],
      'bounded final predicate must be nonzero exactly when the source NAND circuit is satisfiable',
      {
        satisfiable,
        finalPredicateIdenticallyZero,
        finalTrueStateCount,
      },
    );
  }
  if (satisfiable && finalFalseWithZOneStateCount === 0) {
    return validationReject0(
      ['circuit', circuit.auditId, 'finalPredicate'],
      'satisfiable bounded final predicate must not collapse to the final-lock projection',
      { finalFalseWithZOneStateCount },
    );
  }

  const exactMinimumConclusion = satisfiable
    ? {
        lowerBound: baseline + 1,
        upperBound: baseline + 4,
        exact: false,
        comparatorResult: true,
        reason: 'fresh-final-lock separation plus four-gate construction',
      }
    : {
        lowerBound: baseline,
        upperBound: baseline,
        exact: true,
        exactValue: baseline,
        comparatorResult: false,
        reason: 'identically-zero final coordinate is free in the declared gate-count-only output model',
      };
  if (!satisfiable
      && (!directWireModel.constantOutputCoordinatesFree
        || !directWireModel.gateCountOnly)) {
    return validationReject0(
      ['DirectWireModel'],
      'UNSAT threshold direction requires free constant output coordinates in a gate-count-only model',
      { actual: directWireModel },
    );
  }

  return validationAccept0({
    kind: 'BoundedNANDReductionCircuitAudit0NF',
    version: CHECKER_VERSION,
    auditId: circuit.auditId,
    circuitDigest: digestCanonical0(circuit),
    inputCount: n,
    gateCount: m,
    equalityOccurrenceCount: equalityOccurrences,
    constZeroOccurrenceCount: constZeroOccurrences,
    constOneOccurrenceCount: constOneOccurrences,
    baseline,
    fullWordSize: baseline + 4,
    sourceAssignmentCount: inputVectors.length,
    satisfiableAssignmentCount,
    satisfiable,
    acceptedExtensionCount,
    acceptedExtensionsPerInput,
    extensionsPerInput,
    totalCandidateExtensions,
    traceEquivalenceExhaustive: true,
    uniqueCoherentExtensionPerInput: true,
    acceptedTraceOutputEqualsCircuitOutput: true,
    finalPredicateIdenticallyZero,
    finalPredicateNonconstant: satisfiable,
    finalPredicateEssentiallyDependsOnFreshZ: satisfiable,
    finalPredicateNotProjection: satisfiable,
    finalPredicateDistinctFromBaselineByFreshZ: satisfiable,
    satWitness,
    unsatWitness,
    exactMinimumConclusion,
    thresholdComparator: 'minSize>baseline',
    thresholdComparatorMatchesSatisfiability:
      exactMinimumConclusion.comparatorResult === satisfiable,
    residualSlackUpperBound: satisfiable ? 3 : 4,
    macroRelationAuditDigest: digestCanonical0(macroAudit),
    boundedFiniteAuditOnly: true,
  });
}

function deriveActiveBaselineInventoryAudit0({
  gpack,
  macroAudit,
  circuitAudit,
  limits,
  directWireModel,
}) {
  const pre = gpack.PreNAND;
  const m = pre.gates.length;
  const counts = {
    equalityOccurrences: pre.sourceOccurrences?.equality,
    constZeroOccurrences: pre.sourceOccurrences?.const0,
    constOneOccurrences: pre.sourceOccurrences?.const1,
  };
  if (counts.equalityOccurrences !== 2 * m) {
    return validationReject0(
      ['GPack', 'PreNAND', 'sourceOccurrences', 'equality'],
      'active baseline inventory requires two source checks per NAND gate',
      { expected: 2 * m, actual: counts.equalityOccurrences },
    );
  }
  for (const [field, value] of Object.entries(counts)) {
    if (!Number.isInteger(value) || value < 0) {
      return validationReject0(
        ['GPack', 'PreNAND', 'sourceOccurrences', field],
        'active baseline occurrence counts must be non-negative integers',
        { field, actual: value },
      );
    }
  }

  const occurrenceCount = counts.equalityOccurrences
    + counts.constZeroOccurrences
    + counts.constOneOccurrences;
  const families = gpack.SlotAlloc?.families;
  if (!isPlainObject0(families)) {
    return validationReject0(
      ['GPack', 'SlotAlloc', 'families'],
      'active baseline inventory requires concrete slot families',
      { actual: families },
    );
  }
  const expectedLengths = {
    X: pre.inputs.length,
    T: m,
    O: occurrenceCount,
    R: occurrenceCount,
    L: m,
    z: 1,
  };
  const allSlots = [];
  for (const [family, expectedLength] of Object.entries(expectedLengths)) {
    if (!Array.isArray(families[family])
        || families[family].length !== expectedLength) {
      return validationReject0(
        ['GPack', 'SlotAlloc', 'families', family],
        'active baseline slot-family cardinality mismatch',
        { family, expectedLength, actual: families[family] },
      );
    }
    allSlots.push(...families[family]);
  }
  if (new Set(allSlots).size !== allSlots.length) {
    return validationReject0(
      ['GPack', 'SlotAlloc', 'families'],
      'active baseline slots must be globally unique',
      { slots: allSlots },
    );
  }

  const macroOutputCounts = {
    Equality10: Object.keys(
      LOCKED_NAND_MACRO_SIGNATURES0.Equality10.outputs,
    ).length,
    ConstZero3: Object.keys(
      LOCKED_NAND_MACRO_SIGNATURES0.ConstZero3.outputs,
    ).length,
    ConstOne2: Object.keys(
      LOCKED_NAND_MACRO_SIGNATURES0.ConstOne2.outputs,
    ).length,
    NANDTrace18: Object.keys(
      LOCKED_NAND_MACRO_SIGNATURES0.NANDTrace18.outputs,
    ).length,
  };
  const macroGateCount =
    macroOutputCounts.Equality10 * counts.equalityOccurrences
    + macroOutputCounts.ConstZero3 * counts.constZeroOccurrences
    + macroOutputCounts.ConstOne2 * counts.constOneOccurrences
    + macroOutputCounts.NANDTrace18 * m;
  const prefixCheckCount = counts.equalityOccurrences + m;
  if (prefixCheckCount !== 3 * m
      || prefixCheckCount > limits.maxPrefixCheckCount) {
    return validationReject0(
      ['GPack', 'PrefixCert'],
      'active prefix inventory must contain exactly three checks per NAND gate within the audit limit',
      { prefixCheckCount, gateCount: m, limits },
    );
  }
  const prefixAudit = derivePrefixInventoryAudit0(prefixCheckCount);
  if (!prefixAudit.ok) return prefixAudit;
  const prefixGateCount = prefixAudit.nf.outputCount;
  const inventoryCount = macroGateCount + prefixGateCount;
  const expectedBaseline = computeLockedNANDBaseline0({
    gateCount: m,
    ...counts,
  });
  if (inventoryCount !== expectedBaseline
      || circuitAudit.baseline !== expectedBaseline
      || gpack.BaselineCert?.baseline !== expectedBaseline
      || gpack.BaselineCert?.functionsCount !== expectedBaseline
      || gpack.PrefixCert?.prefixConjunctionGates !== prefixGateCount
      || gpack.ThresholdCert?.baseline !== expectedBaseline
      || gpack.ThresholdCert?.fullWordSize !== expectedBaseline + 4) {
    return validationReject0(
      ['GPack', 'BaselineCert'],
      'active baseline inventory, certificate, prefix, and threshold counts must agree exactly',
      {
        inventoryCount,
        expectedBaseline,
        circuitBaseline: circuitAudit.baseline,
        baselineCert: gpack.BaselineCert,
        prefixCert: gpack.PrefixCert,
        thresholdCert: gpack.ThresholdCert,
      },
    );
  }

  if (!directWireModel.oneGateOutputComputesOneBooleanFunction
      || !directWireModel.nonconstantNonprojectionOutputRequiresGate
      || !directWireModel.gateCountOnly) {
    return validationReject0(
      ['DirectWireModel'],
      'active baseline lower-bound audit requires the exact direct-wire gate-count model',
      { actual: directWireModel },
    );
  }

  return validationAccept0({
    kind: 'SATReductionActiveBaselineInventoryAudit0NF',
    version: CHECKER_VERSION,
    gateCount: m,
    occurrenceCounts: counts,
    occurrenceCount,
    macroGateCount,
    prefixCheckCount,
    prefixGateCount,
    inventoryCount,
    expectedBaseline,
    constructedBaselineGateCount: expectedBaseline,
    pairwiseDistinctFunctionCount: expectedBaseline,
    allCountedFunctionsNonconstant: true,
    allCountedFunctionsNonprojection: true,
    allMacroOutputsPrivateLockSeparated: true,
    prefixOutputsPairwiseDistinct: true,
    prefixOutputsSeparatedFromMacrosByMultiLockSupport: true,
    directWireOutputInjectionLowerBound: expectedBaseline,
    exactBaselineMinimum: expectedBaseline,
    fullWordSize: expectedBaseline + 4,
    macroAuditDigest: digestCanonical0(macroAudit),
    prefixAudit: prefixAudit.nf,
    slotAllocationDigest: digestCanonical0(gpack.SlotAlloc),
    directWireModelDigest: digestCanonical0(directWireModel),
  });
}

function derivePrefixInventoryAudit0(checkCount) {
  if (!Number.isInteger(checkCount) || checkCount < 2) {
    return validationReject0(
      ['prefix', 'checkCount'],
      'prefix inventory requires at least two distinguished checks',
      { actual: checkCount },
    );
  }
  const signatures = [];
  for (let end = 1; end < checkCount; end += 1) {
    let andSignature = '';
    for (const vector of enumerateBitVectors0(checkCount)) {
      andSignature += vector.slice(0, end + 1).every(Boolean) ? '1' : '0';
    }
    const nandSignature = invertSignature0(andSignature);
    signatures.push({
      id: `prefix.${end}.nand`,
      supportSize: end + 1,
      signature: nandSignature,
    });
    signatures.push({
      id: `prefix.${end}.and`,
      supportSize: end + 1,
      signature: andSignature,
    });
  }
  const projectionSet = new Set(makeProjectionSignatures0(checkCount));
  const seen = new Map();
  for (const entry of signatures) {
    if (isConstantSignature0(entry.signature)
        || projectionSet.has(entry.signature)
        || entry.supportSize < 2) {
      return validationReject0(
        ['prefix', entry.id],
        'counted prefix output must be nonconstant, nonprojection, and depend on at least two checks',
        entry,
      );
    }
    if (seen.has(entry.signature)) {
      return validationReject0(
        ['prefix', entry.id],
        'counted prefix outputs must be pairwise distinct',
        { entry, previous: seen.get(entry.signature) },
      );
    }
    seen.set(entry.signature, entry.id);
  }
  return validationAccept0({
    kind: 'SATReductionPrefixInventoryAudit0NF',
    version: CHECKER_VERSION,
    checkCount,
    outputCount: signatures.length,
    outputs: signatures.map((entry) => ({
      id: entry.id,
      supportSize: entry.supportSize,
      signatureDigest: digestCanonical0(entry.signature),
    })),
    pairwiseDistinct: true,
    allNonconstant: true,
    allNonprojection: true,
    allDependOnAtLeastTwoPrivateChecks: true,
  });
}

async function deriveDecisionInterfaceAudit0({
  integration,
  gpack,
  activeCircuitAudit,
  baselineAudit,
}) {
  const matchCall = await callChecker0(
    'CheckFinalFrameworkMatch0',
    () => CheckFinalFrameworkMatch0(integration.FinalMatch),
  );
  const decisionCall = await callChecker0(
    'CheckSATDecision0',
    () => CheckSATDecision0(integration.SATDecision),
  );
  const boundsCall = await callChecker0(
    'CheckSATBounds0',
    () => CheckSATBounds0(integration.SATBounds),
  );
  for (const [name, call] of [
    ['CheckFinalFrameworkMatch0', matchCall],
    ['CheckSATDecision0', decisionCall],
    ['CheckSATBounds0', boundsCall],
  ]) {
    if (!call.ok || call.record.tag !== 'accept') {
      return validationReject0(
        ['FinalIntegration', name],
        'SAT-reduction decision interface requires all final subcheckers to accept',
        { name, inner: call.ok ? compactRecord0(call.record) : call.witness },
      );
    }
  }

  const baseline = baselineAudit.expectedBaseline;
  const expected = {
    matchBaseline: integration.FinalMatch?.ChargeMap?.baseline,
    matchFullWordSize: integration.FinalMatch?.ChargeMap?.fullWordSize,
    decisionBaseline: integration.SATDecision?.Baseline?.value,
    decisionLockedBaseline: integration.SATDecision?.LockedWord?.baseline,
    decisionFullWordSize: integration.SATDecision?.LockedWord?.fullWordSize,
    decisionSlack: integration.SATDecision?.LockedWord?.residualSlackMax,
    decisionComparator: integration.SATDecision?.DecisionRule?.comparator,
    decisionUsesExact: integration.SATDecision?.DecisionRule?.usesExactMinimum,
    decisionRejectsApproximate:
      integration.SATDecision?.DecisionRule?.rejectsApproximateMinimum,
    boundsSlack: integration.SATBounds?.Minimizer?.residualSlackBound,
    boundsExact: integration.SATBounds?.Minimizer?.exact,
    boundsComparator: integration.SATBounds?.DecisionProcedure?.comparator,
  };
  if (expected.matchBaseline !== baseline
      || expected.matchFullWordSize !== baseline + 4
      || expected.decisionBaseline !== baseline
      || expected.decisionLockedBaseline !== baseline
      || expected.decisionFullWordSize !== baseline + 4
      || expected.decisionSlack !== 4
      || expected.decisionComparator !== 'minSize>baseline'
      || expected.decisionUsesExact !== true
      || expected.decisionRejectsApproximate !== true
      || expected.boundsSlack !== 4
      || expected.boundsExact !== true
      || expected.boundsComparator !== 'minSize>baseline'
      || activeCircuitAudit.thresholdComparatorMatchesSatisfiability !== true) {
    return validationReject0(
      ['FinalIntegration'],
      'SAT-reduction decision interface does not align with the independently derived bounded threshold audit',
      { baseline, expected, activeCircuitAudit },
    );
  }
  const gpackDigest = digestCanonical0(gpack);
  if (!sameCanonical0(
    integration.SATDecision?.LockedWord?.gpackDigest,
    gpackDigest,
  ) || !sameCanonical0(
    integration.FinalMatch?.PG?.gpackDigest,
    gpackDigest,
  )) {
    return validationReject0(
      ['FinalIntegration', 'GPack'],
      'SAT-reduction decision and framework records must bind the exact audited GPack',
      { expected: gpackDigest },
    );
  }

  const negativeDecisionComparator = await runNegativeProbe0({
    name: 'decision-comparator',
    checker: () => CheckSATDecision0({
      ...deepClone0(integration.SATDecision),
      DecisionRule: {
        ...deepClone0(integration.SATDecision.DecisionRule),
        comparator: 'minSize>=baseline',
      },
    }),
    expectedChecker: 'CheckSATDecision0',
    expectedCoord: 'CheckSATDecision0.decisionRule',
    expectedPath: ['DecisionRule', 'comparator'],
  });
  if (!negativeDecisionComparator.ok) return negativeDecisionComparator;

  const negativeApproximate = await runNegativeProbe0({
    name: 'approximate-minimum',
    checker: () => CheckSATDecision0({
      ...deepClone0(integration.SATDecision),
      DecisionRule: {
        ...deepClone0(integration.SATDecision.DecisionRule),
        usesExactMinimum: false,
      },
    }),
    expectedChecker: 'CheckSATDecision0',
    expectedCoord: 'CheckSATDecision0.decisionRule',
    expectedPath: ['DecisionRule', 'usesExactMinimum'],
  });
  if (!negativeApproximate.ok) return negativeApproximate;

  const negativeBounds = await runNegativeProbe0({
    name: 'nonexact-minimizer-bounds',
    checker: () => CheckSATBounds0({
      ...deepClone0(integration.SATBounds),
      Minimizer: {
        ...deepClone0(integration.SATBounds.Minimizer),
        exact: false,
      },
    }),
    expectedChecker: 'CheckSATBounds0',
    expectedCoord: 'CheckSATBounds0.minimizer',
    expectedPath: ['Minimizer', 'exact'],
  });
  if (!negativeBounds.ok) return negativeBounds;

  return validationAccept0({
    kind: 'SATReductionDecisionInterfaceAudit0NF',
    version: CHECKER_VERSION,
    baseline,
    fullWordSize: baseline + 4,
    comparator: 'minSize>baseline',
    exactMinimumRequired: true,
    approximateMinimumRejected: true,
    residualSlackBound: 4,
    gpackDigest,
    finalMatchRecordDigest: matchCall.record.Digest ?? matchCall.record.digest,
    satDecisionRecordDigest:
      decisionCall.record.Digest ?? decisionCall.record.digest,
    satBoundsRecordDigest: boundsCall.record.Digest ?? boundsCall.record.digest,
    negativeProbes: [
      negativeDecisionComparator.nf,
      negativeApproximate.nf,
      negativeBounds.nf,
    ],
  });
}

function deriveConstructionLedger0({
  circuitAudit,
  baselineAudit,
  integration,
}) {
  const m = circuitAudit.gateCount;
  const counts = baselineAudit.occurrenceCounts;
  const recomputedBaseline =
    18 * m
    + 10 * counts.equalityOccurrences
    + 3 * counts.constZeroOccurrences
    + 2 * counts.constOneOccurrences
    + 2 * (3 * m - 1);
  if (recomputedBaseline !== baselineAudit.expectedBaseline
      || integration.SATBounds?.Converter?.polynomial !== true
      || integration.SATBounds?.LockedBuilder?.polynomial !== true
      || integration.SATBounds?.LockedBuilder?.fullWordOverhead !== 4
      || integration.SATBounds?.LockedBuilder?.residualSlackMax !== 4
      || integration.SATBounds?.LockedBuilder?.usesPublicSchedule !== true) {
    return validationReject0(
      ['FinalIntegration', 'SATBounds'],
      'SAT-reduction construction ledger and displayed locked-builder bounds must agree',
      {
        recomputedBaseline,
        baselineAudit,
        SATBounds: integration.SATBounds,
      },
    );
  }
  return validationAccept0({
    kind: 'SATReductionConstructionLedger0NF',
    version: CHECKER_VERSION,
    sourceGateCount: m,
    equalityOccurrenceCount: counts.equalityOccurrences,
    constZeroOccurrenceCount: counts.constZeroOccurrences,
    constOneOccurrenceCount: counts.constOneOccurrences,
    traceMacroGateCount: 18 * m,
    equalityMacroGateCount: 10 * counts.equalityOccurrences,
    constZeroMacroGateCount: 3 * counts.constZeroOccurrences,
    constOneMacroGateCount: 2 * counts.constOneOccurrences,
    prefixGateCount: 2 * (3 * m - 1),
    finalGateCount: 4,
    baseline: recomputedBaseline,
    fullWordSize: recomputedBaseline + 4,
    affineInDeclaredOccurrenceCounts: true,
    lockedConstructionPolynomialLedgerReady: true,
    auditEnumerationOperationCount: circuitAudit.totalCandidateExtensions,
    auditEnumerationIsNotClaimedPolynomialUniformly: true,
  });
}

function validateDirectionCoverage0(circuitAudits) {
  const sat = circuitAudits.filter((entry) => entry.satisfiable);
  const unsat = circuitAudits.filter((entry) => !entry.satisfiable);
  if (sat.length === 0 || unsat.length === 0) {
    return validationReject0(
      ['WitnessCircuits'],
      'bounded SAT-reduction audit requires at least one satisfiable and one unsatisfiable circuit',
      {
        satisfiableAuditIds: sat.map((entry) => entry.auditId),
        unsatisfiableAuditIds: unsat.map((entry) => entry.auditId),
      },
    );
  }
  for (const entry of sat) {
    if (!entry.finalPredicateNonconstant
        || !entry.finalPredicateEssentiallyDependsOnFreshZ
        || !entry.finalPredicateNotProjection
        || entry.exactMinimumConclusion.lowerBound !== entry.baseline + 1
        || entry.exactMinimumConclusion.upperBound !== entry.baseline + 4) {
      return validationReject0(
        ['WitnessCircuits', entry.auditId],
        'satisfiable bounded witness failed the fresh-lock threshold direction',
        entry,
      );
    }
  }
  for (const entry of unsat) {
    if (!entry.finalPredicateIdenticallyZero
        || entry.exactMinimumConclusion.exact !== true
        || entry.exactMinimumConclusion.exactValue !== entry.baseline) {
      return validationReject0(
        ['WitnessCircuits', entry.auditId],
        'unsatisfiable bounded witness failed the zero-output threshold direction',
        entry,
      );
    }
  }
  return validationAccept0({
    kind: 'SATReductionDirectionCoverage0NF',
    version: CHECKER_VERSION,
    satisfiableAuditIds: sat.map((entry) => entry.auditId),
    unsatisfiableAuditIds: unsat.map((entry) => entry.auditId),
    satDirectionCovered: true,
    unsatDirectionCovered: true,
  });
}

function validateIntegrationAlignment0(input) {
  const checks = [
    ['GPack', input.FinalIntegration.GPack, input.GPack],
    [
      'FinalMatch.PG.gpackDigest',
      input.FinalIntegration.FinalMatch?.PG?.gpackDigest,
      digestCanonical0(input.GPack),
    ],
    [
      'SATDecision.LockedWord.gpackDigest',
      input.FinalIntegration.SATDecision?.LockedWord?.gpackDigest,
      digestCanonical0(input.GPack),
    ],
  ];
  for (const [surface, actual, expected] of checks) {
    if (!sameCanonical0(actual, expected)) {
      return validationReject0(
        ['FinalIntegration', ...surface.split('.')],
        'SAT-reduction audit surfaces must bind the exact audited GPack',
        {
          surface,
          expectedDigest: digestCanonical0(expected),
          actualDigest: digestCanonical0(actual),
        },
      );
    }
  }
  return validationAccept0({
    kind: 'SATReductionIntegrationAlignment0NF',
    alignedSurfaces: checks.map(([surface]) => surface),
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'SAT-reduction audit input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'SATReductionAuditInput0') {
    return validationReject0(
      ['kind'],
      'SAT-reduction audit input kind must be SATReductionAuditInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `SAT-reduction audit input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
    'GPack',
    'FinalIntegration',
    'WitnessCircuits',
    'Limits',
    'DirectWireModel',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'SAT-reduction audit input is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.GPack)
      || !isPlainObject0(input.FinalIntegration)
      || !Array.isArray(input.WitnessCircuits)) {
    return validationReject0(
      ['input'],
      'SAT-reduction audit requires GPack and FinalIntegration objects plus a witness array',
    );
  }
  if (!sameCanonical0(input.Limits, SAT_REDUCTION_AUDIT_LIMITS0)
      || !sameCanonical0(
        input.DirectWireModel,
        SAT_REDUCTION_DIRECT_WIRE_MODEL0,
      )
      || !sameCanonical0(input.Policy, SAT_REDUCTION_AUDIT_POLICY0)) {
    return validationReject0(
      ['input'],
      'SAT-reduction audit limits, direct-wire model, and policy must match the exact bounded fail-closed contract',
      {
        expectedLimits: SAT_REDUCTION_AUDIT_LIMITS0,
        actualLimits: input.Limits,
        expectedModel: SAT_REDUCTION_DIRECT_WIRE_MODEL0,
        actualModel: input.DirectWireModel,
        expectedPolicy: SAT_REDUCTION_AUDIT_POLICY0,
        actualPolicy: input.Policy,
      },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'GPack',
    'FinalIntegration',
    'WitnessCircuits',
    'Limits',
    'DirectWireModel',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'SAT-reduction audit rejects caller-supplied readiness or theorem-truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'SATReductionAuditInputShape0NF' });
}

function validateCircuit0(circuit, limits) {
  if (!isPlainObject0(circuit)
      || !Array.isArray(circuit.inputs)
      || !Array.isArray(circuit.gates)
      || typeof circuit.auditId !== 'string'
      || circuit.auditId.length === 0) {
    return validationReject0(
      ['circuit'],
      'bounded audit circuit must expose an auditId, inputs, and gates',
      { actual: circuit },
    );
  }
  if (circuit.inputs.length < 1
      || circuit.inputs.length > limits.maxInputCount
      || circuit.gates.length < 1
      || circuit.gates.length > limits.maxGateCount) {
    return validationReject0(
      ['circuit', circuit.auditId],
      'bounded audit circuit exceeds declared input or gate limits',
      {
        inputCount: circuit.inputs.length,
        gateCount: circuit.gates.length,
        limits,
      },
    );
  }
  const known = new Set();
  for (let index = 0; index < circuit.inputs.length; index += 1) {
    const input = circuit.inputs[index];
    if (typeof input !== 'string' || input.length === 0 || known.has(input)) {
      return validationReject0(
        ['circuit', circuit.auditId, 'inputs', index],
        'bounded audit circuit inputs must be unique non-empty strings',
        { actual: input },
      );
    }
    known.add(input);
  }
  for (let index = 0; index < circuit.gates.length; index += 1) {
    const gate = circuit.gates[index];
    if (!isPlainObject0(gate)
        || typeof gate.id !== 'string'
        || gate.id.length === 0
        || known.has(gate.id)
        || gate.op !== 'NAND'
        || !Array.isArray(gate.sources)
        || gate.sources.length !== 2) {
      return validationReject0(
        ['circuit', circuit.auditId, 'gates', index],
        'bounded audit circuit gate shape, identity, or NAND arity is invalid',
        { actual: gate },
      );
    }
    for (let sourceIndex = 0; sourceIndex < 2; sourceIndex += 1) {
      if (!known.has(gate.sources[sourceIndex])) {
        return validationReject0(
          ['circuit', circuit.auditId, 'gates', index, 'sources', sourceIndex],
          'bounded audit circuit source must be an input or earlier gate',
          { actual: gate.sources[sourceIndex] },
        );
      }
    }
    known.add(gate.id);
  }
  if (!known.has(circuit.output)) {
    return validationReject0(
      ['circuit', circuit.auditId, 'output'],
      'bounded audit circuit output must name an input or gate',
      { actual: circuit.output },
    );
  }
  return validationAccept0({
    kind: 'SATReductionBoundedCircuitShape0NF',
    auditId: circuit.auditId,
  });
}

function evaluateCircuit0(circuit, inputVector) {
  const values = new Map();
  for (let index = 0; index < circuit.inputs.length; index += 1) {
    values.set(circuit.inputs[index], inputVector[index]);
  }
  const gateValues = {};
  for (const gate of circuit.gates) {
    const left = values.get(gate.sources[0]);
    const right = values.get(gate.sources[1]);
    if (typeof left !== 'boolean' || typeof right !== 'boolean') {
      return validationReject0(
        ['circuit', circuit.auditId, 'gates', gate.id],
        'bounded NAND evaluation encountered an unresolved source',
        { gate, left, right },
      );
    }
    const value = !(left && right);
    values.set(gate.id, value);
    gateValues[gate.id] = value;
  }
  const output = values.get(circuit.output);
  if (typeof output !== 'boolean') {
    return validationReject0(
      ['circuit', circuit.auditId, 'output'],
      'bounded NAND evaluation did not resolve the output',
      { output: circuit.output },
    );
  }
  return validationAccept0({
    kind: 'SATReductionNANDEvaluation0NF',
    input: bitVectorObject0(circuit.inputs, inputVector),
    gates: gateValues,
    output,
  });
}

function isCoherentExtension0({
  circuit,
  inputVector,
  traceBits,
  occurrenceBits,
  inputIndex,
  gateIndex,
}) {
  let occurrenceIndex = 0;
  for (let gatePosition = 0;
    gatePosition < circuit.gates.length;
    gatePosition += 1) {
    const gate = circuit.gates[gatePosition];
    const leftSource = sourceValue0({
      source: gate.sources[0],
      inputVector,
      traceBits,
      inputIndex,
      gateIndex,
    });
    const rightSource = sourceValue0({
      source: gate.sources[1],
      inputVector,
      traceBits,
      inputIndex,
      gateIndex,
    });
    const leftOccurrence = occurrenceBits[occurrenceIndex];
    const rightOccurrence = occurrenceBits[occurrenceIndex + 1];
    if (leftOccurrence !== leftSource || rightOccurrence !== rightSource) {
      return false;
    }
    if (traceBits[gatePosition] !== !(leftOccurrence && rightOccurrence)) {
      return false;
    }
    occurrenceIndex += 2;
  }
  return true;
}

function sourceValue0({
  source,
  inputVector,
  traceBits,
  inputIndex,
  gateIndex,
}) {
  if (inputIndex.has(source)) return inputVector[inputIndex.get(source)];
  if (gateIndex.has(source)) return traceBits[gateIndex.get(source)];
  return undefined;
}

function outputValue0({
  circuit,
  inputVector,
  traceBits,
  inputIndex,
  gateIndex,
}) {
  return sourceValue0({
    source: circuit.output,
    inputVector,
    traceBits,
    inputIndex,
    gateIndex,
  });
}

function getDistinguishedSignatures0() {
  return {
    equality:
      LOCKED_NAND_MACRO_SIGNATURES0.Equality10.outputs.a8,
    constOne:
      LOCKED_NAND_MACRO_SIGNATURES0.ConstOne2.outputs.b2,
    constZero:
      LOCKED_NAND_MACRO_SIGNATURES0.ConstZero3.outputs.d3,
    nandTrace:
      LOCKED_NAND_MACRO_SIGNATURES0.NANDTrace18.outputs.q16,
  };
}

function checkDistinguishedRelation0({ relation, signature, inputCount }) {
  const rows = [];
  for (const vector of enumerateBitVectors0(inputCount)) {
    const actual = evaluateSignature0(signature, vector);
    let expected;
    if (relation === 'lock-and-equality') {
      expected = vector[0] && vector[1] === vector[2];
    } else if (relation === 'lock-and-one') {
      expected = vector[0] && vector[1];
    } else if (relation === 'lock-and-zero') {
      expected = vector[0] && !vector[1];
    } else if (relation === 'lock-and-nand-equation') {
      expected = vector[0]
        && vector[1] === !(vector[2] && vector[3]);
    } else {
      return validationReject0([], 'unknown distinguished macro relation', {
        relation,
      });
    }
    if (actual !== expected) {
      return validationReject0([], 'distinguished macro relation truth-table mismatch', {
        relation,
        vector,
        expected,
        actual,
      });
    }
    rows.push({ vector, value: actual });
  }
  return validationAccept0({
    kind: 'SATReductionDistinguishedRelation0NF',
    relation,
    rowCount: rows.length,
    rows,
  });
}

async function runNegativeProbe0({
  name,
  checker,
  expectedChecker,
  expectedCoord,
  expectedPath,
}) {
  const call = await callChecker0(name, checker);
  if (!call.ok) {
    return validationReject0(
      ['negativeProbe', name],
      'SAT-reduction negative probe threw instead of returning a total record',
      call.witness,
    );
  }
  const record = call.record;
  const coord = record.Coord ?? record.coord;
  const path = record.Path ?? record.path;
  if (record.tag !== 'reject'
      || record.checker !== expectedChecker
      || coord !== expectedCoord
      || !sameCanonical0(path, expectedPath)) {
    return validationReject0(
      ['negativeProbe', name],
      'SAT-reduction negative probe did not reject at the declared coordinate',
      {
        expectedChecker,
        expectedCoord,
        expectedPath,
        actual: compactRecord0(record),
      },
    );
  }
  return validationAccept0({
    kind: 'SATReductionNegativeProbe0NF',
    version: CHECKER_VERSION,
    name,
    checker: expectedChecker,
    coord,
    path,
    recordDigest: record.Digest ?? record.digest,
  });
}

function enumerateBitVectors0(width) {
  const result = [];
  const count = 2 ** width;
  for (let mask = 0; mask < count; mask += 1) {
    const vector = [];
    for (let index = 0; index < width; index += 1) {
      const shift = width - index - 1;
      vector.push(Boolean((mask >> shift) & 1));
    }
    result.push(vector);
  }
  return result;
}

function evaluateSignature0(signature, vector) {
  let index = 0;
  for (const value of vector) index = index * 2 + (value ? 1 : 0);
  return signature[index] === '1';
}

function makeProjectionSignatures0(inputCount) {
  const signatures = [];
  for (let variable = 0; variable < inputCount; variable += 1) {
    let signature = '';
    for (const vector of enumerateBitVectors0(inputCount)) {
      signature += vector[variable] ? '1' : '0';
    }
    signatures.push(signature);
  }
  return signatures;
}

function signatureDependsOnVariable0(signature, inputCount, variableIndex) {
  const vectors = enumerateBitVectors0(inputCount);
  for (const vector of vectors) {
    const toggled = [...vector];
    toggled[variableIndex] = !toggled[variableIndex];
    if (evaluateSignature0(signature, vector)
        !== evaluateSignature0(signature, toggled)) {
      return true;
    }
  }
  return false;
}

function isTruthSignature0(signature, inputCount) {
  return typeof signature === 'string'
    && /^[01]+$/u.test(signature)
    && signature.length === 2 ** inputCount;
}

function isConstantSignature0(signature) {
  return /^0+$/u.test(signature) || /^1+$/u.test(signature);
}

function invertSignature0(signature) {
  return [...signature].map((bit) => (bit === '1' ? '0' : '1')).join('');
}

function bitVectorObject0(names, vector) {
  return Object.fromEntries(names.map((name, index) => [name, vector[index]]));
}

function deepClone0(value) {
  if (typeof structuredClone === 'function') return structuredClone(value);
  return JSON.parse(JSON.stringify(value));
}

async function callChecker0(name, thunk) {
  try {
    const record = await thunk();
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: `${name} did not return a total accept/reject record`,
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: `${name} threw instead of returning a reject record`,
        errorName: error?.name ?? null,
        errorMessage: error?.message ?? String(error),
      },
    };
  }
}

function compactRecord0(record) {
  return {
    tag: record?.tag ?? null,
    checker: record?.checker ?? null,
    coord: record?.Coord ?? record?.coord ?? null,
    path: record?.Path ?? record?.path ?? null,
    witness: record?.Witness ?? record?.witness ?? null,
    digest: record?.Digest ?? record?.digest ?? null,
  };
}

function safeCoord0(value) {
  return String(value).replace(/[^A-Za-z0-9_.-]/gu, '_');
}

function makeLedgerEntry0(phase, ok, material) {
  return {
    phase,
    status: ok ? 'pass' : 'fail',
    digest: digestCanonical0(material ?? null),
  };
}

function makeAcceptRecord0({ checker, nf, ledger }) {
  const digest = digestCanonical0(nf);
  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    Ledger: ledger,
    nf,
    digest,
    ledger,
  };
}

function makeRejectFromValidation0(checker, coord, result, ledger) {
  return makeRejectRecord0({
    checker,
    coord,
    path: result.path,
    witness: result.witness,
    ledger,
  });
}

function makeRejectRecord0({ checker, coord, path, witness, ledger }) {
  const nf = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };
  const digest = digestCanonical0(nf);
  return {
    tag: 'reject',
    kind: 'reject',
    checker,
    version: CHECKER_VERSION,
    Coord: coord,
    Path: path,
    Witness: witness,
    Digest: digest,
    Ledger: ledger,
    coord,
    path,
    witness,
    digest,
    ledger,
  };
}

function validationAccept0(nf) {
  return { ok: true, nf };
}

function validationReject0(path, reason, details = {}) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      ...(details ?? {}),
    },
  };
}

function sameCanonical0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
