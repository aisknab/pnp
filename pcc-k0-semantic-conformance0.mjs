import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckConformance0,
  KERNEL_RULES0,
  makeKernelConformanceSuite0,
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from './pcc-kimpl0.mjs';

import {
  CheckKImplFiniteRelFinalTheoremReadiness0,
  makeKImplFiniteRelSuccessor0,
} from './pcc-kimpl-finiterel-successor0.mjs';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const K0_SEMANTIC_CONFORMANCE_POLICY0 = Object.freeze({
  kind: 'K0SemanticConformancePolicy0',
  version: CHECKER_VERSION,
  exactLegacyConformanceSuiteRequired: true,
  exactLegacyRuleTableRequired: true,
  checkerModulesLoadedFromFixedInternalBindings: true,
  checkerAndTestSourceDigestsComputedInternally: true,
  emptyProofAcceptedNFContractRequired: true,
  malformedRuleDispatchMustReject: true,
  predecessorMustRejectUnimplementedRule: true,
  finalSemanticReadinessRequired: true,
  finalKImplReadinessRequired: true,
  callerSoundnessAssertionsForbidden: true,
  finiteConformanceDoesNotProveMathematicalMetasoundness: true,
});

export const K0_SEMANTIC_CONFORMANCE_BINDING0 = Object.freeze({
  kind: 'K0SemanticConformanceBinding0',
  version: CHECKER_VERSION,
  legacyChecker: 'CheckConformance0',
  finalSemanticReadinessChecker: 'CheckSemanticKernelReadinessFiniteRel0',
  finalKImplReadinessChecker: 'CheckKImplFiniteRelFinalTheoremReadiness0',
  finalProofChecker: 'CheckSemanticKernelProofFiniteRel0',
});

const K0_SEMANTIC_LAYERS0 = Object.freeze([
  Object.freeze({
    layerId: 'EqSubst',
    rules: Object.freeze(['Eq', 'Subst']),
    modulePath: './pcc-kernel-semantic0.mjs',
    testPath: './test/pcc-kernel-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProof0',
    readinessChecker: 'CheckSemanticKernelReadiness0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES0',
  }),
  Object.freeze({
    layerId: 'Record',
    rules: Object.freeze(['Record']),
    modulePath: './pcc-kernel-record-semantic0.mjs',
    testPath: './test/pcc-kernel-record-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofRecord0',
    readinessChecker: 'CheckSemanticKernelReadinessRecord0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_RECORD0',
  }),
  Object.freeze({
    layerId: 'DAGInd',
    rules: Object.freeze(['DAGInd']),
    modulePath: './pcc-kernel-dagind-semantic0.mjs',
    testPath: './test/pcc-kernel-dagind-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofDAGInd0',
    readinessChecker: 'CheckSemanticKernelReadinessDAGInd0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0',
  }),
  Object.freeze({
    layerId: 'LedgerInd',
    rules: Object.freeze(['LedgerInd']),
    modulePath: './pcc-kernel-ledgerind-semantic0.mjs',
    testPath: './test/pcc-kernel-ledgerind-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofLedgerInd0',
    readinessChecker: 'CheckSemanticKernelReadinessLedgerInd0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0',
  }),
  Object.freeze({
    layerId: 'OblTopoInd',
    rules: Object.freeze(['OblTopoInd']),
    modulePath: './pcc-kernel-obltopoind-semantic0.mjs',
    testPath: './test/pcc-kernel-obltopoind-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofOblTopoInd0',
    readinessChecker: 'CheckSemanticKernelReadinessOblTopoInd0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_OBLTOPOIND0',
  }),
  Object.freeze({
    layerId: 'TraceInd',
    rules: Object.freeze(['TraceInd']),
    modulePath: './pcc-kernel-traceind-semantic0.mjs',
    testPath: './test/pcc-kernel-traceind-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofTraceInd0',
    readinessChecker: 'CheckSemanticKernelReadinessTraceInd0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0',
  }),
  Object.freeze({
    layerId: 'FiniteExhaust',
    rules: Object.freeze(['FiniteExhaust']),
    modulePath: './pcc-kernel-finiteexhaust-semantic0.mjs',
    testPath: './test/pcc-kernel-finiteexhaust-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofFiniteExhaust0',
    readinessChecker: 'CheckSemanticKernelReadinessFiniteExhaust0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEEXHAUST0',
  }),
  Object.freeze({
    layerId: 'DPInd',
    rules: Object.freeze(['DPInd']),
    modulePath: './pcc-kernel-dpind-semantic0.mjs',
    testPath: './test/pcc-kernel-dpind-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofDPInd0',
    readinessChecker: 'CheckSemanticKernelReadinessDPInd0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0',
  }),
  Object.freeze({
    layerId: 'Hall',
    rules: Object.freeze(['Hall']),
    modulePath: './pcc-kernel-hall-semantic0.mjs',
    testPath: './test/pcc-kernel-hall-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofHall0',
    readinessChecker: 'CheckSemanticKernelReadinessHall0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0',
  }),
  Object.freeze({
    layerId: 'RankInd',
    rules: Object.freeze(['RankInd']),
    modulePath: './pcc-kernel-rankind-semantic0.mjs',
    testPath: './test/pcc-kernel-rankind-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofRankInd0',
    readinessChecker: 'CheckSemanticKernelReadinessRankInd0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_RANKIND0',
  }),
  Object.freeze({
    layerId: 'MinCounterexample',
    rules: Object.freeze(['MinCounterexample']),
    modulePath: './pcc-kernel-mincounterexample-semantic0.mjs',
    testPath: './test/pcc-kernel-mincounterexample-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofMinCounterexample0',
    readinessChecker: 'CheckSemanticKernelReadinessMinCounterexample0',
    supportedRulesExport:
      'SEMANTIC_KERNEL_SUPPORTED_RULES_MINCOUNTEREXAMPLE0',
  }),
  Object.freeze({
    layerId: 'IntArith',
    rules: Object.freeze(['IntArith']),
    modulePath: './pcc-kernel-intarith-semantic0.mjs',
    testPath: './test/pcc-kernel-intarith-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofIntArith0',
    readinessChecker: 'CheckSemanticKernelReadinessIntArith0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0',
  }),
  Object.freeze({
    layerId: 'Transport',
    rules: Object.freeze(['Transport']),
    modulePath: './pcc-kernel-transport-semantic0.mjs',
    testPath: './test/pcc-kernel-transport-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofTransport0',
    readinessChecker: 'CheckSemanticKernelReadinessTransport0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0',
  }),
  Object.freeze({
    layerId: 'TruthVec',
    rules: Object.freeze(['TruthVec']),
    modulePath: './pcc-kernel-truthvec-semantic0.mjs',
    testPath: './test/pcc-kernel-truthvec-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofTruthVec0',
    readinessChecker: 'CheckSemanticKernelReadinessTruthVec0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_TRUTHVEC0',
  }),
  Object.freeze({
    layerId: 'FiniteRel',
    rules: Object.freeze(['FiniteRel']),
    modulePath: './pcc-kernel-finiterel-semantic0.mjs',
    testPath: './test/pcc-kernel-finiterel-semantic0.test.mjs',
    proofChecker: 'CheckSemanticKernelProofFiniteRel0',
    readinessChecker: 'CheckSemanticKernelReadinessFiniteRel0',
    supportedRulesExport: 'SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0',
  }),
]);

export function makeK0SemanticConformanceInput0({
  KImpl = makeSyntheticKImpl0(),
  SemanticProofDAG = makeSemanticProofDAG0(),
  LegacyConformance = makeKernelConformanceSuite0(),
} = {}) {
  return {
    kind: 'K0SemanticConformanceInput0',
    version: CHECKER_VERSION,
    KImpl,
    SemanticProofDAG,
    LegacyConformance,
    Binding: { ...K0_SEMANTIC_CONFORMANCE_BINDING0 },
    Policy: { ...K0_SEMANTIC_CONFORMANCE_POLICY0 },
  };
}

export async function CheckK0SemanticConformance0(input) {
  const checker = 'CheckK0SemanticConformance0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const expectedLegacy = makeKernelConformanceSuite0();
  if (!sameCanonical0(input.LegacyConformance, expectedLegacy)) {
    const witness = {
      reason: 'K0 semantic conformance requires the exact canonical legacy conformance suite',
      expectedDigest: digestCanonical0(expectedLegacy),
      actualDigest: digestCanonical0(input.LegacyConformance),
    };
    ledger.push(makeLedgerEntry0('exactLegacyConformance', false, witness));
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyConformance.exact`,
      path: ['LegacyConformance'],
      witness,
      ledger,
    });
  }
  ledger.push(makeLedgerEntry0('exactLegacyConformance', true, expectedLegacy));

  const expectedRuleTable = makeKernelRuleTable0();
  if (!sameCanonical0(input.KImpl.RuleTable, expectedRuleTable)) {
    const witness = {
      reason: 'K0 semantic conformance requires the exact canonical primitive rule table',
      expectedDigest: digestCanonical0(expectedRuleTable),
      actualDigest: digestCanonical0(input.KImpl.RuleTable),
    };
    ledger.push(makeLedgerEntry0('exactRuleTable', false, witness));
    return makeRejectRecord0({
      checker,
      coord: `${checker}.ruleTable.exact`,
      path: ['KImpl', 'RuleTable'],
      witness,
      ledger,
    });
  }
  ledger.push(makeLedgerEntry0('exactRuleTable', true, expectedRuleTable));

  const legacyCall = await callChecker0(
    'CheckConformance0',
    () => CheckConformance0(input.KImpl, input.LegacyConformance),
  );
  ledger.push(makeLedgerEntry0(
    'CheckConformance0',
    legacyCall.ok && legacyCall.record.tag === 'accept',
    legacyCall.ok ? legacyCall.record : legacyCall.witness,
  ));
  if (!legacyCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyConformance.exception`,
      path: ['LegacyConformance'],
      witness: legacyCall.witness,
      ledger,
    });
  }
  if (legacyCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyConformance`,
      path: ['LegacyConformance'],
      witness: {
        reason: 'legacy K0 conformance checker rejected before semantic binding',
        inner: compactRecord0(legacyCall.record),
      },
      ledger,
    });
  }

  const finalKImplCall = await callChecker0(
    'CheckKImplFiniteRelFinalTheoremReadiness0',
    () => CheckKImplFiniteRelFinalTheoremReadiness0(
      makeKImplFiniteRelSuccessor0({
        KImpl: input.KImpl,
        SemanticProofDAG: input.SemanticProofDAG,
        Purpose: 'final-theorem',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKImplFiniteRelFinalTheoremReadiness0',
    finalKImplCall.ok && isKImplFinalReady0(finalKImplCall.record),
    finalKImplCall.ok ? finalKImplCall.record : finalKImplCall.witness,
  ));
  if (!finalKImplCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl.exception`,
      path: ['SemanticProofDAG'],
      witness: finalKImplCall.witness,
      ledger,
    });
  }
  if (!isKImplFinalReady0(finalKImplCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl`,
      path: ['SemanticProofDAG'],
      witness: {
        reason: 'K0 semantic conformance requires an independently final-ready FiniteRel KImpl',
        inner: compactRecord0(finalKImplCall.record),
      },
      ledger,
    });
  }

  const layerResults = [];
  const ruleResults = [];
  let previousLayer = null;
  let finalReadinessRecord = null;

  for (let layerIndex = 0;
    layerIndex < K0_SEMANTIC_LAYERS0.length;
    layerIndex += 1) {
    const layer = K0_SEMANTIC_LAYERS0[layerIndex];
    const expectedSupportedRules = KERNEL_RULES0.slice(
      0,
      KERNEL_RULES0.indexOf(layer.rules.at(-1)) + 1,
    );
    const loaded = await loadLayer0(layer);
    ledger.push(makeLedgerEntry0(
      `layer.${String(layerIndex).padStart(2, '0')}.load`,
      loaded.ok,
      loaded.nf ?? loaded.witness,
    ));
    if (!loaded.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.layer.${String(layerIndex).padStart(2, '0')}.load`,
        loaded,
        ledger,
      );
    }

    if (!sameCanonical0(loaded.supportedRules, expectedSupportedRules)) {
      const witness = {
        reason: 'semantic layer exported supported-rule set does not match the canonical cumulative prefix',
        layerId: layer.layerId,
        expected: expectedSupportedRules,
        actual: loaded.supportedRules,
      };
      ledger.push(makeLedgerEntry0(
        `layer.${String(layerIndex).padStart(2, '0')}.supportedRules`,
        false,
        witness,
      ));
      return makeRejectRecord0({
        checker,
        coord: `${checker}.layer.${String(layerIndex).padStart(2, '0')}.supportedRules`,
        path: ['layers', layerIndex, 'supportedRules'],
        witness,
        ledger,
      });
    }

    const emptyCall = await callChecker0(
      layer.proofChecker,
      () => loaded.proofChecker(makeSemanticProofDAG0()),
    );
    const emptyAccepted = emptyCall.ok
      && emptyCall.record.tag === 'accept'
      && emptyCall.record.checker === layer.proofChecker;
    ledger.push(makeLedgerEntry0(
      `layer.${String(layerIndex).padStart(2, '0')}.emptyProof`,
      emptyAccepted,
      emptyCall.ok ? emptyCall.record : emptyCall.witness,
    ));
    if (!emptyAccepted) {
      return makeRejectRecord0({
        checker,
        coord: `${checker}.layer.${String(layerIndex).padStart(2, '0')}.emptyProof`,
        path: ['layers', layerIndex, 'proofChecker'],
        witness: {
          reason: 'semantic layer proof checker failed the empty-proof totality contract',
          layerId: layer.layerId,
          inner: emptyCall.ok
            ? compactRecord0(emptyCall.record)
            : emptyCall.witness,
        },
        ledger,
      });
    }

    const emptyNF = emptyCall.record.NF ?? emptyCall.record.nf ?? {};
    const expectedNFKind = `${layer.proofChecker.replace(/^Check/, '')}NF`;
    if (emptyNF.kind !== expectedNFKind
        || !sameCanonical0(emptyNF.supportedRules, expectedSupportedRules)) {
      const witness = {
        reason: 'semantic layer accepted normal form does not match its declared cumulative contract',
        layerId: layer.layerId,
        expectedNFKind,
        actualNFKind: emptyNF.kind ?? null,
        expectedSupportedRules,
        actualSupportedRules: emptyNF.supportedRules ?? null,
      };
      ledger.push(makeLedgerEntry0(
        `layer.${String(layerIndex).padStart(2, '0')}.acceptedNF`,
        false,
        witness,
      ));
      return makeRejectRecord0({
        checker,
        coord: `${checker}.layer.${String(layerIndex).padStart(2, '0')}.acceptedNF`,
        path: ['layers', layerIndex, 'acceptedNF'],
        witness,
        ledger,
      });
    }

    const readinessCall = await callChecker0(
      layer.readinessChecker,
      () => loaded.readinessChecker(),
    );
    const isFinalLayer = layerIndex === K0_SEMANTIC_LAYERS0.length - 1;
    const readinessExpected = isFinalLayer ? 'accept' : 'reject';
    const readinessMatches = readinessCall.ok
      && readinessCall.record.tag === readinessExpected;
    ledger.push(makeLedgerEntry0(
      `layer.${String(layerIndex).padStart(2, '0')}.readiness`,
      readinessMatches,
      readinessCall.ok ? readinessCall.record : readinessCall.witness,
    ));
    if (!readinessMatches) {
      return makeRejectRecord0({
        checker,
        coord: `${checker}.layer.${String(layerIndex).padStart(2, '0')}.readiness`,
        path: ['layers', layerIndex, 'readinessChecker'],
        witness: {
          reason: 'semantic layer readiness result does not match cumulative coverage',
          layerId: layer.layerId,
          expectedTag: readinessExpected,
          actual: readinessCall.ok
            ? compactRecord0(readinessCall.record)
            : readinessCall.witness,
        },
        ledger,
      });
    }
    if (isFinalLayer) finalReadinessRecord = readinessCall.record;

    const perLayerRules = [];
    for (const ruleName of layer.rules) {
      const probe = makeMalformedDispatchProbe0(ruleName);
      const ownerCall = await callChecker0(
        layer.proofChecker,
        () => loaded.proofChecker(probe),
      );
      const ownerReasons = ownerCall.ok
        ? collectReasons0(ownerCall.record)
        : [ownerCall.witness.reason];
      const ownerRecognizedRule = ownerCall.ok
        && ownerCall.record.tag === 'reject'
        && !ownerReasons.some((reason) => /unsupported rule/i.test(reason));
      ledger.push(makeLedgerEntry0(
        `rule.${String(KERNEL_RULES0.indexOf(ruleName)).padStart(2, '0')}.ownerDispatch`,
        ownerRecognizedRule,
        ownerCall.ok ? ownerCall.record : ownerCall.witness,
      ));
      if (!ownerRecognizedRule) {
        return makeRejectRecord0({
          checker,
          coord: `${checker}.rule.${String(KERNEL_RULES0.indexOf(ruleName)).padStart(2, '0')}.ownerDispatch`,
          path: ['rules', KERNEL_RULES0.indexOf(ruleName)],
          witness: {
            reason: 'owning semantic checker did not recognize and fail-close the malformed rule probe',
            ruleName,
            ownerChecker: layer.proofChecker,
            reasons: ownerReasons,
          },
          ledger,
        });
      }

      let predecessorRejectedUnsupported = null;
      let predecessorRecordDigest = null;
      if (previousLayer !== null) {
        const predecessorCall = await callChecker0(
          previousLayer.binding.proofChecker,
          () => previousLayer.proofChecker(probe),
        );
        const predecessorReasons = predecessorCall.ok
          ? collectReasons0(predecessorCall.record)
          : [predecessorCall.witness.reason];
        predecessorRejectedUnsupported = predecessorCall.ok
          && predecessorCall.record.tag === 'reject'
          && predecessorReasons.some((reason) => /unsupported rule/i.test(reason));
        predecessorRecordDigest = predecessorCall.ok
          ? predecessorCall.record.Digest ?? predecessorCall.record.digest ?? null
          : digestCanonical0(predecessorCall.witness);
        ledger.push(makeLedgerEntry0(
          `rule.${String(KERNEL_RULES0.indexOf(ruleName)).padStart(2, '0')}.predecessorDispatch`,
          predecessorRejectedUnsupported,
          predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
        ));
        if (!predecessorRejectedUnsupported) {
          return makeRejectRecord0({
            checker,
            coord: `${checker}.rule.${String(KERNEL_RULES0.indexOf(ruleName)).padStart(2, '0')}.predecessorDispatch`,
            path: ['rules', KERNEL_RULES0.indexOf(ruleName), 'predecessor'],
            witness: {
              reason: 'predecessor semantic checker did not reject the newly introduced rule as unsupported',
              ruleName,
              predecessorChecker: previousLayer.binding.proofChecker,
              reasons: predecessorReasons,
            },
            ledger,
          });
        }
      }

      const ruleResult = Object.freeze({
        kind: 'K0SemanticRuleConformanceItem0NF',
        version: CHECKER_VERSION,
        index: KERNEL_RULES0.indexOf(ruleName),
        ruleName,
        layerId: layer.layerId,
        proofChecker: layer.proofChecker,
        readinessChecker: layer.readinessChecker,
        modulePath: layer.modulePath,
        testPath: layer.testPath,
        moduleSourceDigest: loaded.moduleSourceDigest,
        testSourceDigest: loaded.testSourceDigest,
        ownerMalformedDispatchRejected: true,
        ownerRecognizedRule: true,
        predecessorRejectedUnsupported,
        predecessorRecordDigest,
        acceptedNFKind: emptyNF.kind,
        acceptedNFSupportedRules: [...emptyNF.supportedRules],
        testCaseCount: loaded.testCaseCount,
        negativeTestMarkerPresent: true,
        mathematicalMetasoundnessNotInferred: true,
      });
      perLayerRules.push(ruleResult);
      ruleResults.push(ruleResult);
    }

    const checkerBindingDigest = digestCanonical0({
      layerId: layer.layerId,
      rules: [...layer.rules],
      moduleSourceDigest: loaded.moduleSourceDigest,
      testSourceDigest: loaded.testSourceDigest,
      proofChecker: layer.proofChecker,
      readinessChecker: layer.readinessChecker,
      supportedRulesExport: layer.supportedRulesExport,
      acceptedNFKind: emptyNF.kind,
      acceptedNFSupportedRules: emptyNF.supportedRules,
      emptyProofDigest: emptyCall.record.Digest ?? emptyCall.record.digest,
      readinessDigest:
        readinessCall.record.Digest ?? readinessCall.record.digest,
      ruleDispatchDigests: perLayerRules.map((item) => ({
        ruleName: item.ruleName,
        moduleSourceDigest: item.moduleSourceDigest,
        testSourceDigest: item.testSourceDigest,
      })),
    });

    const layerResult = Object.freeze({
      kind: 'K0SemanticLayerConformance0NF',
      version: CHECKER_VERSION,
      index: layerIndex,
      layerId: layer.layerId,
      rules: Object.freeze([...layer.rules]),
      modulePath: layer.modulePath,
      testPath: layer.testPath,
      proofChecker: layer.proofChecker,
      readinessChecker: layer.readinessChecker,
      supportedRulesExport: layer.supportedRulesExport,
      supportedRules: Object.freeze([...loaded.supportedRules]),
      moduleSourceDigest: loaded.moduleSourceDigest,
      moduleByteCount: loaded.moduleByteCount,
      testSourceDigest: loaded.testSourceDigest,
      testByteCount: loaded.testByteCount,
      testCaseCount: loaded.testCaseCount,
      negativeTestMarkerPresent: true,
      emptyProofAccepted: true,
      acceptedNFKind: emptyNF.kind,
      readinessTag: readinessCall.record.tag,
      checkerBindingDigest,
    });
    layerResults.push(layerResult);
    previousLayer = {
      binding: layer,
      proofChecker: loaded.proofChecker,
    };
  }

  if (finalReadinessRecord === null
      || finalReadinessRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalSemanticReadiness`,
      path: ['layers', K0_SEMANTIC_LAYERS0.length - 1],
      witness: {
        reason: 'final semantic readiness record was not produced by the FiniteRel layer',
      },
      ledger,
    });
  }

  const finalReadinessNF = finalReadinessRecord.NF
    ?? finalReadinessRecord.nf
    ?? {};
  if (!sameCanonical0(finalReadinessNF.supportedRules, KERNEL_RULES0)
      || !sameCanonical0(finalReadinessNF.missingRules, [])
      || finalReadinessNF.semanticRuleCoverageComplete !== true) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalSemanticReadiness`,
      path: ['layers', K0_SEMANTIC_LAYERS0.length - 1, 'readiness'],
      witness: {
        reason: 'final semantic readiness normal form does not expose complete primitive coverage',
        actual: finalReadinessNF,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'K0SemanticConformance0NF',
      checker,
      version: CHECKER_VERSION,
      semanticConformanceReady: true,
      conformanceScope: 'executable-contract-conformance',
      mathematicalMetasoundnessEstablished: false,
      mathematicalMetasoundnessRequiresIndependentAudit: true,
      exactLegacyConformanceSuite: true,
      exactLegacyRuleTable: true,
      legacyConformanceChecker: legacyCall.record.checker,
      legacyConformanceDigest:
        legacyCall.record.Digest ?? legacyCall.record.digest,
      finalSemanticReadinessChecker: finalReadinessRecord.checker,
      finalSemanticReadinessDigest:
        finalReadinessRecord.Digest ?? finalReadinessRecord.digest,
      semanticKImplFinalChecker: finalKImplCall.record.checker,
      semanticKImplFinalDigest:
        finalKImplCall.record.Digest ?? finalKImplCall.record.digest,
      semanticKImplFinalReady: true,
      ruleCount: KERNEL_RULES0.length,
      layerCount: layerResults.length,
      coveredRules: [...KERNEL_RULES0],
      missingRules: [],
      layers: layerResults,
      rules: ruleResults,
      allCheckerModulesDigest: digestCanonical0(
        layerResults.map((layer) => ({
          layerId: layer.layerId,
          moduleSourceDigest: layer.moduleSourceDigest,
          testSourceDigest: layer.testSourceDigest,
          checkerBindingDigest: layer.checkerBindingDigest,
        })),
      ),
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

async function loadLayer0(layer) {
  try {
    const moduleUrl = new URL(layer.modulePath, import.meta.url);
    const testUrl = new URL(layer.testPath, import.meta.url);
    const moduleBytes = readFileSync(moduleUrl);
    const testBytes = readFileSync(testUrl);
    const moduleText = moduleBytes.toString('utf8');
    const testText = testBytes.toString('utf8');
    const moduleNamespace = await import(moduleUrl.href);
    const proofChecker = moduleNamespace[layer.proofChecker];
    const readinessChecker = moduleNamespace[layer.readinessChecker];
    const supportedRules = moduleNamespace[layer.supportedRulesExport];

    if (typeof proofChecker !== 'function') {
      return validationReject0(
        ['proofChecker'],
        'semantic layer module does not export the declared proof checker',
        { layerId: layer.layerId, proofChecker: layer.proofChecker },
      );
    }
    if (typeof readinessChecker !== 'function') {
      return validationReject0(
        ['readinessChecker'],
        'semantic layer module does not export the declared readiness checker',
        { layerId: layer.layerId, readinessChecker: layer.readinessChecker },
      );
    }
    if (!Array.isArray(supportedRules)) {
      return validationReject0(
        ['supportedRulesExport'],
        'semantic layer module does not export a supported-rule array',
        {
          layerId: layer.layerId,
          supportedRulesExport: layer.supportedRulesExport,
        },
      );
    }
    if (!hasExportedFunction0(moduleText, layer.proofChecker)
        || !hasExportedFunction0(moduleText, layer.readinessChecker)) {
      return validationReject0(
        ['modulePath'],
        'semantic layer source does not contain the declared exported checker functions',
        {
          layerId: layer.layerId,
          proofChecker: layer.proofChecker,
          readinessChecker: layer.readinessChecker,
        },
      );
    }

    const missingRuleMarkers = layer.rules.filter(
      (ruleName) => !moduleText.includes(ruleName),
    );
    if (missingRuleMarkers.length !== 0) {
      return validationReject0(
        ['modulePath'],
        'semantic layer source is missing a declared rule marker',
        { layerId: layer.layerId, missingRuleMarkers },
      );
    }

    const missingTestMarkers = layer.rules.filter(
      (ruleName) => !testText.includes(ruleName),
    );
    const testCaseCount = (testText.match(/\btest\s*\(/g) ?? []).length;
    const negativeTestMarkerPresent = /\brejects?\b/i.test(testText);
    if (missingTestMarkers.length !== 0
        || testCaseCount < 2
        || !negativeTestMarkerPresent) {
      return validationReject0(
        ['testPath'],
        'semantic layer test source does not expose the required positive/negative contract inventory',
        {
          layerId: layer.layerId,
          missingTestMarkers,
          testCaseCount,
          negativeTestMarkerPresent,
        },
      );
    }

    return validationAcceptWith0({
      kind: 'K0SemanticLayerLoad0NF',
      layerId: layer.layerId,
      modulePath: layer.modulePath,
      testPath: layer.testPath,
      proofChecker: layer.proofChecker,
      readinessChecker: layer.readinessChecker,
      supportedRulesExport: layer.supportedRulesExport,
      moduleSourceDigest: digestBytes0(moduleBytes),
      moduleByteCount: moduleBytes.length,
      testSourceDigest: digestBytes0(testBytes),
      testByteCount: testBytes.length,
      testCaseCount,
      negativeTestMarkerPresent: true,
    }, {
      proofChecker,
      readinessChecker,
      supportedRules: [...supportedRules],
      moduleSourceDigest: digestBytes0(moduleBytes),
      moduleByteCount: moduleBytes.length,
      testSourceDigest: digestBytes0(testBytes),
      testByteCount: testBytes.length,
      testCaseCount,
    });
  } catch (error) {
    return validationReject0(
      [],
      'semantic layer source or module could not be loaded deterministically',
      {
        layerId: layer.layerId,
        errorName: error?.name ?? null,
        errorMessage: error?.message ?? String(error),
      },
    );
  }
}

function makeMalformedDispatchProbe0(ruleName) {
  const term = makeSemanticConst0(`k0.probe.${ruleName}`, 'Term');
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: `k0.probe.${ruleName}`,
      RuleName: ruleName,
      Conclusion: makeSemanticEqJudgment0(term, term),
      Payload: { op: '__k0_invalid_dispatch_probe__' },
    }),
  ]);
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'K0 semantic conformance input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'K0SemanticConformanceInput0') {
    return validationReject0(
      ['kind'],
      'K0 semantic conformance kind must be K0SemanticConformanceInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `K0 semantic conformance version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
    'KImpl',
    'SemanticProofDAG',
    'LegacyConformance',
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'K0 semantic conformance input is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KImpl)) {
    return validationReject0(
      ['KImpl'],
      'K0 semantic conformance KImpl must be an object',
      { actual: typeof input.KImpl },
    );
  }
  if (!isPlainObject0(input.LegacyConformance)) {
    return validationReject0(
      ['LegacyConformance'],
      'K0 semantic conformance legacy suite must be an object',
      { actual: typeof input.LegacyConformance },
    );
  }
  if (!isPlainObject0(input.Binding)
      || !sameCanonical0(input.Binding, K0_SEMANTIC_CONFORMANCE_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'K0 semantic conformance binding must match the executable checker boundary',
      {
        expected: K0_SEMANTIC_CONFORMANCE_BINDING0,
        actual: input.Binding,
      },
    );
  }
  if (!isPlainObject0(input.Policy)
      || !sameCanonical0(input.Policy, K0_SEMANTIC_CONFORMANCE_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'K0 semantic conformance policy must match the fail-closed policy',
      {
        expected: K0_SEMANTIC_CONFORMANCE_POLICY0,
        actual: input.Policy,
      },
    );
  }

  const allowed = new Set([
    'kind',
    'version',
    'KImpl',
    'SemanticProofDAG',
    'LegacyConformance',
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'K0 semantic conformance rejects caller-supplied soundness or readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  return validationAccept0({
    kind: 'K0SemanticConformanceInputShape0NF',
    legacySuiteKind: input.LegacyConformance.kind ?? null,
  });
}

function hasExportedFunction0(source, name) {
  const pattern = new RegExp(
    `export\\s+(?:async\\s+)?function\\s+${escapeRegExp0(name)}\\s*\\(`,
  );
  return pattern.test(source);
}

function escapeRegExp0(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function digestBytes0(bytes) {
  return Object.freeze({
    alg: 'SHA256',
    hex: createHash('sha256').update(bytes).digest('hex'),
  });
}

function isKImplFinalReady0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.semanticKernelReady === true
    && nf?.finalTheoremReady === true
    && nf?.publicTheoremEmissionAllowed === true;
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

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
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

function validationAcceptWith0(nf, extra) {
  return { ok: true, nf, ...extra };
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
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}
