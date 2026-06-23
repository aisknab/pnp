import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  makeKernelConformanceSuite0,
  makeReflectionRegistry0,
  makeSigmaRegistry0,
  makeSyntheticKImpl0,
} from './pcc-kimpl0.mjs';

import {
  CheckKBundleFiniteRelSuccessor0,
  makeKBundleFiniteRelSuccessor0,
} from './pcc-kbundle-finiterel-successor0.mjs';

import {
  makeKImplFiniteRelSuccessor0,
} from './pcc-kimpl-finiterel-successor0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
} from './pcc-kernel-finiterel-semantic0.mjs';

import {
  CheckK0SemanticConformance0,
  makeK0SemanticConformanceInput0,
} from './pcc-k0-semantic-conformance0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const KBUNDLE_K0_CONFORMANCE_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const KBUNDLE_K0_CONFORMANCE_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'KBundleSemanticK0ConformanceReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKImplInputMustRemainDevelopmentPurpose: true,
  predecessorKBundleMustRemainDevelopmentOnly: true,
  predecessorKBundleCannotImplyK0SemanticConformance: true,
  semanticConformanceComputedInternally: true,
  semanticConformanceBindsCheckerAndTestSourceDigests: true,
  semanticConformanceScopeIsExecutableContractOnly: true,
  mathematicalMetasoundnessRequiresIndependentAudit: true,
  legacySigmaRegistryIsStructuralOnly: true,
  legacyReflectionRegistryIsStructuralOnly: true,
  finalTheoremRequiresSemanticKImplReadiness: true,
  finalTheoremRequiresSemanticConformance: true,
  finalTheoremRequiresSemanticSigmaDerivations: true,
  finalTheoremRequiresSemanticReflectionSoundness: true,
  publicTheoremEmissionRequiresBundleFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const KBUNDLE_K0_CONFORMANCE_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'KBundleSemanticK0ConformanceCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorKBundleChecker: 'CheckKBundleFiniteRelSuccessor0',
  semanticConformanceChecker: 'CheckK0SemanticConformance0',
});

export function makeKBundleK0ConformanceSuccessor0({
  KImpl = makeSyntheticKImpl0(),
 