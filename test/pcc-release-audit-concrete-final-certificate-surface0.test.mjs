import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
  summarizeReleaseAudit0,
} from '../pcc-release-audit0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function digestOf0(hex) {
  return {
    alg: 'SHA256',
    bytes: 'canonical-json-v0',
    hex,
  };
}

function makeAcceptedConcreteFinalCertificatePublicStatusRecord0() {
  const nf = {
    kind: 'ConcreteFinalCertificatePublicStatus0NF',
    checker: 'CheckConcreteFinalCertificatePublicStatus0',
    version: 0,
    materializedPath: true,
    syntheticRunAll: false,

    concreteRows: true,
    concreteLocalPackages: true,
    concreteGlobalFirewalls: true,
    concreteGlobalProofDAG: true,

    concreteKBundle: true,
    kBundleKernelRuleCoverageComplete: true,
    kBundleSigmaProofRefsResolve: true,
    kBundleReflectionProofRefsResolve: true,

    concreteHardCheck: true,
    hardCheckerCoverageComplete: true,
    hardRowKeyCoverageComplete: true,
    hardRoutePriorityComplete: true,
    hardProofRefPolicyComplete: true,
    hardHashDisciplineComplete: true,
    hardNoMinCoverageComplete: true,
    hardImportPolicyComplete: true,
    hardReflectionPolicyComplete: true,
    hardBoundsPolicyComplete: true,
    hardDiagnosticsPolicyComplete: true,

    concreteFinalIntegration: true,
    finalIntegrationConcreteGlobalProofDAG: true,
    finalIntegrationGPackFieldCoverageComplete: true,
    finalIntegrationRowFamGCoverageComplete: true,
    finalIntegrationUsesGPack: true,
    rowFamGUsesGPack: true,
    finalTheoremUsesFinalIntegration: true,
    rowFamFinalUsesFinalTheorem: true,
    finalMatchUsesGPack: true,
    satDecisionUsesGPack: true,

    concretePCCPack: true,
    concretePCCPackCoverageDigest: digestOf0('cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc'),
    pccPackPublicConclusionOnlyAfterAcceptRun: true,
    pccPackLinkedToKBundle: true,
    pccPackLinkedToHardCheck: true,
    pccPackLinkedToRows: true,
    pccPackLinkedToLocalPackages: true,
    pccPackLinkedToGlobalFirewalls: true,
    pccPackLinkedToGlobalProofDAG: true,
    pccPackLinkedToGPack: true,
    pccPackLinkedToFinalIntegration: true,
    pccPackLinkedToFinalTheorem: true,
    checkPCCPackexpRecordPresent: true,
    checkPCCPackexpRecordAccepted: true,
    checkPCCPackexpRecordChecker: 'CheckPCCPackexp0',
    checkPCCPackexpRecordDigest: digestOf0('dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd'),
    checkPCCPackexpRecordDigestMatchesNF: true,
    checkPCCPackexpRecordConcretePCCPack: true,
    checkPCCPackexpRecordPccPackDigest: digestOf0('eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee'),
    checkPCCPackexpRecordPccPackDigestMatchesConcreteRun: true,
    checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: true,
    checkPCCPackexpRecordPublicConclusionNotEmitted: true,
    checkPCCPackexpRecordClaimBoundaryConditional: true,
    generatedPCCPackexpEnvelopePresent: true,
    generatedPCCPackexpEnvelopeDigest: digestOf0('ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'),
    generatedPCCPackexpGenCallGeneratePCCPack: true,
    generatedPCCPackexpCoreOnly: true,
    generatedPCCPackexpExcludesAcceptRun: true,
    generatedPCCPackexpPackageMatchesConcreteRun: true,
    generatedPCCPackexpCheckRecordMatchesConcreteRun: true,
    generatedPCCPackexpCheckRecordAccepted: true,
    generatedPCCPackexpCheckRecordChecker: 'CheckPCCPackexp0',
    generatedPCCPackexpCheckRecordDigest: digestOf0('eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee'),
    generatedPCCPackexpCheckRecordDigestMatchesNF: true,
    generatedPCCPackexpCheckRecordClaimBoundaryConditional: true,
    generatedPCCPackexpLinkageGeneratedPackageDigestMatches: true,
    generatedPCCPackexpLinkageCheckRecordDigestMatches: true,
    checkGeneratedPCCPackexpRecordPresent: true,
    checkGeneratedPCCPackexpRecordAccepted: true,
    checkGeneratedPCCPackexpRecordChecker: 'CheckGeneratedPCCPackexp0',
    checkGeneratedPCCPackexpRecordDigest: digestOf0('1212121212121212121212121212121212121212121212121212121212121212'),
    checkGeneratedPCCPackexpRecordDigestMatchesNF: true,
    checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope: true,
    checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope: true,

    generatedPCCPackexpBoot0: true,
    generatedPCCPackexpBoot0Accepted: true,
    generatedPCCPackexpBoot0Kind: 'Boot0',
    generatedPCCPackexpBoot0Digest: digestOf0('1313131313131313131313131313131313131313131313131313131313131313'),
    generatedPCCPackexpBoot0CheckDigest: digestOf0('1414141414141414141414141414141414141414141414141414141414141414'),
    generatedPCCPackexpBoot0CanonicalByteDigest: digestOf0('1515151515151515151515151515151515151515151515151515151515151515'),
    generatedPCCPackexpBoot0RowCount: 11,
    generatedPCCPackexpBoot0KernelRuleCount: 16,
    generatedPCCPackexpBoot0JsonMaterialized: true,
    generatedPCCPackexpBoot0NoFixtureMarkers: true,
    generatedPCCPackexpBoot0BootBatchDigest: digestOf0('1616161616161616161616161616161616161616161616161616161616161616'),
    generatedPCCPackexpBoot0BootAuditDigest: digestOf0('1717171717171717171717171717171717171717171717171717171717171717'),
    generatedPCCPackexpBoot0LinkedToPCCPack: true,
    generatedPCCPackexpBoot0LinkedToCoreDigestMap: true,
    generatedPCCPackexpBoot0DigestMatchesGeneratedPackage: true,
    generatedPCCPackexpBoot0DigestMatchesCoreDigestMap: true,

    finalCertificateUsesConcreteAcceptRun: true,
    statusUsesConcreteFinalCertificate: true,
    publicStatusCertificateDigestMatchesConcrete: true,
    publicStatusFinalVerdictDigestMatchesConcrete: true,
    publicStatusAcceptRunDigestMatchesConcrete: true,
    publicStatusPccPackDigestMatchesConcrete: true,

    status: 'accepted',
    verdict: 'accept',
    publicConclusionEmitted: true,
    publicConclusion: {
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
      conditional: true,
    },

    certificateDigest: digestOf0('1111111111111111111111111111111111111111111111111111111111111111'),
    finalVerdictDigest: digestOf0('2222222222222222222222222222222222222222222222222222222222222222'),
    acceptRunDigest: digestOf0('3333333333333333333333333333333333333333333333333333333333333333'),
    pccPackDigest: digestOf0('4444444444444444444444444444444444444444444444444444444444444444'),

    canonicalByteRoots: {
      coreBytesDigest: digestOf0('5555555555555555555555555555555555555555555555555555555555555555'),
      packBytesDigest: digestOf0('6666666666666666666666666666666666666666666666666666666666666666'),
    },

    acceptanceTranscript: {
      transcriptDigest: digestOf0('7777777777777777777777777777777777777777777777777777777777777777'),
      auditLogDigest: digestOf0('8888888888888888888888888888888888888888888888888888888888888888'),
      rejectLogCount: 0,
    },

    releaseAuditAttached: false,
    releaseAuditDigest: null,
    releaseAuditStatus: 'not-attached-to-this-materialized-certificate-yet',

    concreteFinalCertificateEnvelopeDigest: digestOf0('9999999999999999999999999999999999999999999999999999999999999999'),
    finalCertificatePublicStatusEnvelopeDigest: digestOf0('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa'),
    concreteChainDigest: digestOf0('bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb'),
    linkageDigest: null,

    syntheticMarkerCount: 0,
    forbiddenMarkerCount: 0,
    allowSyntheticScaffoldMarker: true,
  };

  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckConcreteFinalCertificatePublicStatus0',
    version: 0,
    NF: nf,
    Digest: digest,
    Ledger: [],
    nf,
    digest,
    ledger: [],
  };
}

test('CheckReleaseAudit0 reports the concrete final-certificate public-status gate summary', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => (
      makeAcceptedConcreteFinalCertificatePublicStatusRecord0()
    ),
  }));

  assert.equal(out.tag, 'accept', JSON.stringify({
    coord: out.Coord ?? out.coord ?? null,
    path: out.Path ?? out.path ?? null,
    witness: out.Witness ?? out.witness ?? null,
  }, null, 2));

  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGate, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateStatus, 'accepted');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateVerdict, 'accept');
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePublicConclusionEmitted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteRows, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteLocalPackages, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteGlobalProofDAG, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteKBundle, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateKBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateKBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateKBundleReflectionProofRefsResolve, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteHardCheck, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateHardCheckerCoverageComplete, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateHardNoMinCoverageComplete, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateHardImportPolicyComplete, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcreteFinalIntegration, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateFinalIntegrationGPackFieldCoverageComplete, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateFinalIntegrationRowFamGCoverageComplete, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateConcretePCCPack, true);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateConcretePCCPackCoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToKBundle, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToHardCheck, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToRows, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToLocalPackages, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalFirewalls, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalProofDAG, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToGPack, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalIntegration, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalTheorem, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordChecker, 'CheckPCCPackexp0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordConcretePCCPack, true);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigestMatchesConcreteRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionNotEmitted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordClaimBoundaryConditional, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopePresent, true);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpGenCallGeneratePCCPack, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCoreOnly, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpExcludesAcceptRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPackageMatchesConcreteRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordMatchesConcreteRun, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordAccepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordChecker, 'CheckPCCPackexp0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigestMatchesNF, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordClaimBoundaryConditional, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageGeneratedPackageDigestMatches, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageCheckRecordDigestMatches, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordPresent, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordChecker, 'CheckGeneratedPCCPackexp0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Accepted, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Kind, 'Boot0');
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CheckDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CanonicalByteDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0RowCount > 0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0KernelRuleCount > 0, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0JsonMaterialized, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0NoFixtureMarkers, true);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootBatchDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToPCCPack, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToCoreDigestMap, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesGeneratedPackage, true);
  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesCoreDigestMap, true);

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateStatusUsesConcreteFinalCertificate, true);

  const summary = summarizeReleaseAudit0(out);

  assert.equal(summary.tag, 'accept');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateSummary.status, 'accepted');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteRows, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteKBundle, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteHardCheck, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteFinalIntegration, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcretePCCPack, true);
  assert.match(summary.concreteFinalCertificatePublicStatusGateConcretePCCPackCoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToKBundle, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToHardCheck, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToRows, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToLocalPackages, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalFirewalls, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToGlobalProofDAG, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToGPack, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalIntegration, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGatePccPackLinkedToFinalTheorem, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordAccepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordChecker, 'CheckPCCPackexp0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordConcretePCCPack, true);
  assert.match(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPccPackDigestMatchesConcreteRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordPublicConclusionNotEmitted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckPCCPackexpRecordClaimBoundaryConditional, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopePresent, true);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpGenCallGeneratePCCPack, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCoreOnly, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpExcludesAcceptRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpPackageMatchesConcreteRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordMatchesConcreteRun, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordAccepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordChecker, 'CheckPCCPackexp0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordDigestMatchesNF, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpCheckRecordClaimBoundaryConditional, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageGeneratedPackageDigestMatches, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpLinkageCheckRecordDigestMatches, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordPresent, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordAccepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordChecker, 'CheckGeneratedPCCPackexp0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateCheckGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope, true);

  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Accepted, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Kind, 'Boot0');
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CheckDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0CanonicalByteDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0RowCount > 0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0KernelRuleCount > 0, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0JsonMaterialized, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0NoFixtureMarkers, true);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootBatchDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0BootAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToPCCPack, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0LinkedToCoreDigestMap, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesGeneratedPackage, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateGeneratedPCCPackexpBoot0DigestMatchesCoreDigestMap, true);

  assert.equal(summary.concreteFinalCertificatePublicStatusGateSummary.publicConclusion.consequent, 'P = NP');
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without concrete rows', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    concreteRows: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, ['concreteFinalCertificatePublicStatusGate', 'NF', 'concreteRows']);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without concrete PCCPack evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    concretePCCPack: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, ['concreteFinalCertificatePublicStatusGate', 'NF', 'concretePCCPack']);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without CheckPCCPackexp0 evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    checkPCCPackexpRecordPresent: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'checkPCCPackexpRecordPresent',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without GeneratedPCCPackexp0 evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpEnvelopePresent: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpEnvelopePresent',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without CheckGeneratedPCCPackexp0 record evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    checkGeneratedPCCPackexpRecordPresent: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'checkGeneratedPCCPackexpRecordPresent',
  ]);
});

test('CheckReleaseAudit0 rejects a concrete final-certificate gate without Boot0 bridge evidence', async () => {
  const bad = makeAcceptedConcreteFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    generatedPCCPackexpBoot0: false,
  };
  bad.nf = bad.NF;
  bad.Digest = digestCanonical0(bad.NF);
  bad.digest = bad.Digest;

  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: false,
    runConcreteFinalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.concreteFinalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, [
    'concreteFinalCertificatePublicStatusGate',
    'NF',
    'generatedPCCPackexpBoot0',
  ]);
});
