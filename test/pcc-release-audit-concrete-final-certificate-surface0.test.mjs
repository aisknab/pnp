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

  assert.equal(out.NF.concreteFinalCertificatePublicStatusGateStatusUsesConcreteFinalCertificate, true);

  const summary = summarizeReleaseAudit0(out);

  assert.equal(summary.tag, 'accept');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateSummary.status, 'accepted');
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteRows, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteKBundle, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteHardCheck, true);
  assert.equal(summary.concreteFinalCertificatePublicStatusGateConcreteFinalIntegration, true);
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
