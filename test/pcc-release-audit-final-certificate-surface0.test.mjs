import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
} from '../pcc-release-audit0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function makeAcceptedFinalCertificatePublicStatusRecord0() {
  const nf = {
    kind: 'FinalCertificatePublicStatus0NF',
    checker: 'CheckFinalCertificatePublicStatus0',
    version: 0,
    phaseOrder: [],
    materializedPath: true,
    syntheticRunAll: false,
    status: 'accepted',
    verdict: 'accept',
    acceptedCertificate: true,
    replayAccepted: true,
    publicConclusionEmitted: true,
    publicConclusion: {
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
      conditional: true,
    },
    claimBoundary: 'conditional-on-accepted-final-certificate',
    checkerTarget: 'CheckPCCPackexp',
    generator: 'GeneratePCCPack',
    runId: 'release-audit-final-certificate-surface.test',
    certificateDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '1111111111111111111111111111111111111111111111111111111111111111',
    },
    finalVerdictDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '2222222222222222222222222222222222222222222222222222222222222222',
    },
    acceptRunDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '3333333333333333333333333333333333333333333333333333333333333333',
    },
    pccPackDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '4444444444444444444444444444444444444444444444444444444444444444',
    },
    canonicalByteRoots: {
      coreBytesDigest: {
        alg: 'SHA256',
        bytes: 'canonical-json-v0',
        hex: '5555555555555555555555555555555555555555555555555555555555555555',
      },
      packBytesDigest: {
        alg: 'SHA256',
        bytes: 'canonical-json-v0',
        hex: '6666666666666666666666666666666666666666666666666666666666666666',
      },
    },
    acceptanceTranscript: {
      transcriptDigest: {
        alg: 'SHA256',
        bytes: 'canonical-json-v0',
        hex: '7777777777777777777777777777777777777777777777777777777777777777',
      },
      auditLogDigest: {
        alg: 'SHA256',
        bytes: 'canonical-json-v0',
        hex: '8888888888888888888888888888888888888888888888888888888888888888',
      },
      rejectLogCount: 0,
    },
    releaseAuditAttached: false,
    releaseAuditDigest: null,
    releaseAuditStatus: 'not-attached-to-this-materialized-certificate-yet',
    linkageDigest: null,
    syntheticMarkerCount: 0,
    forbiddenMarkerCount: 0,
    allowSyntheticScaffoldMarker: true,
  };

  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckFinalCertificatePublicStatus0',
    version: 0,
    NF: nf,
    Digest: digest,
    Ledger: [],
    nf,
    digest,
    ledger: [],
  };
}

test('CheckReleaseAudit0 reports the final-certificate public-status gate summary', async () => {
  const out = await CheckReleaseAudit0(makeReleaseAuditConfig0({
    runSyntaxCheck: false,
    runRunAll: false,
    runMutationCheck: false,
    runCliSmoke: false,
    runPublicSurfaceFreeze: false,
    runMaterializedPublicStatusGate: false,
    runFinalCertificatePublicStatusGate: true,
    finalCertificatePublicStatusGateRunner: async () => makeAcceptedFinalCertificatePublicStatusRecord0(),
  }));

  assert.equal(out.tag, 'accept', JSON.stringify({
    coord: out.Coord ?? out.coord ?? null,
    path: out.Path ?? out.path ?? null,
    witness: out.Witness ?? out.witness ?? null,
    ledger: out.Ledger ?? out.ledger ?? null,
  }, null, 2));
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.NF.finalCertificatePublicStatusGate, true);
  assert.equal(out.NF.finalCertificatePublicStatusGateSummary.status, 'accepted');
  assert.equal(out.NF.finalCertificatePublicStatusGateSummary.verdict, 'accept');
  assert.equal(out.NF.finalCertificatePublicStatusGatePublicConclusionEmitted, true);
  assert.equal(out.NF.finalCertificatePublicStatusGateSummary.publicConclusion.consequent, 'P = NP');
  assert.deepEqual(
    out.NF.finalCertificatePublicStatusGateCertificateDigest,
    out.NF.finalCertificatePublicStatusGateSummary.certificateDigest,
  );
});

test('CheckReleaseAudit0 rejects a final-certificate public-status gate without public conclusion emission', async () => {
  const bad = makeAcceptedFinalCertificatePublicStatusRecord0();

  bad.NF = {
    ...bad.NF,
    publicConclusionEmitted: false,
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
    runFinalCertificatePublicStatusGate: true,
    finalCertificatePublicStatusGateRunner: async () => bad,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.Coord, 'CheckReleaseAudit0.finalCertificatePublicStatusGate');
  assert.deepEqual(out.Path, ['finalCertificatePublicStatusGate', 'NF', 'publicConclusionEmitted']);
});
