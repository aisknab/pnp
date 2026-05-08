#!/usr/bin/env node

import {
  writeFinalPNPCertificateFiles0,
} from '../pcc-final-pnp-certificate0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './final-pnp-certificate0';
const full = args.includes('--full');

const result = await writeFinalPNPCertificateFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    finalPNPCertificateAccepted: result.checked.NF.finalPNPCertificateAccepted,
    status: result.checked.NF.status,
    verdict: result.checked.NF.verdict,
    theorem: result.checked.NF.theorem,
    claimBoundary: result.checked.NF.claimBoundary,
    finalAcceptanceReplayClosed: result.checked.NF.finalAcceptanceReplayClosed,
    generatorIsGeneratePCCPack: result.checked.NF.generatorIsGeneratePCCPack,
    checkAcceptRunAccepted: result.checked.NF.checkAcceptRunAccepted,
    replayAccepted: result.checked.NF.replayAccepted,
    finalVerdictAccepted: result.checked.NF.finalVerdictAccepted,
    checkPCCPackexpAccepted: result.checked.NF.checkPCCPackexpAccepted,
    publicConclusionEmitted: result.checked.NF.publicConclusionEmitted,
    publicConclusionAntecedent: result.checked.NF.publicConclusionAntecedent,
    publicConclusionConsequent: result.checked.NF.publicConclusionConsequent,
    publicConclusionConditional: result.checked.NF.publicConclusionConditional,
    checkPCCPackexpGeneratedPackageImplication:
      result.checked.NF.checkPCCPackexpGeneratedPackageImplication,
    checkPCCPackexpConcreteCoverageComplete:
      result.checked.NF.checkPCCPackexpConcreteCoverageComplete,
    checkPCCPackexpPCCPackLinkageComplete:
      result.checked.NF.checkPCCPackexpPCCPackLinkageComplete,
    releaseAuditDigest: result.checked.NF.releaseAuditDigest,
    concreteFinalAcceptanceReplayRecordDigest:
      result.checked.NF.concreteFinalAcceptanceReplayRecordDigest,
    acceptRunDigest: result.checked.NF.acceptRunDigest,
    pccPackDigest: result.checked.NF.pccPackDigest,
    acceptanceTranscriptDigest: result.checked.NF.acceptanceTranscriptDigest,
    finalVerdictRecordDigest: result.checked.NF.finalVerdictRecordDigest,
    checkPCCPackexpRecordDigest: result.checked.NF.checkPCCPackexpRecordDigest,
    certificateDigest: result.checked.NF.certificateDigest,
    files: result.files,
  }, null, 2));
}
