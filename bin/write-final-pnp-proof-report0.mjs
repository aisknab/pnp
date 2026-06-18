#!/usr/bin/env node

import {
  writeFinalPNPProofReportFiles0,
} from '../pcc-final-proof-report0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './final-pnp-proof-report0';
const full = args.includes('--full');

const result = await writeFinalPNPProofReportFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    finalPNPProofReportAccepted: result.checked.NF.finalPNPProofReportAccepted,
    status: result.checked.NF.status,
    theorem: result.checked.NF.theorem,
    claimBoundary: result.checked.NF.claimBoundary,
    finalPNPReleaseGateAccepted: result.checked.NF.finalPNPReleaseGateAccepted,
    finalPNPCertificateAccepted: result.checked.NF.finalPNPCertificateAccepted,
    releaseAuditAccepted: result.checked.NF.releaseAuditAccepted,
    finalAcceptanceReplayClosed: result.checked.NF.finalAcceptanceReplayClosed,
    verdict: result.checked.NF.verdict,
    generator: result.checked.NF.generator,
    checkerName: result.checked.NF.checkerName,
    generatorIsGeneratePCCPack: result.checked.NF.generatorIsGeneratePCCPack,
    checkPCCPackexpAccepted: result.checked.NF.checkPCCPackexpAccepted,
    checkAcceptRunAccepted: result.checked.NF.checkAcceptRunAccepted,
    replayAccepted: result.checked.NF.replayAccepted,
    finalVerdictAccepted: result.checked.NF.finalVerdictAccepted,
    publicConclusionAntecedent: result.checked.NF.publicConclusionAntecedent,
    publicConclusionConsequent: result.checked.NF.publicConclusionConsequent,
    publicConclusionConditional: result.checked.NF.publicConclusionConditional,
    publicConclusionStatement: result.checked.NF.publicConclusionStatement,
    finalPNPReleaseGateRecordDigest: result.checked.NF.finalPNPReleaseGateRecordDigest,
    releaseAuditDigest: result.checked.NF.releaseAuditDigest,
    certificateDigest: result.checked.NF.certificateDigest,
    acceptRunDigest: result.checked.NF.acceptRunDigest,
    pccPackDigest: result.checked.NF.pccPackDigest,
    acceptanceTranscriptDigest: result.checked.NF.acceptanceTranscriptDigest,
    finalVerdictRecordDigest: result.checked.NF.finalVerdictRecordDigest,
    checkPCCPackexpRecordDigest: result.checked.NF.checkPCCPackexpRecordDigest,
    reportDigest: result.checked.NF.reportDigest,
    files: result.files,
  }, null, 2));
}
