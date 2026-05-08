#!/usr/bin/env node

import {
  writeConcreteFinalAcceptanceReplayFiles0,
} from '../pcc-final-acceptance-replay0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-final-acceptance-replay0';
const full = args.includes('--full');

const result = await writeConcreteFinalAcceptanceReplayFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    finalAcceptanceReplayClosed: result.checked.NF.finalAcceptanceReplayClosed,
    runId: result.checked.NF.runId,
    generatorIsGeneratePCCPack: result.checked.NF.generatorIsGeneratePCCPack,
    checkAcceptRunAccepted: result.checked.NF.checkAcceptRunAccepted,
    replayAccepted: result.checked.NF.replayAccepted,
    finalVerdictAccepted: result.checked.NF.finalVerdictAccepted,
    checkPCCPackexpAccepted: result.checked.NF.checkPCCPackexpAccepted,
    verdict: result.checked.NF.verdict,
    publicConclusionAntecedent: result.checked.NF.publicConclusionAntecedent,
    publicConclusionConsequent: result.checked.NF.publicConclusionConsequent,
    publicConclusionConditional: result.checked.NF.publicConclusionConditional,
    checkPCCPackexpGeneratedPackageImplication:
      result.checked.NF.checkPCCPackexpGeneratedPackageImplication,
    checkPCCPackexpConcreteCoverageComplete:
      result.checked.NF.checkPCCPackexpConcreteCoverageComplete,
    checkPCCPackexpPCCPackLinkageComplete:
      result.checked.NF.checkPCCPackexpPCCPackLinkageComplete,
    acceptRunDigest: result.checked.NF.acceptRunDigest,
    pccPackDigest: result.checked.NF.pccPackDigest,
    checkPCCPackexpRecordDigest: result.checked.NF.checkPCCPackexpRecordDigest,
    files: result.files,
  }, null, 2));
}
