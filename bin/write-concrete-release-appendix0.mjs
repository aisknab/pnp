#!/usr/bin/env node

import {
  writeConcreteReleaseAppendixFiles0,
} from '../pcc-concrete-release-appendix0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './concrete-release-appendix0';
const full = args.includes('--full');

const result = await writeConcreteReleaseAppendixFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    releaseAuditDigest: result.checked.NF.releaseAuditDigest,
    pccPackDigest: result.checked.NF.pccPackDigest,
    finalVerdictDigest: result.checked.NF.finalVerdictDigest,
    certificateDigest: result.checked.NF.certificateDigest,
    concreteRows: result.checked.NF.concreteRows,
    concreteLocalPackages: result.checked.NF.concreteLocalPackages,
    concreteGlobalFirewalls: result.checked.NF.concreteGlobalFirewalls,
    concreteGlobalProofDAG: result.checked.NF.concreteGlobalProofDAG,
    concreteKBundle: result.checked.NF.concreteKBundle,
    kBundleKernelRuleCoverageComplete: result.checked.NF.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: result.checked.NF.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: result.checked.NF.kBundleReflectionProofRefsResolve,
    concreteHardCheck: result.checked.NF.concreteHardCheck,
    hardNoMinCoverageComplete: result.checked.NF.hardNoMinCoverageComplete,
    hardImportPolicyComplete: result.checked.NF.hardImportPolicyComplete,
    concreteFinalIntegration: result.checked.NF.concreteFinalIntegration,
    finalIntegrationGPackFieldCoverageComplete: result.checked.NF.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: result.checked.NF.finalIntegrationRowFamGCoverageComplete,
    publicConclusion: result.checked.NF.publicConclusion,
    generatedPCCPackexpCheckPCCPackexp0: result.checked.NF.generatedPCCPackexpCheckPCCPackexp0,
    generatedPCCPackexpCheckPCCPackexp0Accepted: result.checked.NF.generatedPCCPackexpCheckPCCPackexp0Accepted,
    generatedPCCPackexpCheckPCCPackexp0Checker: result.checked.NF.generatedPCCPackexpCheckPCCPackexp0Checker,
    generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication:
      result.checked.NF.generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication,
    generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete:
      result.checked.NF.generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete:
      result.checked.NF.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete,
    files: result.files,
  }, null, 2));
}
