#!/usr/bin/env node

import { EnforceHistoricalReplayCli0 } from '../pcc-legacy-replay-gate0.mjs';

import {
  writeReleaseAuditFinalCertificateGateFiles0,
} from '../pcc-release-audit-final-certificate-gate0.mjs';

EnforceHistoricalReplayCli0({ entrypoint: 'bin/write-release-audit-final-certificate-gate0.mjs' });

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './release-audit-final-certificate-gate0';
const full = args.includes('--full');

const result = await writeReleaseAuditFinalCertificateGateFiles0(outDir, {
  historicalReplay: true,
});

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    releaseAuditDigest: result.checked.NF.releaseAuditDigest,
    certificateDigest: result.checked.NF.certificateDigest,
    finalVerdictDigest: result.checked.NF.finalVerdictDigest,
    publicConclusion: result.checked.NF.publicConclusion,
    files: result.files,
  }, null, 2));
}
