#!/usr/bin/env node

import {
  writeFinalCertificatePublicStatusFiles0,
} from '../pcc-final-certificate-public-status0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './materialized-final-certificate-public-status0';
const full = args.includes('--full');

const result = await writeFinalCertificatePublicStatusFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    status: result.checked.NF.status,
    publicConclusion: result.checked.NF.publicConclusion,
    certificateDigest: result.checked.NF.certificateDigest,
    finalVerdictDigest: result.checked.NF.finalVerdictDigest,
    files: result.files,
  }, null, 2));
}
