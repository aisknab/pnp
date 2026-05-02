#!/usr/bin/env node

import {
  writeMaterializedFinalCertificateFiles0,
} from '../pcc-final-certificate-materialized0.mjs';

const args = process.argv.slice(2);
const outDir = args.find((arg) => !arg.startsWith('--')) ?? './materialized-final-certificate0';
const full = args.includes('--full');

const result = await writeMaterializedFinalCertificateFiles0(outDir);

if (full) {
  console.log(JSON.stringify(result.checked, null, 2));
} else {
  console.log(JSON.stringify({
    tag: result.checked.tag,
    checker: result.checked.checker,
    digest: result.checked.Digest,
    certificateDigest: result.checked.NF.certificateDigest,
    files: result.files,
  }, null, 2));
}
