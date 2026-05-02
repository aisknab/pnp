#!/usr/bin/env node
import {
  writeMaterializedBoot0Files0,
} from '../pcc-boot-materialized0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const filtered = args.filter((arg) => arg !== '--full');
const outputDir = filtered[0] ?? './materialized-boot0';

const out = await writeMaterializedBoot0Files0(outputDir);

if (full) {
  console.log(JSON.stringify(out, null, 2));
} else {
  console.log(JSON.stringify({
    tag: out.tag,
    checker: out.checker,
    digest: out.Digest ?? out.digest,
    outputDir: out.NF?.outputDir ?? out.nf?.outputDir ?? outputDir,
    files: out.NF?.files ?? out.nf?.files ?? [],
  }, null, 2));
}

if (out.tag !== 'accept') {
  process.exitCode = 1;
}
