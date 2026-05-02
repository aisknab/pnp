#!/usr/bin/env node
import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

import {
  writeMaterializedKBundleFiles0,
} from '../pcc-k-materialized0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const outputDir = args.find((arg) => !arg.startsWith('--')) ?? './materialized-kbundle0';

const out = await writeMaterializedKBundleFiles0(outputDir);

if (full) {
  console.log(stableStringify0(out));
} else {
  console.log(stableStringify0({
    tag: out.tag,
    checker: out.checker,
    outputDir: out.NF?.outputDir ?? null,
    fileCount: out.NF?.fileCount ?? null,
    digest: out.Digest ?? out.digest ?? null,
    coord: out.Coord ?? out.coord ?? null,
    path: out.Path ?? out.path ?? null,
  }));
}

process.exitCode = out.tag === 'accept' ? 0 : 1;
