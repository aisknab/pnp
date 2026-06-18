#!/usr/bin/env node

import {
  CheckMaterializedPCCPackShellFile0,
  summarizeMaterializedShellFileRecord0,
} from '../pcc-materialized-loader0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const requireCanonicalEnvelopeBytes = args.includes('--canonical-envelope-bytes');
const filePath = args.find((arg) => !arg.startsWith('--'));

if (!filePath) {
  console.log(JSON.stringify({
    tag: 'reject',
    checker: 'check-materialized-shell0',
    coord: 'check-materialized-shell0.args',
    path: ['argv'],
    witness: {
      reason: 'usage: node ./bin/check-materialized-shell0.mjs <MaterializedPCCPack0.json> [--full] [--canonical-envelope-bytes]',
    },
  }, null, 2));

  process.exitCode = 1;
} else {
  const out = await CheckMaterializedPCCPackShellFile0(filePath, {
    requireCanonicalEnvelopeBytes,
  });

  console.log(JSON.stringify(full ? out : summarizeMaterializedShellFileRecord0(out), null, 2));

  if (out.tag !== 'accept') {
    process.exitCode = 1;
  }
}