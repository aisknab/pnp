#!/usr/bin/env node

import {
  ResolveMaterializedDigest0,
} from '../pcc-materialized-digest-resolver0.mjs';

const args = process.argv.slice(2);
const full = args.includes('--full');
const bytes = args.includes('--bytes');

const dirIndex = args.indexOf('--dir');
const fixtureDir = dirIndex >= 0
  ? args[dirIndex + 1]
  : undefined;

const digest = args.find((arg, index) => (
  !arg.startsWith('--') &&
  index !== dirIndex + 1
));

if (!digest) {
  console.log(JSON.stringify({
    tag: 'reject',
    checker: 'resolve-materialized-digest0',
    coord: 'resolve-materialized-digest0.args',
    path: ['argv'],
    witness: {
      reason: 'usage: node ./bin/resolve-materialized-digest0.mjs <sha256-hex> [--dir ./materialized-fixtures0] [--full] [--bytes]',
    },
  }, null, 2));

  process.exitCode = 1;
} else {
  const out = await ResolveMaterializedDigest0(digest, {
    ...(fixtureDir ? { fixtureDir } : {}),
    includeBytes: full || bytes,
  });

  console.log(JSON.stringify(full ? out : summarizeResolution0(out, bytes), null, 2));

  if (out.tag !== 'accept') {
    process.exitCode = 1;
  }
}

function summarizeResolution0(out, includeBytes) {
  if (out.tag === 'accept') {
    const summary = {
      tag: out.tag,
      checker: out.checker,
      digest: out.NF.digest,
      filename: out.NF.filename,
      filePath: out.NF.filePath,
      matchedDigestKinds: out.NF.matchedDigestKinds,
      reverseLookupOnly: out.NF.reverseLookupOnly,
      notCryptographicInversion: out.NF.notCryptographicInversion,
      fileBytesSha256: out.NF.fileBytesSha256,
      canonicalBytesSha256: out.NF.canonicalBytesSha256,
      canonicalObjectDigest: out.NF.canonicalObjectDigest,
      recordDigest: out.Digest,
    };

    if (includeBytes) {
      summary.fileBytes = out.FileBytes;
      summary.canonicalBytes = out.CanonicalBytes;
    }

    return summary;
  }

  return {
    tag: out.tag,
    checker: out.checker,
    coord: out.Coord,
    path: out.Path,
    witness: out.Witness,
    digest: out.Digest,
  };
}