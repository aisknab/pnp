import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  printExample,
} from './lib.mjs';

const root = fileURLToPath(new URL('../../', import.meta.url));
const relativeSealPath = 'proof-artifacts/final-pnp-proof-report-hardened-7072f8d/release-seal.json';
const ledgerPath = path.join(
  root,
  'proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS',
);
const sealPath = path.join(root, relativeSealPath);

const ledger = readFileSync(ledgerPath, 'utf8');
const ledgerLine = ledger
  .split(/\r?\n/u)
  .find((line) => line.endsWith(`  ${relativeSealPath}`));

assert.ok(ledgerLine, `No checksum ledger entry for ${relativeSealPath}`);
const expectedSha256 = ledgerLine.slice(0, 64);
const sealBytes = readFileSync(sealPath);
const actualSha256 = createHash('sha256').update(sealBytes).digest('hex');
assert.equal(actualSha256, expectedSha256);

const changedBytes = Buffer.from(sealBytes);
changedBytes[0] ^= 0x01;
const changedSha256 = createHash('sha256').update(changedBytes).digest('hex');
assert.notEqual(changedSha256, expectedSha256);

printExample({
  id: '08-release-seal',
  concept: 'A release seal and SHA-256 ledger identify exact published bytes',
  humanInput: {
    passing: relativeSealPath,
    failing: 'The same in-memory byte sequence with its first byte changed before hashing.',
  },
  expectedCertificate: `SHA-256 ${expectedSha256} recorded in the sealed bundle ledger.`,
  passingCase: {
    status: 'match',
    expectedSha256,
    actualSha256,
    bytes: sealBytes.length,
  },
  failingCase: {
    status: 'mismatch',
    expectedSha256,
    actualSha256: changedSha256,
  },
  proves: 'The current release-seal.json bytes match their listed SHA-256 value and a one-byte mutation does not.',
  doesNotProve: 'A matching hash does not prove that the seal contents, checker, generated artefacts, or mathematical theorem are correct.',
});
