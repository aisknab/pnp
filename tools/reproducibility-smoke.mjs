#!/usr/bin/env node

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const BUNDLE = 'proof-artifacts/final-pnp-proof-report-hardened-7072f8d';
const CLAIM = 'CheckPCCPackexp(GeneratePCCPack())=accept => P = NP';

function sha256(file) {
  return createHash('sha256').update(readFileSync(file)).digest('hex');
}

function parseLedgerLine(line, source) {
  const match = /^([0-9a-f]{64})  (.+)$/u.exec(line);
  assert.ok(match, `${source}: malformed SHA-256 ledger line: ${line}`);
  return { expected: match[1], file: match[2] };
}

const ledgerPath = path.join(ROOT, BUNDLE, 'SHA256SUMS');
const detachedPath = path.join(ROOT, BUNDLE, 'SHA256SUMS.sha256');
const ledgerLines = readFileSync(ledgerPath, 'utf8')
  .split(/\r?\n/u)
  .filter((line) => line.length > 0);

for (const line of ledgerLines) {
  const { expected, file } = parseLedgerLine(line, 'SHA256SUMS');
  const absolute = path.resolve(ROOT, file);
  const relative = path.relative(ROOT, absolute);
  assert.ok(
    !relative.startsWith('..') && !path.isAbsolute(relative),
    `checksum path escapes repository root: ${file}`,
  );
  assert.equal(sha256(absolute), expected, `SHA-256 mismatch: ${file}`);
}

const detachedLines = readFileSync(detachedPath, 'utf8')
  .split(/\r?\n/u)
  .filter((line) => line.length > 0);
assert.equal(detachedLines.length, 1, 'detached checksum file must contain one line');
const detached = parseLedgerLine(detachedLines[0], 'SHA256SUMS.sha256');
assert.equal(detached.file, `${BUNDLE}/SHA256SUMS`, 'detached checksum names the wrong ledger path');
assert.equal(sha256(ledgerPath), detached.expected, 'SHA256SUMS detached hash mismatch');

const seal = JSON.parse(readFileSync(path.join(ROOT, BUNDLE, 'release-seal.json'), 'utf8'));
const summary = JSON.parse(readFileSync(path.join(ROOT, BUNDLE, 'final-pnp-proof-report.summary.json'), 'utf8'));
const full = JSON.parse(readFileSync(path.join(ROOT, BUNDLE, 'final-pnp-proof-report.full.json'), 'utf8'));

assert.equal(seal.sourceTag, 'final-pnp-proof-report-hardened-7072f8d');
assert.equal(seal.sourceCommit, '7072f8d0bda6d44d240f9bb3fad624fd357e1278');
assert.equal(seal.sealedArtifactTag, 'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed');
assert.equal(seal.publicConclusionStatement, CLAIM);
assert.equal(seal.validation.tests, 1121);
assert.equal(seal.validation.pass, 1121);
assert.equal(seal.validation.fail, 0);

for (const [name, envelope, record] of [
  ['summary', summary, summary],
  ['full', full, full.NF],
]) {
  assert.equal(envelope.tag, 'accept', `${name}: tag mismatch`);
  assert.equal(envelope.checker, 'CheckFinalPNPProofReport0', `${name}: checker mismatch`);
  assert.equal(record.finalPNPProofReportAccepted, true, `${name}: final report is not accepted`);
  assert.equal(record.checkPCCPackexpAccepted, true, `${name}: package checker is not accepted`);
  assert.equal(record.publicConclusionStatement, CLAIM, `${name}: public claim boundary mismatch`);
  assert.deepEqual(record.theorem, seal.theorem, `${name}: theorem fields differ from release seal`);
}

console.log(JSON.stringify({
  status: 'ok',
  bundle: BUNDLE,
  checksumEntriesVerified: ledgerLines.length,
  detachedLedgerHashVerified: true,
  summaryAccepted: true,
  fullAccepted: true,
  claimBoundary: CLAIM,
  evidenceBoundary: 'artefact identity and recorded implementation fields only; not theorem correctness',
}, null, 2));
