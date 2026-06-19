#!/usr/bin/env node
import { createHash } from 'node:crypto';
import { readFileSync, statSync } from 'node:fs';

const DOCS_TAG = 'final-pnp-proof-report-docs-hardened-7072f8d-public-access-sealed';
const SOURCE_TAG = 'final-pnp-proof-report-hardened-7072f8d';
const SOURCE_COMMIT = '7072f8d0bda6d44d240f9bb3fad624fd357e1278';
const ARTIFACT_TAG = 'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed';
const DOCS_DIR = 'docs-release/public-access-7072f8d';

const sha256 = (file) => createHash('sha256').update(readFileSync(file)).digest('hex');
const assert = (condition, message) => { if (!condition) throw new Error(message); };

const seal = JSON.parse(readFileSync(`${DOCS_DIR}/release-seal.json`, 'utf8'));
assert(seal.kind === 'PNPDocumentationReleaseSeal', 'release seal kind mismatch');
assert(seal.scope === 'documentation-only public-access revision', 'release seal scope mismatch');
assert(seal.docsTag === DOCS_TAG, 'docs tag mismatch');
assert(seal.sourceTag === SOURCE_TAG, 'source tag mismatch');
assert(seal.sourceCommit === SOURCE_COMMIT, 'source commit mismatch');
assert(seal.artifactTag === ARTIFACT_TAG, 'artifact tag mismatch');
assert(Array.isArray(seal.files) && seal.files.length === 2, 'release seal file inventory mismatch');

for (const entry of seal.files) {
  const rootPath = entry.path;
  const releasePath = `${DOCS_DIR}/${entry.path}`;
  assert(statSync(rootPath).size === entry.bytes, `${rootPath}: byte count mismatch`);
  assert(statSync(releasePath).size === entry.bytes, `${releasePath}: byte count mismatch`);
  assert(sha256(rootPath) === entry.sha256, `${rootPath}: SHA-256 mismatch`);
  assert(sha256(releasePath) === entry.sha256, `${releasePath}: SHA-256 mismatch`);
  assert(readFileSync(rootPath).equals(readFileSync(releasePath)), `${entry.path}: root/release copy mismatch`);
}

const pdf = seal.files.find((entry) => entry.path === 'canonical_proof_report.pdf');
const texEntry = seal.files.find((entry) => entry.path === 'canonical_proof_report.tex');
assert(pdf && texEntry, 'canonical report files missing from release seal');
const expectedSums = `${pdf.sha256}  canonical_proof_report.pdf\n${texEntry.sha256}  canonical_proof_report.tex\n`;
assert(readFileSync(`${DOCS_DIR}/SHA256SUMS`, 'utf8') === expectedSums, 'SHA256SUMS mismatch');

const tex = readFileSync('canonical_proof_report.tex', 'utf8');
for (const required of [DOCS_TAG, 'https://github.com/aisknab/pnp', 'CheckPCCPackexp(GeneratePCCPack())=accept', 'Documentation-only public-access revision']) {
  assert(tex.includes(required), `canonical TeX missing required text: ${required}`);
}
for (const stale of ['source repository access requests', 'source-access', 'artefact-access', 'If repository access is restricted', 'request source repository access']) {
  assert(!tex.includes(stale), `canonical TeX contains stale access wording: ${stale}`);
}

for (const file of ['README.md', 'CURRENT_RELEASE.md', 'REPRODUCE.md', 'REVIEWER_MAP.md', 'PUBLIC_ACCESS_REVISION.md']) {
  const text = readFileSync(file, 'utf8');
  assert(text.includes(DOCS_TAG), `${file}: missing docs tag`);
  assert(text.includes(pdf.sha256), `${file}: missing PDF hash`);
  assert(text.includes(texEntry.sha256), `${file}: missing TeX hash`);
  assert(!text.includes('__DOCS_'), `${file}: unresolved placeholder`);
}

const artifactFiles = {
  'proof-artifacts/final-pnp-proof-report-hardened-7072f8d/release-seal.json': '03a95ff0baeb5b251577780ecbce51e9b305fb611daddee4db9b05f2621d6bc7',
  'proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS': 'd1da103bbf2867b656e8026b734f81b33bc61deb79dbf3a2d48a16f83e8a2356',
  'proof-artifacts/final-pnp-proof-report-hardened-7072f8d/SHA256SUMS.sha256': '61228d99a2ce57dde4e9fa605626277ad3cb591ff424f73c8c240e28e8a876fa',
};
for (const [file, expectedHash] of Object.entries(artifactFiles)) {
  assert(sha256(file) === expectedHash, `${file}: sealed artefact identity changed`);
}

console.log(JSON.stringify({
  status: 'ok', docsTag: DOCS_TAG,
  pdfSha256: pdf.sha256, pdfBytes: pdf.bytes,
  texSha256: texEntry.sha256, texBytes: texEntry.bytes,
  sourceTag: SOURCE_TAG, sourceCommit: SOURCE_COMMIT, artifactTag: ARTIFACT_TAG,
  theoremOrCheckerChange: false,
}, null, 2));
