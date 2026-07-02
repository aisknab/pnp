#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const CHECKER = 'CheckPublicReviewChecklist0';
const VERSION = 0;
const COORD = 'PNP-PUBLIC-REVIEW-CHECKLIST-2026-06-27-01';
const OUT = 'artifacts/public-review-checklist/latest-verdict.json';
const BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const FILES = {
  manifest: 'review/PUBLIC_REVIEW_CHECKLIST.json',
  checklistDoc: 'review/PUBLIC_REVIEW_CHECKLIST.md',
  entrypoint: 'PUBLIC_REVIEW.json',
  handoff: 'release/PUBLIC_REVIEW_HANDOFF.json',
  boundary: 'release/PUBLIC_REVIEW_BOUNDARY.json',
  externalReview: 'EXTERNAL_REVIEW_STATUS.md',
  status: 'PNP_STATUS.json'
};

export async function CheckPublicReviewChecklist0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const outputPath = options.outputPath ?? OUT;
  const writeOutput = options.writeOutput ?? true;
  try {
    const manifestRead = await readJson0(root, options.manifestPath ?? FILES.manifest, options.manifestOverride);
    if (manifestRead.tag === 'reject') return write0(root, outputPath, writeOutput, manifestRead);
    const manifest = manifestRead.value;
    const manifestCheck = validateManifest0(manifest);
    if (manifestCheck.tag === 'reject') return write0(root, outputPath, writeOutput, manifestCheck);

    const statusRead = await readJson0(root, FILES.status, options.statusOverride);
    if (statusRead.tag === 'reject') return write0(root, outputPath, writeOutput, statusRead);
    const statusCheck = validateStatus0(statusRead.value, manifest);
    if (statusCheck.tag === 'reject') return write0(root, outputPath, writeOutput, statusCheck);

    const entrypointRead = await readJson0(root, FILES.entrypoint, options.entrypointOverride);
    if (entrypointRead.tag === 'reject') return write0(root, outputPath, writeOutput, entrypointRead);
    const entrypointCheck = validateEntrypoint0(entrypointRead.value, manifest);
    if (entrypointCheck.tag === 'reject') return write0(root, outputPath, writeOutput, entrypointCheck);

    const handoffRead = await readJson0(root, FILES.handoff, options.handoffOverride);
    if (handoffRead.tag === 'reject') return write0(root, outputPath, writeOutput, handoffRead);
    const handoffCheck = validateHandoff0(handoffRead.value, manifest);
    if (handoffCheck.tag === 'reject') return write0(root, outputPath, writeOutput, handoffCheck);

    const boundaryRead = await readJson0(root, FILES.boundary, options.boundaryOverride);
    if (boundaryRead.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryRead);
    const boundaryCheck = validateBoundaryManifest0(boundaryRead.value, manifest);
    if (boundaryCheck.tag === 'reject') return write0(root, outputPath, writeOutput, boundaryCheck);

    const docRead = await readText0(root, FILES.checklistDoc);
    if (docRead.tag === 'reject') return write0(root, outputPath, writeOutput, docRead);
    const docCheck = validateChecklistDoc0(docRead.text, manifest);
    if (docCheck.tag === 'reject') return write0(root, outputPath, writeOutput, docCheck);

    const externalRead = await readText0(root, FILES.externalReview);
    if (externalRead.tag === 'reject') return write0(root, outputPath, writeOutput, externalRead);
    const externalCheck = validateExternalReviewStatus0(externalRead.text);
    if (externalCheck.tag === 'reject') return write0(root, outputPath, writeOutput, externalCheck);

    const evidence = await digestEvidence0(root, manifest.evidenceSurfaces);
    if (evidence.tag === 'reject') return write0(root, outputPath, writeOutput, evidence);

    return write0(root, outputPath, writeOutput, {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: COORD,
      claimStatus: 'public-review-checklist-accepted-non-activating',
      publicReviewChecklistReady: true,
      checklistDocReady: true,
      rootEntrypointBound: true,
      handoffBound: true,
      boundaryBound: true,
      externalReviewStatusBound: true,
      directTheoremEmissionAllowedByChecklist: false,
      reviewAcceptanceClaimed: false,
      checklistItemCount: manifest.checklistItems.length,
      requiredCommandCount: manifest.requiredReviewerCommands.length,
      requiredVerificationSurfaceCount: manifest.requiredVerificationSurfaceIds.length,
      requiredCoordinates: { ...manifest.requiredCoordinates },
      checklistDocSha256: shaBytes0(docRead.bytes),
      externalReviewStatusSha256: shaBytes0(externalRead.bytes),
      evidenceFileCount: evidence.files.length,
      evidenceDigestSha256: shaText0(stable0(evidence.files)),
      evidenceFiles: evidence.files,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...BLOCKERS],
      outputPath: writeOutput ? outputPath : null
    });
  } catch (error) {
    return write0(root, outputPath, writeOutput, reject0('PublicReviewChecklist.UnhandledException', [], 'public review checklist checker threw unexpectedly', normErr0(error)));
  }
}

function validateManifest0(m) {
  if (!plain0(m) || m.kind !== 'PNPPublicReviewChecklist0' || m.version !== VERSION || m.coordinate !== COORD || m.status !== 'public-review-checklist-ready') return reject0('PublicReviewChecklist.ManifestShape', [FILES.manifest], 'manifest shape mismatch');
  const flags = {
    publicReviewChecklistReady: true,
    checklistDocReady: true,
    rootEntrypointBound: true,
    handoffBound: true,
    boundaryBound: true,
    externalReviewStatusBound: true,
    directTheoremEmissionAllowedByChecklist: false,
    reviewAcceptanceClaimed: false
  };
  for (const [field, expected] of Object.entries(flags)) if (m[field] !== expected) return reject0('PublicReviewChecklist.ManifestFlag', [FILES.manifest, field], 'manifest flag mismatch', { expected, actual: m[field] });
  const boundary = boundary0(m.claimBoundary, [FILES.manifest, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  if (!plain0(m.requiredCoordinates)) return reject0('PublicReviewChecklist.RequiredCoordinateShape', [FILES.manifest, 'requiredCoordinates'], 'requiredCoordinates must be object');
  for (const [field, expected] of Object.entries(m.requiredCoordinates)) if (typeof expected !== 'string' || expected.length === 0) return reject0('PublicReviewChecklist.RequiredCoordinateValue', [FILES.manifest, 'requiredCoordinates', field], 'required coordinate value must be non-empty string');
  for (const field of ['requiredVerificationSurfaceIds', 'requiredReviewerCommands', 'requiredChecklistDocFragments', 'evidenceSurfaces', 'nonClaims']) if (!Array.isArray(m[field]) || m[field].length === 0 || m[field].some((x) => typeof x !== 'string' || x.length === 0)) return reject0('PublicReviewChecklist.ArrayMissing', [FILES.manifest, field], 'manifest string array missing or invalid');
  if (!Array.isArray(m.checklistItems) || m.checklistItems.length !== 12) return reject0('PublicReviewChecklist.ItemCount', [FILES.manifest, 'checklistItems'], 'checklist item count mismatch', { expected: 12, actual: m.checklistItems?.length ?? null });
  const seen = new Set();
  for (let i = 0; i < m.checklistItems.length; i += 1) {
    const item = m.checklistItems[i];
    if (!plain0(item) || typeof item.id !== 'string' || typeof item.surface !== 'string' || typeof item.question !== 'string' || typeof item.expectedCurrentState !== 'string' || item.activationEffect !== 'none') return reject0('PublicReviewChecklist.ItemShape', [FILES.manifest, 'checklistItems', i], 'checklist item shape mismatch or activating effect', { item });
    if (seen.has(item.id)) return reject0('PublicReviewChecklist.DuplicateItemId', [FILES.manifest, 'checklistItems', i, 'id'], 'duplicate checklist item id', { id: item.id });
    seen.add(item.id);
  }
  return { tag: 'accept' };
}

function validateStatus0(status, manifest) {
  if (!plain0(status) || status.kind !== 'PNPStatus0' || status.project !== 'PNP') return reject0('PublicReviewChecklist.StatusShape', [FILES.status], 'status shape mismatch');
  const boundary = boundary0(status, [FILES.status]);
  if (boundary.tag === 'reject') return boundary;
  if (status.pnpVerifyCommand !== 'npm run pnp:verify') return reject0('PublicReviewChecklist.StatusVerifyCommand', [FILES.status, 'pnpVerifyCommand'], 'status pnp verify command mismatch', { actual: status.pnpVerifyCommand });
  for (const [field, expected] of Object.entries(manifest.requiredCoordinates)) if (status[field] !== expected) return reject0('PublicReviewChecklist.StatusCoordinateMismatch', [FILES.status, field], 'status coordinate mismatch', { expected, actual: status[field] });
  const surfaceIds = new Set((status.verificationSurfaces ?? []).map((x) => x.id));
  for (const id of manifest.requiredVerificationSurfaceIds) if (!surfaceIds.has(id)) return reject0('PublicReviewChecklist.StatusSurfaceMissing', [FILES.status, 'verificationSurfaces'], 'required verification surface missing from status', { id });
  return { tag: 'accept' };
}

function validateEntrypoint0(entrypoint, manifest) {
  const expected = manifest.requiredCoordinates.publicReviewEntrypointCoordinate;
  if (!plain0(entrypoint) || entrypoint.kind !== 'PNPPublicReviewEntrypoint0' || entrypoint.coordinate !== expected || entrypoint.publicReviewEntrypointReady !== true || entrypoint.directTheoremEmissionAllowedByEntrypoint !== false) return reject0('PublicReviewChecklist.EntrypointShape', [FILES.entrypoint], 'public review entrypoint shape mismatch or overclaim');
  return boundary0(entrypoint.claimBoundary, [FILES.entrypoint, 'claimBoundary']);
}

function validateHandoff0(handoff, manifest) {
  const expected = manifest.requiredCoordinates.publicReviewHandoffCoordinate;
  if (!plain0(handoff) || handoff.kind !== 'PNPPublicReviewHandoff0' || handoff.coordinate !== expected || handoff.publicReviewHandoffReady !== true || handoff.directTheoremEmissionAllowedByHandoff !== false) return reject0('PublicReviewChecklist.HandoffShape', [FILES.handoff], 'public review handoff shape mismatch or overclaim');
  const boundary = boundary0(handoff.claimBoundary, [FILES.handoff, 'claimBoundary']);
  if (boundary.tag === 'reject') return boundary;
  for (const command of manifest.requiredReviewerCommands.filter((cmd) => cmd !== 'node pcc-public-review-checklist0.mjs --json')) if (!handoff.requiredCommands?.includes?.(command) && !['node pcc-public-review-entrypoint0.mjs --json'].includes(command)) return reject0('PublicReviewChecklist.HandoffCommandMissing', [FILES.handoff, 'requiredCommands'], 'handoff command missing', { command });
  return { tag: 'accept' };
}

function validateBoundaryManifest0(boundary, manifest) {
  const expected = manifest.requiredCoordinates.publicReviewBoundaryCoordinate;
  if (!plain0(boundary) || boundary.kind !== 'PNPPublicReviewBoundary0' || boundary.coordinate !== expected || boundary.publicReviewBoundaryReady !== true || boundary.publicTheoremEmissionAllowedByBoundary !== false || boundary.finalTheoremReadyByBoundary !== false) return reject0('PublicReviewChecklist.BoundaryShape', [FILES.boundary], 'public review boundary shape mismatch or overclaim');
  return boundary0(boundary.claimBoundary, [FILES.boundary, 'claimBoundary']);
}

function validateChecklistDoc0(text, manifest) {
  for (const fragment of manifest.requiredChecklistDocFragments) if (!text.includes(fragment)) return reject0('PublicReviewChecklist.DocFragmentMissing', [FILES.checklistDoc, fragment], 'checklist doc required fragment missing');
  for (const command of manifest.requiredReviewerCommands) if (!text.includes(command)) return reject0('PublicReviewChecklist.DocCommandMissing', [FILES.checklistDoc, command], 'checklist doc required command missing');
  for (const item of manifest.checklistItems) {
    if (!text.includes(item.id) || !text.includes(item.surface) || !text.includes(item.expectedCurrentState)) return reject0('PublicReviewChecklist.DocItemMissing', [FILES.checklistDoc, item.id], 'checklist doc item missing');
  }
  for (const expected of Object.values(manifest.requiredCoordinates)) if (!text.includes(expected)) return reject0('PublicReviewChecklist.DocCoordinateMissing', [FILES.checklistDoc, expected], 'checklist doc required coordinate missing');
  return { tag: 'accept' };
}

function validateExternalReviewStatus0(text) {
  for (const fragment of ['No independent reviewer has confirmed', 'not proof evidence', 'did not validate or reject the claim']) if (!text.includes(fragment)) return reject0('PublicReviewChecklist.ExternalReviewFragmentMissing', [FILES.externalReview, fragment], 'external review status required fragment missing');
  return { tag: 'accept' };
}

async function readJson0(root, rel, override) {
  if (override !== undefined) return { tag: 'accept', value: override };
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes }; }
  catch (error) { return reject0('PublicReviewChecklist.ReadOrParseFailed', [rel], 'could not read or parse JSON', normErr0(error)); }
}
async function readText0(root, rel) {
  try { const bytes = await readFile(safeJoinRequired0(root, rel)); return { tag: 'accept', text: bytes.toString('utf8'), bytes }; }
  catch (error) { return reject0('PublicReviewChecklist.ReadTextFailed', [rel], 'could not read text file', normErr0(error)); }
}
async function digestEvidence0(root, paths) {
  const files = [];
  for (const rel of [...new Set(paths)]) {
    const safe = safeJoin0(root, rel);
    if (safe === null) return reject0('PublicReviewChecklist.UnsafePath', ['evidenceSurfaces', rel], 'unsafe evidence path');
    try {
      const info = await stat(safe);
      if (!info.isFile()) return reject0('PublicReviewChecklist.PathNotFile', ['evidenceSurfaces', rel], 'evidence path is not a file');
      const bytes = await readFile(safe);
      files.push({ path: rel, size: bytes.length, sha256: shaBytes0(bytes) });
    } catch (error) {
      return reject0('PublicReviewChecklist.PathMissing', ['evidenceSurfaces', rel], 'evidence path missing', normErr0(error));
    }
  }
  return { tag: 'accept', files };
}
function boundary0(b, pathArray) { if (!plain0(b)) return reject0('PublicReviewChecklist.BoundaryShape', pathArray, 'boundary must be object'); if (b.publicTheoremEmissionAllowed !== false || b.finalTheoremReady !== false || !sameArray0(b.activeFinalNodeIds, []) || !sameArray0(b.remainingBlockers, BLOCKERS)) return reject0('PublicReviewChecklist.BoundaryMismatch', pathArray, 'non-activation boundary mismatch'); return { tag: 'accept' }; }
function safeJoinRequired0(root, rel) { const p = safeJoin0(root, rel); if (p === null) throw new Error(`unsafe path: ${rel}`); return p; }
function safeJoin0(root, rel) { if (typeof rel !== 'string' || rel.length === 0 || path.isAbsolute(rel)) return null; const rr = path.resolve(root); const out = path.resolve(rr, rel); const back = path.relative(rr, out); return back.startsWith('..') || path.isAbsolute(back) ? null : out; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...BLOCKERS] }; }
async function write0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const out = path.join(root, outputPath); await mkdir(path.dirname(out), { recursive: true }); await writeFile(out, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function plain0(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }
function sameArray0(a, b) { return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((x, i) => x === b[i]); }
function stable0(v) { if (v === null || typeof v !== 'object') return JSON.stringify(v); if (Array.isArray(v)) return `[${v.map(stable0).join(',')}]`; return `{${Object.keys(v).sort().map((k) => `${JSON.stringify(k)}:${stable0(v[k])}`).join(',')}}`; }
function shaBytes0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function shaText0(text) { return createHash('sha256').update(String(text), 'utf8').digest('hex'); }
function normErr0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function parseArgs0(argv) { const o = { root: process.cwd(), outputPath: OUT, writeOutput: true, json: false }; for (let i = 0; i < argv.length; i += 1) { const a = argv[i]; if (a === '--json') o.json = true; else if (a === '--no-write') o.writeOutput = false; else if (a === '--root') o.root = argv[++i]; else if (a === '--output') o.outputPath = argv[++i]; else if (a === '--help' || a === '-h') { console.log('Usage: node pcc-public-review-checklist0.mjs [--json] [--no-write] [--root <path>] [--output <path>]'); process.exit(0); } else throw new Error(`unknown argument: ${a}`); } return o; }
async function main0() { let options; try { options = parseArgs0(process.argv.slice(2)); } catch (error) { const v = reject0('Cli.BadArgument', [], 'bad public review checklist CLI argument', normErr0(error)); console.error(JSON.stringify(v, null, 2)); process.exit(2); } const verdict = await CheckPublicReviewChecklist0(options); const rendered = JSON.stringify(verdict, null, 2); if (options.json || verdict.tag === 'accept') console.log(rendered); else console.error(rendered); process.exit(verdict.tag === 'accept' ? 0 : 1); }
if (import.meta.url === `file://${process.argv[1]}`) main0();
