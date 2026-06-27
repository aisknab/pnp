#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

const CHECKER = 'AuditNegativeCheckerMutations0';
const VERSION = 0;
const MANIFEST_PATH = 'checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json';
const DEFAULT_OUTPUT_PATH = 'artifacts/checker-mutations/latest-verdict.json';
const EXPECTED_COORDINATE = 'PNP-NEGATIVE-CHECKER-MUTATIONS-2026-06-27-01';
const EXPECTED_BLOCKERS = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];
const EXPECTED_TARGET_IDS = ['CheckMinimalKernel0', 'CheckTrustBase0', 'CheckTrustBaseShrinkPlan0', 'CheckPublicEntryReleaseSurface0'];

export async function AuditNegativeCheckerMutations0(options = {}) {
  const root = path.resolve(options.root ?? process.cwd());
  const manifestPath = options.manifestPath ?? MANIFEST_PATH;
  const outputPath = options.outputPath ?? DEFAULT_OUTPUT_PATH;
  const writeOutput = options.writeOutput ?? true;

  try {
    const manifestRead = await readJson0(root, manifestPath, options.manifestOverride);
    if (manifestRead.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestRead);

    const manifestCheck = validateManifest0(manifestRead.value);
    if (manifestCheck.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, manifestCheck);

    const run = await runMutationSuite0(root, manifestRead.value);
    if (run.tag === 'reject') return writeAndReturn0(root, outputPath, writeOutput, run);

    const verdict = {
      tag: 'accept',
      kind: 'accept',
      checker: CHECKER,
      version: VERSION,
      coordinate: EXPECTED_COORDINATE,
      claimStatus: 'negative-checker-mutation-seed-accepted',
      manifestPath,
      manifestSha256: sha256Hex0(manifestRead.bytes),
      negativeMutationSeedReady: true,
      fullNegativeMutationCoverageProved: false,
      targetCount: manifestRead.value.targets.length,
      validCaseCount: run.validCaseCount,
      mutationCaseCount: run.mutationCaseCount,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS],
      outputPath: writeOutput ? outputPath : null,
    };

    return writeAndReturn0(root, outputPath, writeOutput, verdict);
  } catch (error) {
    return writeAndReturn0(root, outputPath, writeOutput, reject0('NegativeMutations.UnhandledException', [], 'negative mutation audit threw unexpectedly', normalizeError0(error)));
  }
}

async function readJson0(root, relativePath, override) {
  if (override !== undefined) {
    const bytes = Buffer.from(JSON.stringify(override, null, 2) + '\n', 'utf8');
    return { tag: 'accept', value: override, bytes };
  }
  try {
    const bytes = await readFile(path.join(root, relativePath));
    return { tag: 'accept', value: JSON.parse(bytes.toString('utf8')), bytes };
  } catch (error) {
    return reject0('NegativeMutations.JsonReadOrParseFailed', [relativePath], 'could not read or parse negative mutation JSON', normalizeError0(error));
  }
}

function validateManifest0(manifest) {
  if (!plain0(manifest)) return reject0('NegativeMutations.ManifestShape', [], 'manifest must be an object');
  if (manifest.kind !== 'PNPNegativeCheckerMutations0') return reject0('NegativeMutations.ManifestKind', ['kind'], 'manifest kind mismatch');
  if (manifest.version !== VERSION) return reject0('NegativeMutations.ManifestVersion', ['version'], 'manifest version mismatch');
  if (manifest.coordinate !== EXPECTED_COORDINATE) return reject0('NegativeMutations.ManifestCoordinate', ['coordinate'], 'manifest coordinate mismatch');
  if (manifest.status !== 'negative-checker-mutation-seed-ready') return reject0('NegativeMutations.ManifestStatus', ['status'], 'manifest status mismatch');
  if (manifest.negativeMutationSeedReady !== true) return reject0('NegativeMutations.SeedFlag', ['negativeMutationSeedReady'], 'negativeMutationSeedReady must be true');
  if (manifest.fullNegativeMutationCoverageProved !== false) return reject0('NegativeMutations.FullCoverageFlag', ['fullNegativeMutationCoverageProved'], 'initial mutation suite cannot claim full coverage');
  const boundary = validateBoundary0(manifest.claimBoundary);
  if (boundary.tag === 'reject') return boundary;

  if (!Array.isArray(manifest.mutationFamilies) || manifest.mutationFamilies.length === 0) return reject0('NegativeMutations.Families', ['mutationFamilies'], 'mutationFamilies must be non-empty');
  if (!Array.isArray(manifest.targets)) return reject0('NegativeMutations.TargetsShape', ['targets'], 'targets must be an array');
  const ids = manifest.targets.map((entry) => entry?.id);
  if (!sameArray0(ids, EXPECTED_TARGET_IDS)) return reject0('NegativeMutations.TargetIds', ['targets'], 'target ids must stay exact and ordered', { expected: EXPECTED_TARGET_IDS, actual: ids });

  for (let index = 0; index < manifest.targets.length; index += 1) {
    const target = manifest.targets[index];
    const targetPath = ['targets', index];
    if (!plain0(target)) return reject0('NegativeMutations.TargetShape', targetPath, 'target must be an object');
    for (const field of ['id', 'file', 'exportName', 'validCase']) {
      if (!nonempty0(target[field])) return reject0('NegativeMutations.TargetField', [...targetPath, field], 'target field must be a non-empty string');
    }
    if (target.id !== target.exportName) return reject0('NegativeMutations.TargetIdMismatch', targetPath, 'target id must equal exportName');
    if (!target.file.endsWith('.mjs') || path.isAbsolute(target.file) || target.file.startsWith('.')) return reject0('NegativeMutations.TargetFile', [...targetPath, 'file'], 'target file must be repository-relative .mjs');
    if (!Array.isArray(target.mutations) || target.mutations.length === 0) return reject0('NegativeMutations.TargetMutations', [...targetPath, 'mutations'], 'target must have mutations');
    const mutationIds = new Set();
    for (let mutationIndex = 0; mutationIndex < target.mutations.length; mutationIndex += 1) {
      const mutation = target.mutations[mutationIndex];
      const mutationPath = [...targetPath, 'mutations', mutationIndex];
      if (!plain0(mutation)) return reject0('NegativeMutations.MutationShape', mutationPath, 'mutation must be an object');
      for (const field of ['id', 'family', 'expectedTag']) {
        if (!nonempty0(mutation[field])) return reject0('NegativeMutations.MutationField', [...mutationPath, field], 'mutation field must be non-empty');
      }
      if (mutation.expectedTag !== 'reject') return reject0('NegativeMutations.MutationExpectedTag', [...mutationPath, 'expectedTag'], 'negative mutations must expect reject');
      if (!manifest.mutationFamilies.includes(mutation.family)) return reject0('NegativeMutations.UnknownFamily', [...mutationPath, 'family'], 'mutation references an unknown family');
      if (mutationIds.has(mutation.id)) return reject0('NegativeMutations.DuplicateMutation', [...mutationPath, 'id'], 'mutation ids must be unique per target');
      mutationIds.add(mutation.id);
    }
  }

  const expectedAudit = {
    checker: CHECKER,
    script: 'scripts/audit-negative-checker-mutations.mjs',
    command: 'npm run checker:mutations',
    expectedAcceptTag: 'accept',
  };
  if (!plain0(manifest.audit)) return reject0('NegativeMutations.AuditShape', ['audit'], 'audit must be an object');
  for (const [key, expected] of Object.entries(expectedAudit)) {
    if (manifest.audit[key] !== expected) return reject0('NegativeMutations.AuditField', ['audit', key], 'manifest audit field mismatch', { expected, actual: manifest.audit[key] });
  }
  return { tag: 'accept' };
}

function validateBoundary0(boundary) {
  if (!plain0(boundary)) return reject0('NegativeMutations.BoundaryShape', ['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return reject0('NegativeMutations.PublicEmission', ['claimBoundary', 'publicTheoremEmissionAllowed'], 'public theorem emission must remain disabled');
  if (boundary.finalTheoremReady !== false) return reject0('NegativeMutations.FinalReady', ['claimBoundary', 'finalTheoremReady'], 'final theorem readiness must remain disabled');
  if (!sameArray0(boundary.activeFinalNodeIds, [])) return reject0('NegativeMutations.ActiveFinalNodes', ['claimBoundary', 'activeFinalNodeIds'], 'active final node ids must remain empty');
  if (!sameArray0(boundary.remainingBlockers, EXPECTED_BLOCKERS)) return reject0('NegativeMutations.RemainingBlockers', ['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact');
  return { tag: 'accept' };
}

async function runMutationSuite0(root, manifest) {
  let validCaseCount = 0;
  let mutationCaseCount = 0;
  for (const target of manifest.targets) {
    const moduleLoad = await importTarget0(root, target.file);
    if (moduleLoad.tag === 'reject') return moduleLoad;
    const fn = moduleLoad.module[target.exportName];
    if (typeof fn !== 'function') return reject0('NegativeMutations.TargetNotFunction', [target.file, target.exportName], 'target export is not a function');

    const valid = await buildCaseArgs0(root, moduleLoad.module, target, target.validCase);
    if (valid.tag === 'reject') return valid;
    const validResult = await callCase0(fn, target, target.validCase, valid.args, 'accept');
    if (validResult.tag === 'reject') return validResult;
    validCaseCount += 1;

    for (const mutation of target.mutations) {
      const built = await buildCaseArgs0(root, moduleLoad.module, target, mutation.id);
      if (built.tag === 'reject') return built;
      const result = await callCase0(fn, target, mutation.id, built.args, mutation.expectedTag);
      if (result.tag === 'reject') return result;
      mutationCaseCount += 1;
    }
  }
  return { tag: 'accept', validCaseCount, mutationCaseCount };
}

async function importTarget0(root, relativePath) {
  try {
    return { tag: 'accept', module: await import(pathToFileURL(path.join(root, relativePath)).href) };
  } catch (error) {
    return reject0('NegativeMutations.ModuleImportFailed', [relativePath], 'could not import mutation target', normalizeError0(error));
  }
}

async function buildCaseArgs0(root, mod, target, caseId) {
  try {
    switch (caseId) {
      case 'minimal.valid-default': return { tag: 'accept', args: [] };
      case 'minimal.kind-mismatch': return { tag: 'accept', args: [{ ...mod.makeMinimalKernelInput0(), kind: 'WrongMinimalKernelInput0' }] };
      case 'minimal.boundary-activation': {
        const kernel = clone0(mod.PNP_MINIMAL_KERNEL0);
        kernel.claimBoundary.publicTheoremEmissionAllowed = true;
        return { tag: 'accept', args: [mod.makeMinimalKernelInput0({ Kernel: kernel })] };
      }
      case 'minimal.missing-primitive-rule': {
        const kernel = clone0(mod.PNP_MINIMAL_KERNEL0);
        kernel.proofKernel.primitiveRules = kernel.proofKernel.primitiveRules.slice(1);
        return { tag: 'accept', args: [mod.makeMinimalKernelInput0({ Kernel: kernel })] };
      }
      case 'minimal.caller-readiness': return { tag: 'accept', args: [{ ...mod.makeMinimalKernelInput0(), publicTheoremEmissionAllowed: true }] };

      case 'trustbase.valid-default': return { tag: 'accept', args: [{ writeOutput: false }] };
      case 'trustbase.kind-mismatch': {
        const trustBaseOverride = { kind: 'WrongTrustBase0' };
        return { tag: 'accept', args: [{ trustBaseOverride, sha256SumsOverride: checksumLine0(trustBaseOverride), writeOutput: false }] };
      }
      case 'trustbase.boundary-activation': {
        const trustBaseOverride = await readRepoJson0(root, 'trust-base/TRUST_BASE.json');
        trustBaseOverride.claimBoundary.publicTheoremEmissionAllowed = true;
        return { tag: 'accept', args: [{ trustBaseOverride, sha256SumsOverride: checksumLine0(trustBaseOverride), writeOutput: false }] };
      }
      case 'trustbase.missing-assumption': {
        const trustBaseOverride = await readRepoJson0(root, 'trust-base/TRUST_BASE.json');
        trustBaseOverride.assumptions = trustBaseOverride.assumptions.slice(1);
        return { tag: 'accept', args: [{ trustBaseOverride, sha256SumsOverride: checksumLine0(trustBaseOverride), writeOutput: false }] };
      }
      case 'trustbase.checksum-mismatch': {
        const trustBaseOverride = await readRepoJson0(root, 'trust-base/TRUST_BASE.json');
        return { tag: 'accept', args: [{ trustBaseOverride, sha256SumsOverride: `${'0'.repeat(64)}  TRUST_BASE.json\n`, writeOutput: false }] };
      }
      case 'trustbase.empty-claim': {
        const trustBaseOverride = await readRepoJson0(root, 'trust-base/TRUST_BASE.json');
        trustBaseOverride.trustBaseEmpty = true;
        return { tag: 'accept', args: [{ trustBaseOverride, sha256SumsOverride: checksumLine0(trustBaseOverride), writeOutput: false }] };
      }

      case 'shrink.valid-default': return { tag: 'accept', args: [{ writeOutput: false }] };
      case 'shrink.kind-mismatch': return { tag: 'accept', args: [{ planOverride: { kind: 'WrongShrinkPlan0' }, trustBaseOverride: { kind: 'WrongTrustBase0' }, writeOutput: false }] };
      case 'shrink.boundary-activation': {
        const planOverride = await readRepoJson0(root, 'trust-base/SHRINK_PLAN.json');
        const trustBaseOverride = await readRepoJson0(root, 'trust-base/TRUST_BASE.json');
        planOverride.claimBoundary.publicTheoremEmissionAllowed = true;
        return { tag: 'accept', args: [{ planOverride, trustBaseOverride, writeOutput: false }] };
      }
      case 'shrink.unknown-dependency': {
        const planOverride = await readRepoJson0(root, 'trust-base/SHRINK_PLAN.json');
        const trustBaseOverride = await readRepoJson0(root, 'trust-base/TRUST_BASE.json');
        planOverride.tasks[1].blockedBy.push('TB-999');
        return { tag: 'accept', args: [{ planOverride, trustBaseOverride, writeOutput: false }] };
      }
      case 'shrink.premature-complete': {
        const planOverride = await readRepoJson0(root, 'trust-base/SHRINK_PLAN.json');
        const trustBaseOverride = await readRepoJson0(root, 'trust-base/TRUST_BASE.json');
        planOverride.tasks[0].status = 'complete';
        return { tag: 'accept', args: [{ planOverride, trustBaseOverride, writeOutput: false }] };
      }

      case 'publicsurface.valid-default': return { tag: 'accept', args: [] };
      case 'publicsurface.extra-script': {
        const pkg = await readRepoJson0(root, 'package.json');
        pkg.scripts['unexpected:mutation'] = 'node unexpected.mjs';
        return { tag: 'accept', args: [{ rootDir: root, publicEntryOverride: null, packageJsonOverride: pkg }] };
      }
      case 'publicsurface.main-mismatch': {
        const pkg = await readRepoJson0(root, 'package.json');
        pkg.main = './wrong.mjs';
        return { tag: 'accept', args: [{ rootDir: root, publicEntryOverride: null, packageJsonOverride: pkg }] };
      }
      case 'publicsurface.exports-missing': {
        const pkg = await readRepoJson0(root, 'package.json');
        delete pkg.exports['./runall0'];
        return { tag: 'accept', args: [{ rootDir: root, publicEntryOverride: null, packageJsonOverride: pkg }] };
      }

      default: return reject0('NegativeMutations.UnknownCase', [target.id, caseId], 'unknown negative mutation case');
    }
  } catch (error) {
    return reject0('NegativeMutations.BuildCaseFailed', [target.id, caseId], 'could not build mutation case', normalizeError0(error));
  }
}

async function callCase0(fn, target, caseId, args, expectedTag) {
  let record;
  try {
    record = await fn(...args);
  } catch (error) {
    return reject0('NegativeMutations.TargetThrew', [target.id, caseId], 'checker threw instead of returning accept/reject', normalizeError0(error));
  }
  if (!plain0(record) || !['accept', 'reject'].includes(record.tag)) return reject0('NegativeMutations.NonTotalReturn', [target.id, caseId], 'checker returned a non accept/reject record', { actual: String(record) });
  if (record.tag !== expectedTag) return reject0('NegativeMutations.UnexpectedTag', [target.id, caseId], 'mutation case returned unexpected tag', { expectedTag, actualTag: record.tag, coord: record.coord ?? record.Coord ?? null });
  return { tag: 'accept' };
}

async function readRepoJson0(root, relativePath) {
  return JSON.parse(await readFile(path.join(root, relativePath), 'utf8'));
}

function clone0(value) { return JSON.parse(JSON.stringify(value)); }
function checksumLine0(value) { return `${sha256Hex0(Buffer.from(JSON.stringify(value, null, 2) + '\n', 'utf8'))}  TRUST_BASE.json\n`; }
function reject0(coord, pathArray, reason, witness = {}) { return { tag: 'reject', kind: 'reject', checker: CHECKER, version: VERSION, coord, path: pathArray, witness: { reason, ...witness }, publicTheoremEmissionAllowed: false, finalTheoremReady: false, activeFinalNodeIds: [], remainingBlockers: [...EXPECTED_BLOCKERS] }; }
async function writeAndReturn0(root, outputPath, writeOutput, verdict) { if (writeOutput) { const absoluteOutputPath = path.join(root, outputPath); await mkdir(path.dirname(absoluteOutputPath), { recursive: true }); await writeFile(absoluteOutputPath, `${JSON.stringify(verdict, null, 2)}\n`, 'utf8'); } return { ...verdict, outputPath: writeOutput ? outputPath : null }; }
function sha256Hex0(bytes) { return createHash('sha256').update(bytes).digest('hex'); }
function normalizeError0(error) { return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null }; }
function sameArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function plain0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function nonempty0(value) { return typeof value === 'string' && value.length > 0; }

function parseArgs0(argv) {
  const options = { root: process.cwd(), manifestPath: MANIFEST_PATH, outputPath: DEFAULT_OUTPUT_PATH, writeOutput: true, json: false };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--json') options.json = true;
    else if (arg === '--no-write') options.writeOutput = false;
    else if (arg === '--root') options.root = requireValue0(argv, ++index, '--root');
    else if (arg === '--manifest') options.manifestPath = requireValue0(argv, ++index, '--manifest');
    else if (arg === '--output') options.outputPath = requireValue0(argv, ++index, '--output');
    else if (arg === '--help' || arg === '-h') { printHelp0(); process.exit(0); }
    else throw new Error(`unknown argument: ${arg}`);
  }
  return options;
}

function requireValue0(argv, index, flag) { if (index >= argv.length) throw new Error(`${flag} requires a value`); return argv[index]; }
function printHelp0() { console.log(`Usage: node scripts/audit-negative-checker-mutations.mjs [options]\n\nOptions:\n  --json              Emit verdict JSON.\n  --no-write          Do not write artifacts/checker-mutations/latest-verdict.json.\n  --root <path>       Repository root. Defaults to cwd.\n  --manifest <path>   Mutation manifest path relative to root.\n  --output <path>     Verdict output path relative to root.\n`); }

async function main0() {
  let options;
  try {
    options = parseArgs0(process.argv.slice(2));
  } catch (error) {
    const verdict = reject0('Cli.BadArgument', [], 'bad negative mutation CLI argument', normalizeError0(error));
    console.error(JSON.stringify(verdict, null, 2));
    process.exit(2);
  }
  const verdict = await AuditNegativeCheckerMutations0(options);
  const rendered = JSON.stringify(verdict, null, 2);
  if (options.json || verdict.tag === 'accept') console.log(rendered);
  else console.error(rendered);
  process.exit(verdict.tag === 'accept' ? 0 : 1);
}

if (import.meta.url === `file://${process.argv[1]}`) main0();
