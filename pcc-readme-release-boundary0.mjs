import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { digestCanonical0 } from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0 = Object.freeze([
  '# pnp',
  'target theorem is not currently established',
  'public theorem emission is disabled',
  'status/FORMAL_RECONSTRUCTION_STATUS.json',
  'FORMAL_RECONSTRUCTION.md',
  'formalReleaseGatePassed = false',
  'JSON booleans, JavaScript checker acceptance',
  'Human review is not a mathematical premise',
  'Proof-development scripts',
  'proof:*',
  'node pcc-<checker-name>0.mjs --json',
  'npm run proof:formal-reconstruction-status',
  'Public RunAll0 entry point',
  'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP',
  'The generator is untrusted.',
  'canonical bytes rather than digest equality',
  'A reject run emits a replayable first failure and no public theorem conclusion.',
  'Release audit',
  'The release audit checks the public package surface',
  'Internal materialized package path',
]);

export const README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0 = Object.freeze([
  'stale duplicate ES modules under `src`',
  'src folder',
  '`src` folder',
  'source tree under `src`',
  'P = NP is established',
  'P = NP has been proved',
  'unconditional P = NP',
  'the proof of P = NP is complete',
  'publicTheoremEmissionAllowed = true',
  'public-theorem-emission-activated-under-checker-trust-model',
  'remainingBlockers = []',
]);

export function makeReadmeReleaseBoundaryConfig0(overrides = {}) {
  return {
    kind: 'ReadmeReleaseBoundaryConfig0',
    version: CHECKER_VERSION,
    rootDir: REPO_ROOT,
    readmePath: null,
    readmeText: null,
    ...overrides,
  };
}

export async function CheckReadmeReleaseBoundary0(config = makeReadmeReleaseBoundaryConfig0()) {
  const checker = 'CheckReadmeReleaseBoundary0';
  const ledger = [];
  const cfg = makeReadmeReleaseBoundaryConfig0(config);

  const shape = validateConfig0(cfg);
  ledger.push(ledgerEntry0('config', shape));
  if (!shape.ok) return makeRejectRecord0(checker, `${checker}.config`, shape.path, shape.witness, ledger);

  const loaded = await loadReadmeText0(cfg);
  ledger.push(ledgerEntry0('load', loaded));
  if (!loaded.ok) return makeRejectRecord0(checker, `${checker}.load`, loaded.path, loaded.witness, ledger);

  const required = validateRequiredSnippets0(loaded.text);
  ledger.push(ledgerEntry0('requiredSnippets', required));
  if (!required.ok) return makeRejectRecord0(checker, `${checker}.requiredSnippet`, required.path, required.witness, ledger);

  const forbidden = validateForbiddenSnippets0(loaded.text);
  ledger.push(ledgerEntry0('forbiddenSnippets', forbidden));
  if (!forbidden.ok) return makeRejectRecord0(checker, `${checker}.forbiddenSnippet`, forbidden.path, forbidden.witness, ledger);

  const nf = {
    kind: 'ReadmeReleaseBoundary0NF',
    checker,
    version: CHECKER_VERSION,
    readmePath: loaded.readmePath,
    byteLength: Buffer.byteLength(loaded.text, 'utf8'),
    requiredSnippetCount: README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0.length,
    forbiddenSnippetCount: README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0.length,
    readmeTextDigest: digestCanonical0(loaded.text),
    conditionalClaimBoundaryFrozen: true,
    formalReconstructionBoundaryFrozen: true,
    publicTheoremEmissionDisabled: true,
    legacyActivationSuperseded: true,
    proofDevelopmentScriptsDocumented: true,
    staleLayoutWordingRejected: true,
    overclaimingWordingRejected: true,
  };

  return makeAcceptRecord0(checker, nf, ledger);
}

function validateConfig0(config) {
  if (!isPlainObject0(config)) return validationReject0([], 'ReadmeReleaseBoundaryConfig0 must be an object', { actual: typeof config });
  if (config.kind !== undefined && config.kind !== 'ReadmeReleaseBoundaryConfig0') return validationReject0(['kind'], 'ReadmeReleaseBoundaryConfig0 kind mismatch', { actual: config.kind });
  if (config.version !== undefined && config.version !== CHECKER_VERSION) return validationReject0(['version'], `ReadmeReleaseBoundaryConfig0 version must be ${CHECKER_VERSION} when present`, { actual: config.version });
  if (typeof config.rootDir !== 'string' || config.rootDir.length === 0) return validationReject0(['rootDir'], 'ReadmeReleaseBoundaryConfig0 rootDir must be a non-empty string', { actual: config.rootDir });
  if (config.readmePath !== null && (typeof config.readmePath !== 'string' || config.readmePath.length === 0)) return validationReject0(['readmePath'], 'ReadmeReleaseBoundaryConfig0 readmePath must be null or a non-empty string', { actual: config.readmePath });
  if (config.readmeText !== null && typeof config.readmeText !== 'string') return validationReject0(['readmeText'], 'ReadmeReleaseBoundaryConfig0 readmeText must be null or a string', { actual: typeof config.readmeText });
  return validationAccept0({ kind: 'ReadmeReleaseBoundaryConfig0NF' });
}

async function loadReadmeText0(config) {
  if (config.readmeText !== null) {
    return {
      ok: true,
      text: config.readmeText,
      readmePath: config.readmePath ?? '<inline>',
      nf: { kind: 'ReadmeReleaseBoundaryInlineText0NF', byteLength: Buffer.byteLength(config.readmeText, 'utf8') },
    };
  }
  const readmePath = config.readmePath ?? path.join(config.rootDir, 'README.md');
  try {
    const text = await fs.readFile(readmePath, 'utf8');
    return { ok: true, text, readmePath, nf: { kind: 'ReadmeReleaseBoundaryFile0NF', readmePath, byteLength: Buffer.byteLength(text, 'utf8') } };
  } catch (error) {
    return validationReject0(['README.md'], 'README.md must be readable UTF-8 text', { readmePath, error: error.message });
  }
}

function validateRequiredSnippets0(text) {
  for (const snippet of README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0) {
    if (!text.includes(snippet)) {
      return validationReject0(['README.md'], 'README release boundary wording is missing a required snippet', { snippet });
    }
  }
  return validationAccept0({ kind: 'ReadmeRequiredSnippets0NF', count: README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0.length });
}

function validateForbiddenSnippets0(text) {
  for (const snippet of README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0) {
    if (text.includes(snippet)) {
      return validationReject0(['README.md'], 'README release boundary wording contains a forbidden stale or overclaiming snippet', { snippet });
    }
  }
  return validationAccept0({ kind: 'ReadmeForbiddenSnippets0NF', count: README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0.length });
}

function ledgerEntry0(phase, result) {
  return { phase, status: result.ok ? 'pass' : 'fail', digest: digestCanonical0(result.nf ?? result.witness ?? null) };
}

function validationAccept0(nf) { return { ok: true, nf }; }
function validationReject0(pathArray, reason, detail) { return { ok: false, path: pathArray, witness: { reason, detail } }; }

function makeAcceptRecord0(checker, nf, ledger) {
  const digest = digestCanonical0(nf);
  return { tag: 'accept', kind: 'accept', checker, version: CHECKER_VERSION, NF: nf, Digest: digest, Ledger: ledger, nf, digest, ledger };
}

function makeRejectRecord0(checker, coord, pathArray, witness, ledger) {
  const rejectNF = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path: pathArray, witness, ledger };
  const digest = digestCanonical0(rejectNF);
  return { tag: 'reject', kind: 'reject', checker, version: CHECKER_VERSION, Coord: coord, Path: pathArray, Witness: witness, Digest: digest, Ledger: ledger, coord, path: pathArray, witness, digest, ledger };
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object') return false;
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}
