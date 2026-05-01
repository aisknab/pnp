import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0 = Object.freeze([
  '# pnp',
  'Public RunAll0 entry point',
  'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP',
  'The generator is untrusted.',
  'canonical bytes rather than digest equality',
  'A reject run emits a replayable first failure and no public theorem conclusion.',
  'Release audit',
  'The release audit checks the public package surface, package exports, README claim boundary, orphaned tests, syntax of checker modules, deterministic repeated `RunAll0` execution, mutation safety of the synthetic full-stack input, the public surface freeze phase, and the materialized public-status release gate.',
  'Internal materialized public status release gate',
  'pending  -> no public P = NP conclusion',
  'rejected -> no public P = NP conclusion',
  'accepted -> emits the conditional public conclusion',
  'Release audit hard-gate default',
  'The default release audit CLI run executes the public surface freeze and the materialized public-status gate.',
  'Fast local mode keeps the public surface freeze enabled and skips only the heavier materialized public-status roundtrip gate.',
  'Public entry release surface freeze',
  'Release audit phase-order freeze',
  'Release audit README wording freeze',
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

  ledger.push({
    phase: 'config',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const loaded = await loadReadmeText0(cfg);

  ledger.push({
    phase: 'load',
    status: loaded.ok ? 'pass' : 'fail',
    digest: digestCanonical0(loaded.nf ?? loaded.witness ?? null),
  });

  if (!loaded.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.load`,
      path: loaded.path,
      witness: loaded.witness,
      ledger,
    });
  }

  const required = validateRequiredSnippets0(loaded.text);

  ledger.push({
    phase: 'requiredSnippets',
    status: required.ok ? 'pass' : 'fail',
    digest: digestCanonical0(required.nf ?? required.witness ?? null),
  });

  if (!required.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.requiredSnippet`,
      path: required.path,
      witness: required.witness,
      ledger,
    });
  }

  const forbidden = validateForbiddenSnippets0(loaded.text);

  ledger.push({
    phase: 'forbiddenSnippets',
    status: forbidden.ok ? 'pass' : 'fail',
    digest: digestCanonical0(forbidden.nf ?? forbidden.witness ?? null),
  });

  if (!forbidden.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.forbiddenSnippet`,
      path: forbidden.path,
      witness: forbidden.witness,
      ledger,
    });
  }

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
    staleLayoutWordingRejected: true,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ReadmeReleaseBoundaryConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ReadmeReleaseBoundaryConfig0') {
    return validationReject0(['kind'], 'ReadmeReleaseBoundaryConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ReadmeReleaseBoundaryConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.rootDir !== 'string' || config.rootDir.length === 0) {
    return validationReject0(['rootDir'], 'ReadmeReleaseBoundaryConfig0 rootDir must be a non-empty string', {
      actual: config.rootDir,
    });
  }

  if (
    config.readmePath !== null &&
    (typeof config.readmePath !== 'string' || config.readmePath.length === 0)
  ) {
    return validationReject0(['readmePath'], 'ReadmeReleaseBoundaryConfig0 readmePath must be null or a non-empty string', {
      actual: config.readmePath,
    });
  }

  if (
    config.readmeText !== null &&
    typeof config.readmeText !== 'string'
  ) {
    return validationReject0(['readmeText'], 'ReadmeReleaseBoundaryConfig0 readmeText must be null or a string', {
      actual: typeof config.readmeText,
    });
  }

  return validationAccept0({
    kind: 'ReadmeReleaseBoundaryConfig0NF',
  });
}

async function loadReadmeText0(config) {
  if (config.readmeText !== null) {
    return {
      ok: true,
      text: config.readmeText,
      readmePath: config.readmePath ?? '<inline>',
      nf: {
        kind: 'ReadmeReleaseBoundaryInlineText0NF',
        byteLength: Buffer.byteLength(config.readmeText, 'utf8'),
      },
    };
  }

  const readmePath = config.readmePath ?? path.join(config.rootDir, 'README.md');

  try {
    const text = await fs.readFile(readmePath, 'utf8');

    return {
      ok: true,
      text,
      readmePath,
      nf: {
        kind: 'ReadmeReleaseBoundaryFile0NF',
        readmePath,
        byteLength: Buffer.byteLength(text, 'utf8'),
      },
    };
  } catch (error) {
    return validationReject0(['README.md'], 'README.md must be readable UTF-8 text', {
      readmePath,
      error: error.message,
    });
  }
}

function validateRequiredSnippets0(text) {
  for (let index = 0; index < README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0.length; index += 1) {
    const snippet = README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0[index];

    if (!text.includes(snippet)) {
      return validationReject0(['README.md', 'requiredSnippet', index], 'README release boundary wording is missing a required snippet', {
        snippet,
      });
    }
  }

  return validationAccept0({
    kind: 'ReadmeRequiredSnippets0NF',
    requiredSnippetCount: README_RELEASE_BOUNDARY_REQUIRED_SNIPPETS0.length,
  });
}

function validateForbiddenSnippets0(text) {
  for (let index = 0; index < README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0.length; index += 1) {
    const snippet = README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0[index];

    if (text.includes(snippet)) {
      return validationReject0(['README.md', 'forbiddenSnippet', index], 'README release boundary wording contains a forbidden stale or overclaiming snippet', {
        snippet,
      });
    }
  }

  return validationAccept0({
    kind: 'ReadmeForbiddenSnippets0NF',
    forbiddenSnippetCount: README_RELEASE_BOUNDARY_FORBIDDEN_SNIPPETS0.length,
  });
}

function makeAcceptRecord({
  checker,
  nf,
  ledger,
}) {
  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    Ledger: ledger,
    nf,
    digest,
    ledger,
  };
}

function makeRejectRecord({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
  const rejectNF = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };

  const digest = digestCanonical0(rejectNF);

  return {
    tag: 'reject',
    kind: 'reject',
    checker,
    version: CHECKER_VERSION,
    Coord: coord,
    Path: path,
    Witness: witness,
    Digest: digest,
    Ledger: ledger,
    coord,
    path,
    witness,
    digest,
    ledger,
  };
}

function validationAccept0(nf) {
  return {
    ok: true,
    nf,
  };
}

function validationReject0(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}