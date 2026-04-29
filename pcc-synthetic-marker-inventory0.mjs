import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterialized0,
  makeMaterializedGateConfig0,
} from './pcc-materialized0.mjs';

import {
  RunAll0,
  makeSyntheticRunAllInput0,
} from './pcc-runall0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const SYNTHETIC_MARKER_TERMS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export const SYNTHETIC_NOTE_KEYS0 = Object.freeze([
  'note',
  'notes',
  'placeholder',
  'stub',
  'mock',
  'todo',
]);

export const SYNTHETIC_MARKER_ALLOWED_CLASSES0 = Object.freeze([
  'engineering-fixture-source',
  'engineering-fixture-test',
  'materialized-mode-blocker',
]);

export function makeSyntheticMarkerInventoryConfig0(overrides = {}) {
  return {
    kind: 'SyntheticMarkerInventoryConfig0',
    version: CHECKER_VERSION,
    rootDir: REPO_ROOT,
    scanSourceFiles: true,
    scanTests: true,
    runMaterializedGateProbe: true,
    syntheticInputFactory: null,
    materializedRunner: null,
    ...overrides,
  };
}

export async function CheckSyntheticMarkerInventory0(config = makeSyntheticMarkerInventoryConfig0()) {
  const checker = 'CheckSyntheticMarkerInventory0';
  const ledger = [];
  const cfg = makeSyntheticMarkerInventoryConfig0(config);

  const phases = [
    ['config', `${checker}.config`, () => validateConfig0(cfg)],
    ['sourceMarkers', `${checker}.sourceMarkers`, () => collectSourceMarkerInventory0(cfg)],
    ['valueMarkers', `${checker}.valueMarkers`, () => collectSyntheticInputMarkerInventory0(cfg)],
    ['materializedGate', `${checker}.materializedGate`, () => validateMaterializedGateRejectsSynthetic0(cfg)],
  ];

  const phaseNFs = [];

  for (const [phase, coord, run] of phases) {
    const result = await run();

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    phaseNFs.push({
      phase,
      nf: result.nf,
    });
  }

  const source = phaseNFs.find((entry) => entry.phase === 'sourceMarkers')?.nf;
  const value = phaseNFs.find((entry) => entry.phase === 'valueMarkers')?.nf;
  const gate = phaseNFs.find((entry) => entry.phase === 'materializedGate')?.nf;

  const nf = {
    kind: 'SyntheticMarkerInventory0NF',
    checker,
    version: CHECKER_VERSION,
    sourceHitCount: source?.hitCount ?? 0,
    valueHitCount: value?.hitCount ?? 0,
    materializedBlockerCount: value?.materializedBlockerCount ?? 0,
    sourceClassCounts: source?.classCounts ?? {},
    valueClassCounts: value?.classCounts ?? {},
    materializedGateRejected: gate?.materializedGateRejected ?? false,
    materializedGateCoord: gate?.materializedGateCoord ?? null,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export function findSyntheticMarkersInValue0(value, {
  rootPath = [],
  classHint = 'materialized-mode-blocker',
} = {}) {
  const hits = [];
  scanValueForMarkers0(value, rootPath, hits, classHint);
  return hits;
}

export function classifySyntheticMarkerHit0(hit) {
  if (hit.sourceKind === 'test') {
    return 'engineering-fixture-test';
  }

  if (hit.sourceKind === 'value') {
    return 'materialized-mode-blocker';
  }

  return 'engineering-fixture-source';
}

async function collectSourceMarkerInventory0(config) {
  if (config.scanSourceFiles !== true && config.scanTests !== true) {
    return validationAccept0({
      kind: 'SyntheticSourceMarkerInventory0NF',
      scannedFileCount: 0,
      hitCount: 0,
      classCounts: {},
      hits: [],
    });
  }

  const files = await markerScanFiles0(config.rootDir, {
    scanSourceFiles: config.scanSourceFiles,
    scanTests: config.scanTests,
  });

  const hits = [];

  for (const relativeFile of files) {
    const absoluteFile = path.join(config.rootDir, relativeFile);
    const text = await fs.readFile(absoluteFile, 'utf8');
    const fileHits = findSyntheticMarkersInText0(text, relativeFile);

    hits.push(...fileHits);
  }

  const classified = hits.map((hit) => ({
    ...hit,
    class: classifySyntheticMarkerHit0(hit),
  }));

  return validationAccept0({
    kind: 'SyntheticSourceMarkerInventory0NF',
    scannedFileCount: files.length,
    hitCount: classified.length,
    classCounts: classCounts0(classified),
    hits: classified,
  });
}

async function collectSyntheticInputMarkerInventory0(config) {
  const input = typeof config.syntheticInputFactory === 'function'
    ? config.syntheticInputFactory()
    : makeSyntheticRunAllInput0();

  const hits = findSyntheticMarkersInValue0(input, {
    rootPath: ['RunAllInput0'],
    classHint: 'materialized-mode-blocker',
  }).map((hit) => ({
    ...hit,
    class: classifySyntheticMarkerHit0(hit),
  }));

  if (hits.length === 0) {
    return validationReject0(['RunAllInput0'], 'synthetic marker inventory found no markers in the synthetic RunAll input', null);
  }

  const materializedBlockerCount = hits.filter((hit) => hit.class === 'materialized-mode-blocker').length;

  if (materializedBlockerCount === 0) {
    return validationReject0(['RunAllInput0'], 'synthetic RunAll input markers were not classified as materialized-mode blockers', {
      hits,
    });
  }

  return validationAccept0({
    kind: 'SyntheticValueMarkerInventory0NF',
    hitCount: hits.length,
    materializedBlockerCount,
    classCounts: classCounts0(hits),
    inputDigest: digestCanonical0(input),
    hits,
  });
}

async function validateMaterializedGateRejectsSynthetic0(config) {
  if (config.runMaterializedGateProbe !== true) {
    return validationAccept0({
      kind: 'SyntheticMaterializedGateSkipped0NF',
      materializedGateRejected: false,
    });
  }

  const input = typeof config.syntheticInputFactory === 'function'
    ? config.syntheticInputFactory()
    : makeSyntheticRunAllInput0({
        RequireMaterialized: true,
        MaterializedConfig: makeMaterializedGateConfig0(),
      });

  const runner = typeof config.materializedRunner === 'function'
    ? config.materializedRunner
    : RunAll0;

  const record = await runner(input);

  if (!isRejectRecord0(record)) {
    return validationReject0(['RunAll0'], 'materialized gate did not reject the synthetic RunAll input', {
      observed: compactRecord0(record),
    });
  }

  const inner = compactReject0(record);

  if (inner.coord !== 'RunAll0.materialized') {
    return validationReject0(['RunAll0'], 'materialized gate rejected at the wrong coordinate', {
      expected: 'RunAll0.materialized',
      actual: inner,
    });
  }

  const nestedCoord = record.Witness?.detail?.inner?.coord ?? record.witness?.detail?.inner?.coord ?? null;

  if (nestedCoord !== 'CheckMaterialized0.scan') {
    return validationReject0(['RunAll0'], 'materialized gate did not expose CheckMaterialized0.scan as the inner rejection', {
      expected: 'CheckMaterialized0.scan',
      actual: nestedCoord,
      record: inner,
    });
  }

  return validationAccept0({
    kind: 'SyntheticMaterializedGate0NF',
    materializedGateRejected: true,
    materializedGateCoord: inner.coord,
    innerCoord: nestedCoord,
    rejectDigest: record.Digest ?? record.digest,
  });
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'SyntheticMarkerInventoryConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'SyntheticMarkerInventoryConfig0') {
    return validationReject0(['kind'], 'SyntheticMarkerInventoryConfig0 kind must be SyntheticMarkerInventoryConfig0 when present', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `SyntheticMarkerInventoryConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.rootDir !== 'string' || config.rootDir.length === 0) {
    return validationReject0(['rootDir'], 'SyntheticMarkerInventoryConfig0 rootDir must be a non-empty string', {
      actual: config.rootDir,
    });
  }

  for (const field of [
    'scanSourceFiles',
    'scanTests',
    'runMaterializedGateProbe',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `SyntheticMarkerInventoryConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  return validationAccept0({
    kind: 'SyntheticMarkerInventoryConfig0NF',
  });
}

function scanValueForMarkers0(value, path, hits, classHint) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const marker = firstMarkerInText0(value);

    if (marker !== null) {
      hits.push({
        sourceKind: 'value',
        path,
        marker,
        value,
        classHint,
      });
    }

    return;
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      scanValueForMarkers0(value[index], [...path, index], hits, classHint);
    }

    return;
  }

  if (!isPlainObject(value)) {
    return;
  }

  for (const key of Object.keys(value)) {
    const keyMarker = firstMarkerInText0(key);

    if (keyMarker !== null) {
      hits.push({
        sourceKind: 'value',
        path: [...path, key],
        marker: keyMarker,
        value: key,
        classHint,
      });
    }

    if (SYNTHETIC_NOTE_KEYS0.includes(normalizeKey0(key))) {
      hits.push({
        sourceKind: 'value',
        path: [...path, key],
        marker: normalizeKey0(key),
        value: value[key],
        classHint,
      });
    }

    scanValueForMarkers0(value[key], [...path, key], hits, classHint);
  }
}

function findSyntheticMarkersInText0(text, relativeFile) {
  const hits = [];
  const sourceKind = relativeFile.startsWith(`test${path.sep}`) || relativeFile.startsWith('test/')
    ? 'test'
    : 'source';

  for (const marker of SYNTHETIC_MARKER_TERMS0) {
    const lowerText = text.toLowerCase();
    const lowerMarker = marker.toLowerCase();
    let index = lowerText.indexOf(lowerMarker);

    while (index !== -1) {
      hits.push({
        sourceKind,
        file: relativeFile,
        marker,
        index,
        context: text.slice(Math.max(0, index - 80), Math.min(text.length, index + 120)),
      });

      index = lowerText.indexOf(lowerMarker, index + lowerMarker.length);
    }
  }

  return hits.sort((a, b) => {
    if (a.file !== b.file) {
      return String(a.file).localeCompare(String(b.file));
    }

    return a.index - b.index;
  });
}

function firstMarkerInText0(value) {
  const lower = String(value).toLowerCase();

  for (const marker of SYNTHETIC_MARKER_TERMS0) {
    if (lower.includes(marker)) {
      return marker;
    }
  }

  return null;
}

async function markerScanFiles0(rootDir, {
  scanSourceFiles,
  scanTests,
}) {
  const files = [];

  if (scanSourceFiles) {
    const rootEntries = await fs.readdir(rootDir, {
      withFileTypes: true,
    });

    for (const entry of rootEntries) {
      if (
        entry.isFile() &&
        entry.name.endsWith('.mjs') &&
        (
          entry.name === 'index.mjs' ||
          entry.name.startsWith('pcc-')
        )
      ) {
        files.push(entry.name);
      }
    }

    const binDir = path.join(rootDir, 'bin');

    try {
      const binEntries = await fs.readdir(binDir, {
        withFileTypes: true,
      });

      for (const entry of binEntries) {
        if (entry.isFile() && entry.name.endsWith('.mjs')) {
          files.push(path.join('bin', entry.name));
        }
      }
    } catch {
      // No bin directory means no bin files.
    }
  }

  if (scanTests) {
    const testDir = path.join(rootDir, 'test');

    try {
      const testEntries = await fs.readdir(testDir, {
        withFileTypes: true,
      });

      for (const entry of testEntries) {
        if (entry.isFile() && entry.name.endsWith('.mjs')) {
          files.push(path.join('test', entry.name));
        }
      }
    } catch {
      // No test directory means no test files.
    }
  }

  return files.sort();
}

function classCounts0(hits) {
  const counts = {};

  for (const hit of hits) {
    counts[hit.class] = (counts[hit.class] ?? 0) + 1;
  }

  return counts;
}

function normalizeKey0(value) {
  return String(value).replace(/[_\-\s]/g, '').toLowerCase();
}

function compactRecord0(value) {
  if (!isPlainObject(value)) {
    return value;
  }

  return {
    tag: value.tag,
    checker: value.checker ?? null,
    digest: value.Digest ?? value.digest ?? null,
  };
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

function isRejectRecord0(value) {
  return classifyRecord0(value) === 'reject';
}

function classifyRecord0(value) {
  if (!isPlainObject(value)) {
    return 'unknown';
  }

  const raw =
    value.tag ??
    value.kind ??
    value.verdict ??
    value.status ??
    value.result ??
    value.outcome;

  if (typeof raw !== 'string') {
    return 'unknown';
  }

  const normalized = raw.trim().toLowerCase();

  if (
    normalized === 'accept' ||
    normalized === 'accepted' ||
    normalized === 'ok' ||
    normalized === 'pass' ||
    normalized === 'passed'
  ) {
    return 'accept';
  }

  if (
    normalized === 'reject' ||
    normalized === 'rejected' ||
    normalized === 'err' ||
    normalized === 'error' ||
    normalized === 'fail' ||
    normalized === 'failed'
  ) {
    return 'reject';
  }

  return 'unknown';
}

function compactReject0(value) {
  if (!isPlainObject(value)) {
    return value;
  }

  return {
    checker: value.checker ?? null,
    coord: value.Coord ?? value.coord ?? null,
    path: value.Path ?? value.path ?? null,
    witness: value.Witness ?? value.witness ?? null,
    digest: value.Digest ?? value.digest ?? null,
  };
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}