import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedAggregateFile0,
} from './pcc-materialized-aggregate0.mjs';

import {
  CheckMaterializedFinalVerdictFile0,
} from './pcc-materialized-final-verdict0.mjs';

import {
  MATERIALIZED_FIXTURE_FILENAMES0,
} from './pcc-materialized-fixture-writer0.mjs';

import {
  MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0,
} from './pcc-materialized-accept-run-fixtures0.mjs';

import {
  WriteMaterializedFinalRunFixtureSet0,
} from './pcc-materialized-final-run-fixtures0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const MATERIALIZED_FINAL_RUN_ROUNDTRIP_CHECKS0 = Object.freeze([
  'WriteMaterializedFinalRunFixtureSet0.first',
  'WriteMaterializedFinalRunFixtureSet0.second',
  'CompareFinalRunFixtureBytes0',
  'CheckMaterializedAggregateFile0',
  'CheckMaterializedFinalVerdictFile0.pending',
  'CheckMaterializedFinalVerdictFile0.reject',
  'CheckMaterializedFinalVerdictFile0.accepted',
  'CLI.check-materialized-aggregate0',
  'CLI.check-materialized-final-verdict0.pending',
  'CLI.check-materialized-final-verdict0.reject',
  'CLI.check-materialized-final-verdict0.accepted',
]);

export const MATERIALIZED_FINAL_RUN_ROUNDTRIP_FILES0 = Object.freeze([
  Object.freeze({
    kind: 'MaterializedPCCPack0',
    verdict: null,
    filename: MATERIALIZED_FIXTURE_FILENAMES0.pack,
  }),
  Object.freeze({
    kind: 'MaterializedAcceptRun0.pending',
    verdict: 'pending',
    filename: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.pending,
  }),
  Object.freeze({
    kind: 'MaterializedAcceptRun0.reject',
    verdict: 'reject',
    filename: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.reject,
  }),
  Object.freeze({
    kind: 'MaterializedAcceptRun0.accepted',
    verdict: 'accept',
    filename: MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.accepted,
  }),
]);

export function makeMaterializedFinalRunRoundtripConfig0(overrides = {}) {
  return {
    kind: 'MaterializedFinalRunRoundtripConfig0',
    version: CHECKER_VERSION,
    outputDir: path.join(process.cwd(), 'materialized-final-run-roundtrip0'),
    canonicalEnvelopeBytes: false,
    overwrite: true,
    verifyFinalRunWriter: true,
    runCliChecks: true,
    mutateSecondWrite: null,
    ...overrides,
  };
}

export async function CheckMaterializedFinalRunRoundtrip0(config = makeMaterializedFinalRunRoundtripConfig0()) {
  const checker = 'CheckMaterializedFinalRunRoundtrip0';
  const ledger = [];
  const cfg = makeMaterializedFinalRunRoundtripConfig0(config);

  const shape = validateRoundtripConfig0(cfg);

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

  const firstWrite = await WriteMaterializedFinalRunFixtureSet0({
    outputDir: cfg.outputDir,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    overwrite: cfg.overwrite,
    verifyAcceptRunWriter: cfg.verifyFinalRunWriter,
    verifyDirect: cfg.verifyFinalRunWriter,
    verifyCli: cfg.verifyFinalRunWriter,
  });
  const firstWriteResult = recordToValidation0(firstWrite, ['outputDir']);

  ledger.push({
    phase: 'WriteMaterializedFinalRunFixtureSet0.first',
    status: firstWriteResult.ok ? 'pass' : 'fail',
    digest: firstWrite.Digest ?? firstWrite.digest ?? digestCanonical0(firstWrite),
  });

  if (!firstWriteResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.writeFirst`,
      path: firstWriteResult.path,
      witness: firstWriteResult.witness,
      ledger,
    });
  }

  const firstSnapshot = await readFinalRunFixtureSnapshot0(cfg.outputDir);

  ledger.push({
    phase: 'ReadFirstSnapshot0',
    status: firstSnapshot.ok ? 'pass' : 'fail',
    digest: digestCanonical0(firstSnapshot.nf ?? firstSnapshot.witness ?? null),
  });

  if (!firstSnapshot.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.readFirstSnapshot`,
      path: firstSnapshot.path,
      witness: firstSnapshot.witness,
      ledger,
    });
  }

  const secondWrite = await WriteMaterializedFinalRunFixtureSet0({
    outputDir: cfg.outputDir,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    overwrite: true,
    verifyAcceptRunWriter: cfg.verifyFinalRunWriter,
    verifyDirect: cfg.verifyFinalRunWriter,
    verifyCli: cfg.verifyFinalRunWriter,
  });
  const secondWriteResult = recordToValidation0(secondWrite, ['outputDir']);

  ledger.push({
    phase: 'WriteMaterializedFinalRunFixtureSet0.second',
    status: secondWriteResult.ok ? 'pass' : 'fail',
    digest: secondWrite.Digest ?? secondWrite.digest ?? digestCanonical0(secondWrite),
  });

  if (!secondWriteResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.writeSecond`,
      path: secondWriteResult.path,
      witness: secondWriteResult.witness,
      ledger,
    });
  }

  if (typeof cfg.mutateSecondWrite === 'function') {
    await cfg.mutateSecondWrite({
      outputDir: cfg.outputDir,
      files: MATERIALIZED_FINAL_RUN_ROUNDTRIP_FILES0,
    });
  }

  const secondSnapshot = await readFinalRunFixtureSnapshot0(cfg.outputDir);

  ledger.push({
    phase: 'ReadSecondSnapshot0',
    status: secondSnapshot.ok ? 'pass' : 'fail',
    digest: digestCanonical0(secondSnapshot.nf ?? secondSnapshot.witness ?? null),
  });

  if (!secondSnapshot.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.readSecondSnapshot`,
      path: secondSnapshot.path,
      witness: secondSnapshot.witness,
      ledger,
    });
  }

  const compare = compareFinalRunSnapshots0(firstSnapshot.snapshot, secondSnapshot.snapshot);

  ledger.push({
    phase: 'CompareFinalRunFixtureBytes0',
    status: compare.ok ? 'pass' : 'fail',
    digest: digestCanonical0(compare.nf ?? compare.witness ?? null),
  });

  if (!compare.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.compareBytes`,
      path: compare.path,
      witness: compare.witness,
      ledger,
    });
  }

  const direct = await verifyDirectFinalRunRoundtrip0(cfg);

  ledger.push({
    phase: 'VerifyDirectFinalRunRoundtrip0',
    status: direct.ok ? 'pass' : 'fail',
    digest: digestCanonical0(direct.nf ?? direct.witness ?? null),
  });

  if (!direct.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.direct`,
      path: direct.path,
      witness: direct.witness,
      ledger,
    });
  }

  let cli = validationAccept0({
    kind: 'MaterializedFinalRunCliRoundtripSkipped0NF',
    cliChecked: false,
    records: [],
  });

  if (cfg.runCliChecks === true) {
    cli = await verifyCliFinalRunRoundtrip0(cfg);
  }

  ledger.push({
    phase: 'VerifyCliFinalRunRoundtrip0',
    status: cli.ok ? 'pass' : 'fail',
    digest: digestCanonical0(cli.nf ?? cli.witness ?? null),
  });

  if (!cli.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.cli`,
      path: cli.path,
      witness: cli.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedFinalRunRoundtrip0NF',
    checker,
    version: CHECKER_VERSION,
    outputDir: cfg.outputDir,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    deterministic: true,
    fileCount: compare.nf.fileCount,
    byteComparisons: compare.nf.comparisons,
    directRecords: direct.nf.records,
    cliRecords: cli.nf.records,
    acceptedPublicConclusionOnly: true,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

async function readFinalRunFixtureSnapshot0(outputDir) {
  const entries = [];

  for (const file of MATERIALIZED_FINAL_RUN_ROUNDTRIP_FILES0) {
    const filePath = path.join(outputDir, file.filename);

    let text;

    try {
      text = await fs.readFile(filePath, 'utf8');
    } catch (error) {
      return validationReject0(['files', file.filename], 'final-run roundtrip fixture file must be readable', {
        filePath,
        error: error.message,
      });
    }

    entries.push({
      ...file,
      filePath,
      text,
      byteLength: Buffer.byteLength(text, 'utf8'),
      digest: digestCanonical0(text),
    });
  }

  return {
    ok: true,
    snapshot: entries,
    nf: {
      kind: 'MaterializedFinalRunSnapshot0NF',
      fileCount: entries.length,
      files: entries.map((entry) => ({
        kind: entry.kind,
        verdict: entry.verdict,
        filename: entry.filename,
        filePath: entry.filePath,
        byteLength: entry.byteLength,
        digest: entry.digest,
      })),
    },
  };
}

function compareFinalRunSnapshots0(first, second) {
  const comparisons = [];

  for (const firstEntry of first) {
    const secondEntry = second.find((entry) => entry.filename === firstEntry.filename);

    if (secondEntry === undefined) {
      return validationReject0(['files', firstEntry.filename], 'second final-run snapshot is missing a file', {
        filename: firstEntry.filename,
      });
    }

    if (firstEntry.text !== secondEntry.text) {
      return validationReject0(['files', firstEntry.filename], 'final-run fixture bytes are not deterministic across repeated writes', {
        filename: firstEntry.filename,
        first: {
          byteLength: firstEntry.byteLength,
          digest: firstEntry.digest,
        },
        second: {
          byteLength: secondEntry.byteLength,
          digest: secondEntry.digest,
        },
      });
    }

    comparisons.push({
      kind: firstEntry.kind,
      verdict: firstEntry.verdict,
      filename: firstEntry.filename,
      filePath: firstEntry.filePath,
      byteLength: firstEntry.byteLength,
      digest: firstEntry.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalRunByteComparisons0NF',
    fileCount: comparisons.length,
    comparisons,
  });
}

async function verifyDirectFinalRunRoundtrip0(config) {
  const packFile = path.join(config.outputDir, MATERIALIZED_FIXTURE_FILENAMES0.pack);

  const aggregate = await CheckMaterializedAggregateFile0(packFile, {
    loaderConfig: {
      requireCanonicalEnvelopeBytes: config.canonicalEnvelopeBytes,
    },
  });

  if (isRejectRecord0(aggregate)) {
    return validationReject0(['files', MATERIALIZED_FIXTURE_FILENAMES0.pack], 'final-run roundtrip aggregate file rejected', {
      inner: compactReject0(aggregate),
    });
  }

  const records = [
    {
      checker: 'CheckMaterializedAggregateFile0',
      filename: MATERIALIZED_FIXTURE_FILENAMES0.pack,
      digest: aggregate.Digest ?? aggregate.digest,
    },
  ];

  for (const file of MATERIALIZED_FINAL_RUN_ROUNDTRIP_FILES0) {
    if (file.verdict === null) {
      continue;
    }

    const filePath = path.join(config.outputDir, file.filename);
    const record = await CheckMaterializedFinalVerdictFile0(filePath);

    if (isRejectRecord0(record)) {
      return validationReject0(['files', file.filename], 'final-run roundtrip final verdict file rejected', {
        file,
        inner: compactReject0(record),
      });
    }

    const verdict = validateFinalVerdictNF0(record.NF ?? record.nf, file, ['files', file.filename]);

    if (!verdict.ok) {
      return verdict;
    }

    records.push({
      checker: 'CheckMaterializedFinalVerdictFile0',
      filename: file.filename,
      verdict: file.verdict,
      digest: record.Digest ?? record.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalRunDirectRoundtrip0NF',
    records,
  });
}

async function verifyCliFinalRunRoundtrip0(config) {
  const packFile = path.join(config.outputDir, MATERIALIZED_FIXTURE_FILENAMES0.pack);
  const aggregateArgs = [
    path.join(REPO_ROOT, 'bin', 'check-materialized-aggregate0.mjs'),
    packFile,
  ];

  if (config.canonicalEnvelopeBytes === true) {
    aggregateArgs.push('--canonical-envelope-bytes');
  }

  const checks = [
    {
      label: 'CLI.check-materialized-aggregate0',
      filename: MATERIALIZED_FIXTURE_FILENAMES0.pack,
      args: aggregateArgs,
      expectedChecker: 'CheckMaterializedAggregateFile0',
      verdict: null,
    },
    ...MATERIALIZED_FINAL_RUN_ROUNDTRIP_FILES0
      .filter((file) => file.verdict !== null)
      .map((file) => ({
        label: `CLI.check-materialized-final-verdict0.${file.verdict}`,
        filename: file.filename,
        args: [
          path.join(REPO_ROOT, 'bin', 'check-materialized-final-verdict0.mjs'),
          path.join(config.outputDir, file.filename),
        ],
        expectedChecker: 'CheckMaterializedFinalVerdictFile0',
        verdict: file.verdict,
      })),
  ];

  const records = [];

  for (const check of checks) {
    const child = spawnSync(process.execPath, check.args, {
      encoding: 'utf8',
      windowsHide: true,
    });

    if (child.status !== 0) {
      return validationReject0(['cli', check.label], 'final-run roundtrip CLI command failed', {
        label: check.label,
        args: check.args,
        status: child.status,
        stdout: child.stdout,
        stderr: child.stderr,
        error: child.error?.message ?? null,
      });
    }

    let parsed;

    try {
      parsed = JSON.parse(child.stdout);
    } catch (error) {
      return validationReject0(['cli', check.label], 'final-run roundtrip CLI did not emit JSON', {
        label: check.label,
        stdout: child.stdout,
        error: error.message,
      });
    }

    if (parsed.tag !== 'accept') {
      return validationReject0(['cli', check.label], 'final-run roundtrip CLI emitted non-accept', {
        label: check.label,
        parsed,
      });
    }

    if (parsed.checker !== check.expectedChecker) {
      return validationReject0(['cli', check.label, 'checker'], 'final-run roundtrip CLI emitted unexpected checker', {
        expected: check.expectedChecker,
        actual: parsed.checker,
      });
    }

    if (check.verdict !== null) {
      const verdict = validateFinalVerdictNF0(parsed, {
        filename: check.filename,
        verdict: check.verdict,
      }, ['cli', check.label]);

      if (!verdict.ok) {
        return verdict;
      }
    }

    records.push({
      checker: check.label,
      filename: check.filename,
      verdict: check.verdict,
      digest: parsed.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalRunCliRoundtrip0NF',
    cliChecked: true,
    records,
  });
}

function validateFinalVerdictNF0(nf, file, path) {
  if (!isPlainObject(nf)) {
    return validationReject0(path, 'final verdict summary must be an object', {
      file,
      actual: typeof nf,
    });
  }

  if (nf.verdict !== file.verdict) {
    return validationReject0([...path, 'verdict'], 'final-run fixture returned wrong verdict', {
      expected: file.verdict,
      actual: nf.verdict,
    });
  }

  if (file.verdict === 'pending') {
    if (
      nf.replayAccepted !== false ||
      nf.publicConclusionEmitted !== false ||
      nf.publicConclusion !== null
    ) {
      return validationReject0(path, 'pending final-run fixture must emit no public conclusion', {
        file,
        nf,
      });
    }
  }

  if (file.verdict === 'reject') {
    if (
      nf.replayAccepted !== false ||
      nf.publicConclusionEmitted !== false ||
      nf.publicConclusion !== null ||
      nf.rejectLogCount !== 1
    ) {
      return validationReject0(path, 'reject final-run fixture must emit one replayable failure and no public conclusion', {
        file,
        nf,
      });
    }
  }

  if (file.verdict === 'accept') {
    if (
      nf.replayAccepted !== true ||
      nf.publicConclusionEmitted !== true ||
      !isPlainObject(nf.publicConclusion) ||
      nf.publicConclusion.consequent !== 'P = NP'
    ) {
      return validationReject0(path, 'accepted final-run fixture must emit public conclusion only after accepted replay', {
        file,
        nf,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedFinalRunVerdictCheck0NF',
    verdict: file.verdict,
  });
}

function validateRoundtripConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedFinalRunRoundtripConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedFinalRunRoundtripConfig0') {
    return validationReject0(['kind'], 'MaterializedFinalRunRoundtripConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedFinalRunRoundtripConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.outputDir !== 'string' || config.outputDir.length === 0) {
    return validationReject0(['outputDir'], 'MaterializedFinalRunRoundtripConfig0 outputDir must be a non-empty string', {
      actual: config.outputDir,
    });
  }

  for (const field of [
    'canonicalEnvelopeBytes',
    'overwrite',
    'verifyFinalRunWriter',
    'runCliChecks',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedFinalRunRoundtripConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (
    config.mutateSecondWrite !== null &&
    typeof config.mutateSecondWrite !== 'function'
  ) {
    return validationReject0(['mutateSecondWrite'], 'mutateSecondWrite must be null or a function', {
      actual: typeof config.mutateSecondWrite,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalRunRoundtripConfig0NF',
  });
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
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