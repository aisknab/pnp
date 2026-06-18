import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  CheckMaterializedAggregateFile0,
} from './pcc-materialized-aggregate0.mjs';

import {
  CheckMaterializedAcceptanceBridgeFile0,
} from './pcc-materialized-acceptance-bridge0.mjs';

import {
  MATERIALIZED_FIXTURE_FILENAMES0,
  WriteMaterializedFixtureSet0,
} from './pcc-materialized-fixture-writer0.mjs';

const CHECKER_VERSION = 0;
const REPO_ROOT = path.dirname(fileURLToPath(import.meta.url));

export const MATERIALIZED_ROUNDTRIP_CHECKS0 = Object.freeze([
  'WriteMaterializedFixtureSet0.first',
  'WriteMaterializedFixtureSet0.second',
  'CompareFixtureBytes0',
  'CheckMaterializedPCCPackShellFile0',
  'CheckMaterializedAggregateFile0',
  'CheckMaterializedAcceptanceBridgeFile0.pending',
  'CheckMaterializedAcceptanceBridgeFile0.accepted',
  'CLI.check-materialized-shell0',
  'CLI.check-materialized-aggregate0',
  'CLI.check-materialized-acceptance-bridge0.pending',
  'CLI.check-materialized-acceptance-bridge0.accepted',
]);

export function makeMaterializedFixtureRoundtripConfig0(overrides = {}) {
  return {
    kind: 'MaterializedFixtureRoundtripConfig0',
    version: CHECKER_VERSION,
    outputDirA: path.join(process.cwd(), 'materialized-roundtrip0', 'a'),
    outputDirB: path.join(process.cwd(), 'materialized-roundtrip0', 'b'),
    canonicalEnvelopeBytes: false,
    overwrite: true,
    writerVerify: true,
    runCliChecks: true,
    mutateSecondWrite: null,
    ...overrides,
  };
}

export async function CheckMaterializedFixtureRoundtrip0(config = makeMaterializedFixtureRoundtripConfig0()) {
  const checker = 'CheckMaterializedFixtureRoundtrip0';
  const ledger = [];
  const cfg = makeMaterializedFixtureRoundtripConfig0(config);

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

  const firstWrite = await WriteMaterializedFixtureSet0({
    outputDir: cfg.outputDirA,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    overwrite: cfg.overwrite,
    verify: cfg.writerVerify,
  });
  const firstWriteResult = recordToValidation0(firstWrite, ['outputDirA']);

  ledger.push({
    phase: 'WriteMaterializedFixtureSet0.first',
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

  const secondWrite = await WriteMaterializedFixtureSet0({
    outputDir: cfg.outputDirB,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    overwrite: cfg.overwrite,
    verify: cfg.writerVerify,
  });
  const secondWriteResult = recordToValidation0(secondWrite, ['outputDirB']);

  ledger.push({
    phase: 'WriteMaterializedFixtureSet0.second',
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
      outputDir: cfg.outputDirB,
      files: secondWrite.NF.files,
    });
  }

  const compare = await compareFixtureBytes0(cfg);

  ledger.push({
    phase: 'CompareFixtureBytes0',
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

  const direct = await verifyDirectRoundtrip0(cfg);

  ledger.push({
    phase: 'VerifyDirectRoundtrip0',
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
    kind: 'MaterializedFixtureCliRoundtripSkipped0NF',
    cliChecked: false,
    records: [],
  });

  if (cfg.runCliChecks === true) {
    cli = await verifyCliRoundtrip0(cfg);
  }

  ledger.push({
    phase: 'VerifyCliRoundtrip0',
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
    kind: 'MaterializedFixtureRoundtrip0NF',
    checker,
    version: CHECKER_VERSION,
    canonicalEnvelopeBytes: cfg.canonicalEnvelopeBytes,
    outputDirA: cfg.outputDirA,
    outputDirB: cfg.outputDirB,
    fileCount: compare.nf.fileCount,
    deterministic: true,
    byteComparisons: compare.nf.comparisons,
    directRecords: direct.nf.records,
    cliRecords: cli.nf.records,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckMaterializedFixtureRoundtripDirs0(outputDirA, outputDirB, overrides = {}) {
  return CheckMaterializedFixtureRoundtrip0({
    outputDirA,
    outputDirB,
    ...overrides,
  });
}

function validateRoundtripConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedFixtureRoundtripConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedFixtureRoundtripConfig0') {
    return validationReject0(['kind'], 'MaterializedFixtureRoundtripConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedFixtureRoundtripConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'outputDirA',
    'outputDirB',
  ]) {
    if (typeof config[field] !== 'string' || config[field].length === 0) {
      return validationReject0([field], `MaterializedFixtureRoundtripConfig0 ${field} must be a non-empty string`, {
        actual: config[field],
      });
    }
  }

  if (path.resolve(config.outputDirA) === path.resolve(config.outputDirB)) {
    return validationReject0(['outputDirB'], 'roundtrip output directories must be distinct', {
      outputDirA: config.outputDirA,
      outputDirB: config.outputDirB,
    });
  }

  for (const field of [
    'canonicalEnvelopeBytes',
    'overwrite',
    'writerVerify',
    'runCliChecks',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `MaterializedFixtureRoundtripConfig0 ${field} must be boolean`, {
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
    kind: 'MaterializedFixtureRoundtripConfig0NF',
  });
}

async function compareFixtureBytes0(config) {
  const comparisons = [];

  for (const filename of Object.values(MATERIALIZED_FIXTURE_FILENAMES0)) {
    const fileA = path.join(config.outputDirA, filename);
    const fileB = path.join(config.outputDirB, filename);

    const textA = await readUtf8File0(fileA, ['outputDirA', filename]);

    if (!textA.ok) {
      return textA;
    }

    const textB = await readUtf8File0(fileB, ['outputDirB', filename]);

    if (!textB.ok) {
      return textB;
    }

    const digestA = digestCanonical0(textA.text);
    const digestB = digestCanonical0(textB.text);

    if (textA.text !== textB.text) {
      return validationReject0(['files', filename], 'roundtrip fixture bytes are not deterministic across repeated writes', {
        filename,
        first: {
          filePath: fileA,
          byteLength: Buffer.byteLength(textA.text, 'utf8'),
          digest: digestA,
        },
        second: {
          filePath: fileB,
          byteLength: Buffer.byteLength(textB.text, 'utf8'),
          digest: digestB,
        },
      });
    }

    comparisons.push({
      filename,
      byteLength: Buffer.byteLength(textA.text, 'utf8'),
      digest: digestA,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFixtureByteComparisons0NF',
    fileCount: comparisons.length,
    comparisons,
  });
}

async function verifyDirectRoundtrip0(config) {
  const packFile = path.join(config.outputDirA, MATERIALIZED_FIXTURE_FILENAMES0.pack);
  const pendingBridgeFile = path.join(config.outputDirA, MATERIALIZED_FIXTURE_FILENAMES0.pendingBridge);
  const acceptedBridgeFile = path.join(config.outputDirA, MATERIALIZED_FIXTURE_FILENAMES0.acceptedBridge);

  const checks = [
    {
      label: 'CheckMaterializedPCCPackShellFile0',
      path: ['files', MATERIALIZED_FIXTURE_FILENAMES0.pack],
      run: () => CheckMaterializedPCCPackShellFile0(packFile, {
        requireCanonicalEnvelopeBytes: config.canonicalEnvelopeBytes,
      }),
    },
    {
      label: 'CheckMaterializedAggregateFile0',
      path: ['files', MATERIALIZED_FIXTURE_FILENAMES0.pack],
      run: () => CheckMaterializedAggregateFile0(packFile, {
        loaderConfig: {
          requireCanonicalEnvelopeBytes: config.canonicalEnvelopeBytes,
        },
      }),
    },
    {
      label: 'CheckMaterializedAcceptanceBridgeFile0.pending',
      path: ['files', MATERIALIZED_FIXTURE_FILENAMES0.pendingBridge],
      run: () => CheckMaterializedAcceptanceBridgeFile0(pendingBridgeFile),
      expect: (record) => record.NF.replayVerdict === 'pending' && record.NF.publicConclusionEmitted === false,
    },
    {
      label: 'CheckMaterializedAcceptanceBridgeFile0.accepted',
      path: ['files', MATERIALIZED_FIXTURE_FILENAMES0.acceptedBridge],
      run: () => CheckMaterializedAcceptanceBridgeFile0(acceptedBridgeFile),
      expect: (record) => record.NF.replayVerdict === 'accept' && record.NF.publicConclusionEmitted === true,
    },
  ];

  const records = [];

  for (const check of checks) {
    const record = await check.run();

    if (isRejectRecord0(record)) {
      return validationReject0(check.path, 'direct roundtrip checker rejected a fixture file', {
        checker: check.label,
        inner: compactReject0(record),
      });
    }

    if (check.expect !== undefined && check.expect(record) !== true) {
      return validationReject0(check.path, 'direct roundtrip checker accepted with unexpected normal form', {
        checker: check.label,
        nf: record.NF ?? record.nf,
      });
    }

    records.push({
      checker: check.label,
      digest: record.Digest ?? record.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFixtureDirectRoundtrip0NF',
    records,
  });
}

async function verifyCliRoundtrip0(config) {
  const packFile = path.join(config.outputDirA, MATERIALIZED_FIXTURE_FILENAMES0.pack);
  const pendingBridgeFile = path.join(config.outputDirA, MATERIALIZED_FIXTURE_FILENAMES0.pendingBridge);
  const acceptedBridgeFile = path.join(config.outputDirA, MATERIALIZED_FIXTURE_FILENAMES0.acceptedBridge);

  const shellArgs = [
    path.join(REPO_ROOT, 'bin', 'check-materialized-shell0.mjs'),
    packFile,
  ];

  if (config.canonicalEnvelopeBytes === true) {
    shellArgs.push('--canonical-envelope-bytes');
  }

  const aggregateArgs = [
    path.join(REPO_ROOT, 'bin', 'check-materialized-aggregate0.mjs'),
    packFile,
  ];

  if (config.canonicalEnvelopeBytes === true) {
    aggregateArgs.push('--canonical-envelope-bytes');
  }

  const checks = [
    {
      label: 'CLI.check-materialized-shell0',
      args: shellArgs,
      expectedChecker: 'CheckMaterializedPCCPackShellFile0',
    },
    {
      label: 'CLI.check-materialized-aggregate0',
      args: aggregateArgs,
      expectedChecker: 'CheckMaterializedAggregateFile0',
    },
    {
      label: 'CLI.check-materialized-acceptance-bridge0.pending',
      args: [
        path.join(REPO_ROOT, 'bin', 'check-materialized-acceptance-bridge0.mjs'),
        pendingBridgeFile,
      ],
      expectedChecker: 'CheckMaterializedAcceptanceBridgeFile0',
      expect: (json) => json.replayVerdict === 'pending' && json.publicConclusionEmitted === false,
    },
    {
      label: 'CLI.check-materialized-acceptance-bridge0.accepted',
      args: [
        path.join(REPO_ROOT, 'bin', 'check-materialized-acceptance-bridge0.mjs'),
        acceptedBridgeFile,
      ],
      expectedChecker: 'CheckMaterializedAcceptanceBridgeFile0',
      expect: (json) => json.replayVerdict === 'accept' && json.publicConclusionEmitted === true,
    },
  ];

  const records = [];

  for (const check of checks) {
    const child = spawnSync(process.execPath, check.args, {
      encoding: 'utf8',
      windowsHide: true,
    });

    if (child.status !== 0) {
      return validationReject0(['cli', check.label], 'materialized fixture CLI roundtrip command failed', {
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
      parsed = parseCliJson0(child.stdout);
    } catch (error) {
      return validationReject0(['cli', check.label], 'materialized fixture CLI did not emit JSON', {
        label: check.label,
        stdout: child.stdout,
        error: error.message,
      });
    }

    if (parsed.tag !== 'accept') {
      return validationReject0(['cli', check.label], 'materialized fixture CLI emitted non-accept record', {
        label: check.label,
        parsed,
      });
    }

    if (parsed.checker !== check.expectedChecker) {
      return validationReject0(['cli', check.label, 'checker'], 'materialized fixture CLI emitted unexpected checker', {
        label: check.label,
        expected: check.expectedChecker,
        actual: parsed.checker,
      });
    }

    if (check.expect !== undefined && check.expect(parsed) !== true) {
      return validationReject0(['cli', check.label], 'materialized fixture CLI accepted with unexpected summary', {
        label: check.label,
        parsed,
      });
    }

    records.push({
      checker: check.label,
      digest: parsed.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFixtureCliRoundtrip0NF',
    cliChecked: true,
    records,
  });
}

async function readUtf8File0(filePath, rejectPath) {
  try {
    const text = await fs.readFile(filePath, 'utf8');

    return {
      ok: true,
      text,
    };
  } catch (error) {
    return validationReject0(rejectPath, 'roundtrip fixture file must be readable', {
      filePath,
      error: error.message,
    });
  }
}

function parseCliJson0(stdout) {
  const firstBrace = stdout.indexOf('{');

  if (firstBrace === -1) {
    throw new Error('stdout contains no JSON object');
  }

  return JSON.parse(stdout.slice(firstBrace));
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