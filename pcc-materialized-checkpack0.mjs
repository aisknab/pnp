import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckPackSufficiency0,
} from './pcc-pack-sufficiency0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  CheckMaterializedImports0,
  makeMaterializedImportShell0,
} from './pcc-materialized-imports0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_CHECKPCCPACK_PHASES0 = Object.freeze([
  'CheckMaterializedImports0',
  'ExtractMaterializedPCCPack0',
  'RunCheckPCCPackexp0',
  'EmitMaterializedCheckPCCPackStatus0',
]);

export const MATERIALIZED_CHECKPCCPACK_MODES0 = Object.freeze([
  'deferred',
  'strict',
]);

export const MATERIALIZED_CHECKPCCPACK_STATUSES0 = Object.freeze([
  'pending',
  'accepted',
]);

export function makeMaterializedCheckPCCPackConfig0(overrides = {}) {
  return {
    kind: 'MaterializedCheckPCCPackConfig0',
    version: CHECKER_VERSION,
    mode: 'deferred',
    importsConfig: {},
    packageCheckConfig: {},
    packageCheckRunner: null,
    ...overrides,
  };
}

export function makeMaterializedCheckPCCPackShell0(overrides = {}) {
  return makeMaterializedImportShell0(overrides);
}

export async function CheckMaterializedCheckPCCPack0(shell, config = makeMaterializedCheckPCCPackConfig0()) {
  const checker = 'CheckMaterializedCheckPCCPack0';
  const ledger = [];
  const cfg = makeMaterializedCheckPCCPackConfig0(config);

  const configCheck = validateConfig0(cfg);

  ledger.push({
    phase: 'config',
    status: configCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(configCheck.nf ?? configCheck.witness ?? null),
  });

  if (!configCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: configCheck.path,
      witness: configCheck.witness,
      ledger,
    });
  }

  const importsRecord = await CheckMaterializedImports0(shell, cfg.importsConfig ?? {});
  const imports = recordToValidation0(importsRecord, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedImports0',
    status: imports.ok ? 'pass' : 'fail',
    digest: importsRecord.Digest ?? importsRecord.digest ?? digestCanonical0(importsRecord),
  });

  if (!imports.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.imports`,
      path: imports.path,
      witness: imports.witness,
      ledger,
    });
  }

  const packObject = importsRecord.PackObject ?? importsRecord.packObject;
  const manifest = importsRecord.Manifest ?? importsRecord.manifest;
  const extract = validateExtractedPack0(packObject, manifest);

  ledger.push({
    phase: 'ExtractMaterializedPCCPack0',
    status: extract.ok ? 'pass' : 'fail',
    digest: digestCanonical0(extract.nf ?? extract.witness ?? null),
  });

  if (!extract.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.extract`,
      path: extract.path,
      witness: extract.witness,
      ledger,
    });
  }

  const runner = typeof cfg.packageCheckRunner === 'function'
    ? cfg.packageCheckRunner
    : CheckPackSufficiency0;

  const packageRecord = await runPackageChecker0(runner, packObject, cfg.packageCheckConfig ?? {});
  const packageClass = classifyRecord0(packageRecord);
  const packageDigest = packageRecord.Digest ?? packageRecord.digest ?? digestCanonical0(packageRecord);

  ledger.push({
    phase: 'RunCheckPCCPackexp0',
    status: packageClass === 'accept' || cfg.mode === 'deferred' ? 'pass' : 'fail',
    digest: packageDigest,
  });

  if (packageClass !== 'accept') {
    if (cfg.mode === 'strict') {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckPCCPackexp`,
        path: ['PackObject'],
        witness: {
          reason: 'strict materialized CheckPCCPackexp bridge requires accepted package check',
          detail: {
            packageCheck: compactReject0(packageRecord),
            packageCheckDigest: packageDigest,
          },
        },
        ledger,
      });
    }

    const pendingNF = makeStatusNF0({
      checker,
      mode: cfg.mode,
      status: 'pending',
      accepted: false,
      importsRecord,
      packageRecord,
      packageDigest,
      pendingReason: 'materialized package has not yet accepted CheckPCCPackexp; fixture path remains deferred',
    });

    ledger.push({
      phase: 'EmitMaterializedCheckPCCPackStatus0',
      status: 'pass',
      digest: digestCanonical0(pendingNF),
    });

    return makeAcceptRecord({
      checker,
      nf: pendingNF,
      ledger,
    });
  }

  const accepted = validateAcceptedPackageRecord0(packageRecord);

  ledger.push({
    phase: 'acceptedPackageBoundary',
    status: accepted.ok ? 'pass' : 'fail',
    digest: digestCanonical0(accepted.nf ?? accepted.witness ?? null),
  });

  if (!accepted.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.acceptedPackage`,
      path: accepted.path,
      witness: accepted.witness,
      ledger,
    });
  }

  const acceptedNF = makeStatusNF0({
    checker,
    mode: cfg.mode,
    status: 'accepted',
    accepted: true,
    importsRecord,
    packageRecord,
    packageDigest,
    pendingReason: null,
  });

  ledger.push({
    phase: 'EmitMaterializedCheckPCCPackStatus0',
    status: 'pass',
    digest: digestCanonical0(acceptedNF),
  });

  return makeAcceptRecord({
    checker,
    nf: acceptedNF,
    ledger,
  });
}

export async function CheckMaterializedCheckPCCPackFile0(filePath, config = makeMaterializedCheckPCCPackConfig0()) {
  const checker = 'CheckMaterializedCheckPCCPackFile0';
  const ledger = [];
  const cfg = makeMaterializedCheckPCCPackConfig0(config);

  const loaded = await LoadMaterializedPCCPackShellFile0(filePath, cfg.loaderConfig ?? {});
  const loadResult = recordToValidation0(loaded, ['file']);

  ledger.push({
    phase: 'load',
    status: loadResult.ok ? 'pass' : 'fail',
    digest: loaded.Digest ?? loaded.digest ?? digestCanonical0(loaded),
  });

  if (!loadResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.load`,
      path: loadResult.path,
      witness: loadResult.witness,
      ledger,
    });
  }

  const checked = await CheckMaterializedCheckPCCPack0(loaded.Shell, cfg);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedCheckPCCPack0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.checkPCCPack`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedCheckPCCPackFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    checkPCCPackDigest: checked.Digest ?? checked.digest,
    status: checked.NF.status,
    accepted: checked.NF.accepted,
    strict: checked.NF.strict,
    packDigest: checked.NF.packDigest,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedCheckPCCPackConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedCheckPCCPackConfig0') {
    return validationReject0(['kind'], 'MaterializedCheckPCCPackConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedCheckPCCPackConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (!MATERIALIZED_CHECKPCCPACK_MODES0.includes(config.mode)) {
    return validationReject0(['mode'], 'MaterializedCheckPCCPackConfig0 mode must be deferred or strict', {
      actual: config.mode,
    });
  }

  if (!isPlainObject(config.importsConfig)) {
    return validationReject0(['importsConfig'], 'importsConfig must be an object', {
      actual: typeof config.importsConfig,
    });
  }

  if (!isPlainObject(config.packageCheckConfig)) {
    return validationReject0(['packageCheckConfig'], 'packageCheckConfig must be an object', {
      actual: typeof config.packageCheckConfig,
    });
  }

  if (
    config.packageCheckRunner !== null &&
    typeof config.packageCheckRunner !== 'function'
  ) {
    return validationReject0(['packageCheckRunner'], 'packageCheckRunner must be null or a function', {
      actual: typeof config.packageCheckRunner,
    });
  }

  return validationAccept0({
    kind: 'MaterializedCheckPCCPackConfig0NF',
  });
}

function validateExtractedPack0(packObject, manifest) {
  if (!isPlainObject(packObject)) {
    return validationReject0(['PackObject'], 'materialized PackObject must be an object', {
      actual: typeof packObject,
    });
  }

  if (packObject.kind !== 'PCCPack0') {
    return validationReject0(['PackObject', 'kind'], 'materialized PackObject kind must be PCCPack0', {
      actual: packObject.kind,
    });
  }

  if (!isPlainObject(manifest)) {
    return validationReject0(['PackObject', 'Manifest'], 'materialized PackObject Manifest must be an object', {
      actual: typeof manifest,
    });
  }

  if (containsAcceptRun0(packObject.Core)) {
    return validationReject0(['PackObject', 'Core'], 'materialized package core must not contain AcceptRun', null);
  }

  if (Object.prototype.hasOwnProperty.call(packObject, 'AcceptRun')) {
    return validationReject0(['PackObject', 'AcceptRun'], 'materialized package must keep AcceptRun outside core package', null);
  }

  return validationAccept0({
    kind: 'MaterializedExtractedPCCPack0NF',
    packKind: packObject.kind,
    manifestKind: manifest.kind ?? null,
    packObjectDigest: digestCanonical0(packObject),
    manifestDigest: digestCanonical0(manifest),
  });
}

async function runPackageChecker0(runner, packObject, packageCheckConfig) {
  try {
    return await runner(packObject, packageCheckConfig);
  } catch (error) {
    const witness = {
      kind: 'ThrownPackageCheckerError0',
      message: error?.message ?? String(error),
      name: error?.name ?? null,
    };

    const rejectNF = {
      kind: 'ThrownPackageCheckerReject0NF',
      checker: 'CheckPCCPackexp',
      version: CHECKER_VERSION,
      coord: 'CheckPCCPackexp.runner',
      path: ['PackObject'],
      witness,
    };

    const digest = digestCanonical0(rejectNF);

    return {
      tag: 'reject',
      kind: 'reject',
      checker: 'CheckPCCPackexp',
      version: CHECKER_VERSION,
      Coord: 'CheckPCCPackexp.runner',
      Path: ['PackObject'],
      Witness: witness,
      Digest: digest,
      coord: 'CheckPCCPackexp.runner',
      path: ['PackObject'],
      witness,
      digest,
    };
  }
}

function validateAcceptedPackageRecord0(record) {
  const nf = record?.NF ?? record?.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['CheckPCCPackexp', 'NF'], 'accepted package checker must emit an NF object', {
      actual: typeof nf,
    });
  }

  const publicConclusion = nf.publicConclusion ?? nf.PublicConclusion ?? null;

  if (!samePublicConclusion0(publicConclusion, MATERIALIZED_PACK_PUBLIC_BOUNDARY0)) {
    return validationReject0(['CheckPCCPackexp', 'NF', 'publicConclusion'], 'accepted package checker public conclusion boundary mismatch', {
      expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
      actual: publicConclusion,
    });
  }

  return validationAccept0({
    kind: 'AcceptedMaterializedCheckPCCPack0NF',
    packageNFKind: nf.kind ?? null,
    publicConclusion,
  });
}

function makeStatusNF0({
  checker,
  mode,
  status,
  accepted,
  importsRecord,
  packageRecord,
  packageDigest,
  pendingReason,
}) {
  const importsNF = importsRecord.NF ?? importsRecord.nf ?? {};
  const packageNF = packageRecord?.NF ?? packageRecord?.nf ?? null;

  return {
    kind: 'MaterializedCheckPCCPack0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: MATERIALIZED_CHECKPCCPACK_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,
    checkerBoundary: 'CheckPCCPackexp',
    mode,
    strict: mode === 'strict',
    status,
    accepted,
    pendingReason,
    publicClaimBoundary: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
    packDigest: importsNF.packDigest ?? null,
    manifestDigest: importsNF.manifestDigest ?? null,
    importDigest: importsNF.importDigest ?? null,
    artefactImportCount: importsNF.artefactImportCount ?? null,
    packageImportEdgeCount: importsNF.packageImportEdgeCount ?? null,
    packageCheckDigest: packageDigest,
    packageCheckNFKind: isPlainObject(packageNF) ? packageNF.kind ?? null : null,
    packageCheckReject: accepted ? null : compactReject0(packageRecord),
  };
}

function containsAcceptRun0(value) {
  if (value === null || value === undefined) {
    return false;
  }

  if (typeof value === 'string') {
    return value === 'AcceptRun' || value === 'AcceptRun0';
  }

  if (Array.isArray(value)) {
    return value.some((entry) => containsAcceptRun0(entry));
  }

  if (!isPlainObject(value)) {
    return false;
  }

  for (const key of Object.keys(value)) {
    if (key === 'AcceptRun' || key === 'AcceptRun0') {
      return true;
    }

    if (containsAcceptRun0(value[key])) {
      return true;
    }
  }

  return false;
}

function samePublicConclusion0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.antecedent === b.antecedent &&
    a.consequent === b.consequent &&
    a.conditional === b.conditional
  );
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