import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedPCCPackShell0,
  sha256Utf8DigestRecord0,
} from './pcc-materialized-pack0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

const CHECKER_VERSION = 0;

export function makeMaterializedCoreExtractorConfig0(overrides = {}) {
  return {
    kind: 'MaterializedCoreExtractorConfig0',
    version: CHECKER_VERSION,
    checkShell: true,
    loaderConfig: {},
    requireCoreBoundary: true,
    ...overrides,
  };
}

export async function ExtractMaterializedCore0(shell, config = makeMaterializedCoreExtractorConfig0()) {
  const checker = 'ExtractMaterializedCore0';
  const ledger = [];
  const cfg = makeMaterializedCoreExtractorConfig0(config);

  const configCheck = validateExtractorConfig0(cfg);

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

  if (cfg.checkShell === true) {
    const shellRecord = await CheckMaterializedPCCPackShell0(shell);
    const shellResult = recordToValidation0(shellRecord, ['Shell']);

    ledger.push({
      phase: 'CheckMaterializedPCCPackShell0',
      status: shellResult.ok ? 'pass' : 'fail',
      digest: shellRecord.Digest ?? shellRecord.digest ?? digestCanonical0(shellRecord),
    });

    if (!shellResult.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.shell`,
        path: shellResult.path,
        witness: shellResult.witness,
        ledger,
      });
    }
  }

  const coreParsed = parseCanonicalJsonBytes0(shell?.CoreBytes, ['CoreBytes'], 'CoreBytes');

  ledger.push({
    phase: 'parseCoreBytes',
    status: coreParsed.ok ? 'pass' : 'fail',
    digest: digestCanonical0(coreParsed.nf ?? coreParsed.witness ?? null),
  });

  if (!coreParsed.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.coreBytes`,
      path: coreParsed.path,
      witness: coreParsed.witness,
      ledger,
    });
  }

  const packParsed = parseCanonicalJsonBytes0(shell?.PackBytes, ['PackBytes'], 'PackBytes');

  ledger.push({
    phase: 'parsePackBytes',
    status: packParsed.ok ? 'pass' : 'fail',
    digest: digestCanonical0(packParsed.nf ?? packParsed.witness ?? null),
  });

  if (!packParsed.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.packBytes`,
      path: packParsed.path,
      witness: packParsed.witness,
      ledger,
    });
  }

  const digestCheck = validateDisplayedDigests0(shell, coreParsed.value, packParsed.value);

  ledger.push({
    phase: 'displayedDigests',
    status: digestCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(digestCheck.nf ?? digestCheck.witness ?? null),
  });

  if (!digestCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.displayedDigests`,
      path: digestCheck.path,
      witness: digestCheck.witness,
      ledger,
    });
  }

  const coreLink = validatePackCoreLink0(shell, coreParsed.value, packParsed.value);

  ledger.push({
    phase: 'packCoreLink',
    status: coreLink.ok ? 'pass' : 'fail',
    digest: digestCanonical0(coreLink.nf ?? coreLink.witness ?? null),
  });

  if (!coreLink.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.packCoreLink`,
      path: coreLink.path,
      witness: coreLink.witness,
      ledger,
    });
  }

  if (cfg.requireCoreBoundary === true) {
    const boundary = validateCoreBoundary0(coreParsed.value);

    ledger.push({
      phase: 'coreBoundary',
      status: boundary.ok ? 'pass' : 'fail',
      digest: digestCanonical0(boundary.nf ?? boundary.witness ?? null),
    });

    if (!boundary.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.coreBoundary`,
        path: boundary.path,
        witness: boundary.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'MaterializedCoreExtraction0NF',
    checker,
    version: CHECKER_VERSION,
    coreKind: coreParsed.value.kind ?? null,
    packKind: packParsed.value.kind ?? null,
    coreDigest: shell.CoreDigest,
    packDigest: shell.PackDigest,
    coreObjectDigest: digestCanonical0(coreParsed.value),
    packObjectDigest: digestCanonical0(packParsed.value),
    packCoreDigest: digestCanonical0(packParsed.value.Core),
    packCoreMatchesCoreBytes: true,
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    CoreObject: coreParsed.value,
    PackObject: packParsed.value,
    coreObject: coreParsed.value,
    packObject: packParsed.value,
  };
}

export async function ExtractMaterializedCoreFile0(filePath, config = makeMaterializedCoreExtractorConfig0()) {
  const checker = 'ExtractMaterializedCoreFile0';
  const ledger = [];
  const cfg = makeMaterializedCoreExtractorConfig0(config);

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

  const extracted = await ExtractMaterializedCore0(loaded.Shell, cfg);
  const extractResult = recordToValidation0(extracted, ['Shell']);

  ledger.push({
    phase: 'ExtractMaterializedCore0',
    status: extractResult.ok ? 'pass' : 'fail',
    digest: extracted.Digest ?? extracted.digest ?? digestCanonical0(extracted),
  });

  if (!extractResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.extract`,
      path: extractResult.path,
      witness: extractResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedCoreFileExtraction0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    shellDigest: loaded.NF.shellDigest,
    coreExtractionDigest: extracted.Digest ?? extracted.digest,
    coreDigest: extracted.NF.coreDigest,
    packDigest: extracted.NF.packDigest,
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    CoreObject: extracted.CoreObject,
    PackObject: extracted.PackObject,
    coreObject: extracted.CoreObject,
    packObject: extracted.PackObject,
  };
}

function validateExtractorConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'MaterializedCoreExtractorConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'MaterializedCoreExtractorConfig0') {
    return validationReject0(['kind'], 'MaterializedCoreExtractorConfig0 kind must be MaterializedCoreExtractorConfig0 when present', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedCoreExtractorConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  if (typeof config.checkShell !== 'boolean') {
    return validationReject0(['checkShell'], 'MaterializedCoreExtractorConfig0 checkShell must be boolean', {
      actual: config.checkShell,
    });
  }

  if (typeof config.requireCoreBoundary !== 'boolean') {
    return validationReject0(['requireCoreBoundary'], 'MaterializedCoreExtractorConfig0 requireCoreBoundary must be boolean', {
      actual: config.requireCoreBoundary,
    });
  }

  if (!isPlainObject(config.loaderConfig)) {
    return validationReject0(['loaderConfig'], 'MaterializedCoreExtractorConfig0 loaderConfig must be an object', {
      actual: typeof config.loaderConfig,
    });
  }

  return validationAccept0({
    kind: 'MaterializedCoreExtractorConfig0NF',
  });
}

function parseCanonicalJsonBytes0(bytes, path, label) {
  if (typeof bytes !== 'string' || bytes.length === 0) {
    return validationReject0(path, `${label} must be a non-empty string`, {
      actual: typeof bytes,
    });
  }

  let value;

  try {
    value = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(path, `${label} must parse as JSON`, {
      error: error.message,
    });
  }

  const canonical = stableStringify0(value);

  if (canonical !== bytes) {
    return validationReject0(path, `${label} must be canonical JSON bytes`, {
      expectedDigest: sha256Utf8DigestRecord0(canonical),
      actualDigest: sha256Utf8DigestRecord0(bytes),
    });
  }

  return {
    ok: true,
    value,
    nf: {
      kind: 'ParsedMaterializedCanonicalBytes0NF',
      label,
      byteDigest: sha256Utf8DigestRecord0(bytes),
      objectDigest: digestCanonical0(value),
    },
  };
}

function validateDisplayedDigests0(shell) {
  const expectedCoreDigest = sha256Utf8DigestRecord0(shell.CoreBytes);
  const expectedPackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  if (!sameDigestRecord0(shell.CoreDigest, expectedCoreDigest)) {
    return validationReject0(['CoreDigest'], 'CoreDigest must be SHA256 over CoreBytes', {
      expected: expectedCoreDigest,
      actual: shell.CoreDigest,
    });
  }

  if (!sameDigestRecord0(shell.PackDigest, expectedPackDigest)) {
    return validationReject0(['PackDigest'], 'PackDigest must be SHA256 over PackBytes', {
      expected: expectedPackDigest,
      actual: shell.PackDigest,
    });
  }

  return validationAccept0({
    kind: 'DisplayedDigestLink0NF',
    coreDigest: shell.CoreDigest,
    packDigest: shell.PackDigest,
  });
}

function validatePackCoreLink0(shell, coreObject, packObject) {
  if (!isPlainObject(coreObject)) {
    return validationReject0(['CoreBytes'], 'CoreBytes must decode to an object', {
      actual: typeof coreObject,
    });
  }

  if (!isPlainObject(packObject)) {
    return validationReject0(['PackBytes'], 'PackBytes must decode to an object', {
      actual: typeof packObject,
    });
  }

  if (!Object.prototype.hasOwnProperty.call(packObject, 'Core')) {
    return validationReject0(['PackBytes', 'Core'], 'PackBytes object must contain a Core field', null);
  }

  if (!isPlainObject(packObject.Core)) {
    return validationReject0(['PackBytes', 'Core'], 'Pack.Core must be an object', {
      actual: typeof packObject.Core,
    });
  }

  const packCoreBytes = stableStringify0(packObject.Core);

  if (packCoreBytes !== shell.CoreBytes) {
    return validationReject0(['PackBytes', 'Core'], 'Pack.Core canonical bytes must exactly match CoreBytes', {
      expectedDigest: sha256Utf8DigestRecord0(shell.CoreBytes),
      actualDigest: sha256Utf8DigestRecord0(packCoreBytes),
    });
  }

  return validationAccept0({
    kind: 'PackCoreLink0NF',
    coreDigest: digestCanonical0(coreObject),
    packCoreDigest: digestCanonical0(packObject.Core),
  });
}

function validateCoreBoundary0(coreObject) {
  if (containsAcceptRun0(coreObject)) {
    return validationReject0(['CoreObject'], 'materialized core object must not contain AcceptRun', null);
  }

  if (coreObject.excludesAcceptRun !== true) {
    return validationReject0(['CoreObject', 'excludesAcceptRun'], 'materialized core must certify excludesAcceptRun', {
      actual: coreObject.excludesAcceptRun,
    });
  }

  if (coreObject.includesAcceptRun === true) {
    return validationReject0(['CoreObject', 'includesAcceptRun'], 'materialized core must not include AcceptRun', {
      actual: coreObject.includesAcceptRun,
    });
  }

  for (const field of [
    'canonicalByteEquality',
    'materializedOutputOnly',
    'noDigestOnlyEquality',
  ]) {
    if (coreObject[field] !== true) {
      return validationReject0(['CoreObject', field], `materialized core must certify ${field}`, {
        actual: coreObject[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedCoreBoundary0NF',
  });
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

function sameDigestRecord0(actual, expected) {
  return (
    isPlainObject(actual) &&
    actual.alg === expected.alg &&
    actual.bytes === expected.bytes &&
    actual.hex === expected.hex
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