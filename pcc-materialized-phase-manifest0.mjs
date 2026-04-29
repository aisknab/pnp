import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  ACCEPT_RUN_PHASES0,
} from './pcc-accept-run0.mjs';

import {
  PCCPACK_REQUIRED_FIELDS0,
} from './pcc-pack-sufficiency0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  ExtractMaterializedCore0,
} from './pcc-materialized-core-extractor0.mjs';

import {
  CheckMaterializedPCCPackShell0,
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
  canonicalBytesForMaterializedObject0,
  makeMaterializedPCCPackShell0,
  sha256Utf8DigestRecord0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_PHASE_MANIFEST_REQUIRED_FIELDS0 = Object.freeze([
  'kind',
  'version',
  'checker',
  'phaseOrder',
  'requiredArtefacts',
  'coreDigest',
  'coreBytesDigest',
  'coreExcludesAcceptRun',
  'acceptRunLocation',
  'canonicalBytePolicy',
  'publicClaimBoundary',
]);

export const MATERIALIZED_PHASE_MANIFEST_KIND0 = 'MaterializedPhaseManifest0';

export function makeMaterializedPhaseManifest0({
  coreDigest,
  coreBytesDigest,
  requiredArtefacts = PCCPACK_REQUIRED_FIELDS0,
  phaseOrder = ACCEPT_RUN_PHASES0,
} = {}) {
  return {
    kind: MATERIALIZED_PHASE_MANIFEST_KIND0,
    version: CHECKER_VERSION,
    checker: 'CheckPCCPackexp',
    phaseOrder: [...phaseOrder],
    requiredArtefacts: [...requiredArtefacts],
    coreDigest,
    coreBytesDigest,
    coreExcludesAcceptRun: true,
    acceptRunLocation: 'outside-core',
    canonicalBytePolicy: {
      canonicalJson: true,
      fullBytesCompared: true,
      digestEqualityIsNotObjectEquality: true,
      materializedOutputOnly: true,
      generatorUntrusted: true,
    },
    publicClaimBoundary: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
  };
}

export function makeMaterializedPhaseManifestShell0(overrides = {}) {
  const shell = makeMaterializedPCCPackShell0();
  const coreObject = JSON.parse(shell.CoreBytes);
  const packObject = JSON.parse(shell.PackBytes);

  const manifest = makeMaterializedPhaseManifest0({
    coreDigest: shell.CoreDigest,
    coreBytesDigest: sha256Utf8DigestRecord0(shell.CoreBytes),
  });

  packObject.Core = coreObject;
  packObject.Manifest = manifest;

  shell.PackBytes = canonicalBytesForMaterializedObject0(packObject);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  shell.Manifest = {
    kind: 'MaterializedPackManifestEnvelope0',
    version: CHECKER_VERSION,
    checker: 'CheckPCCPackexp',
    phaseManifestDigest: digestCanonical0(manifest),
    requiredChecks: [
      'CheckMaterialized0',
      'ExtractMaterializedCore0',
      'CheckMaterializedPhaseManifest0',
      'CheckPCCPackexp',
      'ReplayAcceptRun0',
      'EmitFinalVerdict0',
    ],
    coreDigestField: 'CoreDigest',
    packDigestField: 'PackDigest',
    acceptsOnlyAfterReplay: true,
  };

  return {
    ...shell,
    ...overrides,
  };
}

export async function CheckMaterializedPhaseManifest0(shell, config = {}) {
  const checker = 'CheckMaterializedPhaseManifest0';
  const ledger = [];

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

  const extraction = await ExtractMaterializedCore0(shell, {
    checkShell: false,
    requireCoreBoundary: true,
    ...(config.extractorConfig ?? {}),
  });
  const extractionResult = recordToValidation0(extraction, ['Shell']);

  ledger.push({
    phase: 'ExtractMaterializedCore0',
    status: extractionResult.ok ? 'pass' : 'fail',
    digest: extraction.Digest ?? extraction.digest ?? digestCanonical0(extraction),
  });

  if (!extractionResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.extract`,
      path: extractionResult.path,
      witness: extractionResult.witness,
      ledger,
    });
  }

  const packObject = extraction.PackObject;
  const coreObject = extraction.CoreObject;
  const manifest = packObject.Manifest;

  const shape = validateManifestShape0(manifest);

  ledger.push({
    phase: 'manifestShape',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.manifest`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const phaseOrder = validateManifestPhaseOrder0(manifest);

  ledger.push({
    phase: 'phaseOrder',
    status: phaseOrder.ok ? 'pass' : 'fail',
    digest: digestCanonical0(phaseOrder.nf ?? phaseOrder.witness ?? null),
  });

  if (!phaseOrder.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.phaseOrder`,
      path: phaseOrder.path,
      witness: phaseOrder.witness,
      ledger,
    });
  }

  const artefacts = validateManifestRequiredArtefacts0(manifest);

  ledger.push({
    phase: 'requiredArtefacts',
    status: artefacts.ok ? 'pass' : 'fail',
    digest: digestCanonical0(artefacts.nf ?? artefacts.witness ?? null),
  });

  if (!artefacts.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.requiredArtefacts`,
      path: artefacts.path,
      witness: artefacts.witness,
      ledger,
    });
  }

  const digestLinks = validateManifestDigestLinks0(shell, manifest);

  ledger.push({
    phase: 'digestLinks',
    status: digestLinks.ok ? 'pass' : 'fail',
    digest: digestCanonical0(digestLinks.nf ?? digestLinks.witness ?? null),
  });

  if (!digestLinks.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.digestLinks`,
      path: digestLinks.path,
      witness: digestLinks.witness,
      ledger,
    });
  }

  const coreBoundary = validateManifestCoreBoundary0(manifest, coreObject, packObject);

  ledger.push({
    phase: 'coreBoundary',
    status: coreBoundary.ok ? 'pass' : 'fail',
    digest: digestCanonical0(coreBoundary.nf ?? coreBoundary.witness ?? null),
  });

  if (!coreBoundary.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.coreBoundary`,
      path: coreBoundary.path,
      witness: coreBoundary.witness,
      ledger,
    });
  }

  const policy = validateManifestCanonicalPolicy0(manifest);

  ledger.push({
    phase: 'canonicalBytePolicy',
    status: policy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
  });

  if (!policy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.canonicalBytePolicy`,
      path: policy.path,
      witness: policy.witness,
      ledger,
    });
  }

  const publicClaim = validateManifestPublicClaimBoundary0(manifest);

  ledger.push({
    phase: 'publicClaimBoundary',
    status: publicClaim.ok ? 'pass' : 'fail',
    digest: digestCanonical0(publicClaim.nf ?? publicClaim.witness ?? null),
  });

  if (!publicClaim.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.publicClaimBoundary`,
      path: publicClaim.path,
      witness: publicClaim.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedPhaseManifest0NF',
    checker,
    version: CHECKER_VERSION,
    manifestKind: manifest.kind,
    manifestChecker: manifest.checker,
    phaseCount: manifest.phaseOrder.length,
    artefactCount: manifest.requiredArtefacts.length,
    coreDigest: manifest.coreDigest,
    coreBytesDigest: manifest.coreBytesDigest,
    manifestDigest: digestCanonical0(manifest),
    packDigest: shell.PackDigest,
    publicClaimBoundary: manifest.publicClaimBoundary,
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    Manifest: manifest,
    CoreObject: coreObject,
    PackObject: packObject,
    manifest,
    coreObject,
    packObject,
  };
}

export async function CheckMaterializedPhaseManifestFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedPhaseManifestFile0';
  const ledger = [];

  const loaded = await LoadMaterializedPCCPackShellFile0(filePath, config.loaderConfig ?? {});
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

  const checked = await CheckMaterializedPhaseManifest0(loaded.Shell, config);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedPhaseManifest0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.manifest`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedPhaseManifestFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    phaseManifestDigest: checked.NF.manifestDigest,
    phaseCount: checked.NF.phaseCount,
    artefactCount: checked.NF.artefactCount,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateManifestShape0(manifest) {
  if (!isPlainObject(manifest)) {
    return validationReject0(['PackBytes', 'Manifest'], 'Pack.Manifest must be an object', {
      actual: typeof manifest,
    });
  }

  for (const field of MATERIALIZED_PHASE_MANIFEST_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(manifest, field)) {
      return validationReject0(['PackBytes', 'Manifest', field], 'Pack.Manifest is missing a required field', {
        field,
      });
    }
  }

  if (manifest.kind !== MATERIALIZED_PHASE_MANIFEST_KIND0) {
    return validationReject0(['PackBytes', 'Manifest', 'kind'], 'Pack.Manifest kind mismatch', {
      expected: MATERIALIZED_PHASE_MANIFEST_KIND0,
      actual: manifest.kind,
    });
  }

  if (manifest.version !== CHECKER_VERSION) {
    return validationReject0(['PackBytes', 'Manifest', 'version'], `Pack.Manifest version must be ${CHECKER_VERSION}`, {
      actual: manifest.version,
    });
  }

  if (manifest.checker !== 'CheckPCCPackexp') {
    return validationReject0(['PackBytes', 'Manifest', 'checker'], 'Pack.Manifest checker must be CheckPCCPackexp', {
      actual: manifest.checker,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPhaseManifestShape0NF',
  });
}

function validateManifestPhaseOrder0(manifest) {
  if (!Array.isArray(manifest.phaseOrder)) {
    return validationReject0(['PackBytes', 'Manifest', 'phaseOrder'], 'Pack.Manifest phaseOrder must be an array', {
      actual: typeof manifest.phaseOrder,
    });
  }

  if (manifest.phaseOrder.length !== ACCEPT_RUN_PHASES0.length) {
    return validationReject0(['PackBytes', 'Manifest', 'phaseOrder'], 'Pack.Manifest phaseOrder length mismatch', {
      expected: ACCEPT_RUN_PHASES0.length,
      actual: manifest.phaseOrder.length,
    });
  }

  for (let index = 0; index < ACCEPT_RUN_PHASES0.length; index += 1) {
    if (manifest.phaseOrder[index] !== ACCEPT_RUN_PHASES0[index]) {
      return validationReject0(['PackBytes', 'Manifest', 'phaseOrder', index], 'Pack.Manifest phaseOrder mismatch', {
        expected: ACCEPT_RUN_PHASES0[index],
        actual: manifest.phaseOrder[index],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedPhaseOrder0NF',
    phaseCount: manifest.phaseOrder.length,
  });
}

function validateManifestRequiredArtefacts0(manifest) {
  if (!Array.isArray(manifest.requiredArtefacts)) {
    return validationReject0(['PackBytes', 'Manifest', 'requiredArtefacts'], 'Pack.Manifest requiredArtefacts must be an array', {
      actual: typeof manifest.requiredArtefacts,
    });
  }

  for (const artefact of PCCPACK_REQUIRED_FIELDS0) {
    if (!manifest.requiredArtefacts.includes(artefact)) {
      return validationReject0(['PackBytes', 'Manifest', 'requiredArtefacts', artefact], 'Pack.Manifest is missing a required package artefact', {
        artefact,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedRequiredArtefacts0NF',
    artefactCount: manifest.requiredArtefacts.length,
  });
}

function validateManifestDigestLinks0(shell, manifest) {
  if (!sameDigestRecord0(manifest.coreDigest, shell.CoreDigest)) {
    return validationReject0(['PackBytes', 'Manifest', 'coreDigest'], 'Pack.Manifest coreDigest must match envelope CoreDigest', {
      expected: shell.CoreDigest,
      actual: manifest.coreDigest,
    });
  }

  const expectedCoreBytesDigest = sha256Utf8DigestRecord0(shell.CoreBytes);

  if (!sameDigestRecord0(manifest.coreBytesDigest, expectedCoreBytesDigest)) {
    return validationReject0(['PackBytes', 'Manifest', 'coreBytesDigest'], 'Pack.Manifest coreBytesDigest must be SHA256 over CoreBytes', {
      expected: expectedCoreBytesDigest,
      actual: manifest.coreBytesDigest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedManifestDigestLinks0NF',
    coreDigest: manifest.coreDigest,
    coreBytesDigest: manifest.coreBytesDigest,
  });
}

function validateManifestCoreBoundary0(manifest, coreObject, packObject) {
  if (manifest.coreExcludesAcceptRun !== true) {
    return validationReject0(['PackBytes', 'Manifest', 'coreExcludesAcceptRun'], 'Pack.Manifest must certify that Core excludes AcceptRun', {
      actual: manifest.coreExcludesAcceptRun,
    });
  }

  if (manifest.acceptRunLocation !== 'outside-core') {
    return validationReject0(['PackBytes', 'Manifest', 'acceptRunLocation'], 'Pack.Manifest acceptRunLocation must be outside-core', {
      actual: manifest.acceptRunLocation,
    });
  }

  if (containsAcceptRun0(coreObject)) {
    return validationReject0(['CoreBytes'], 'CoreBytes must not contain AcceptRun', null);
  }

  if (containsAcceptRun0(packObject.Core)) {
    return validationReject0(['PackBytes', 'Core'], 'Pack.Core must not contain AcceptRun', null);
  }

  return validationAccept0({
    kind: 'MaterializedManifestCoreBoundary0NF',
  });
}

function validateManifestCanonicalPolicy0(manifest) {
  const policy = manifest.canonicalBytePolicy;

  if (!isPlainObject(policy)) {
    return validationReject0(['PackBytes', 'Manifest', 'canonicalBytePolicy'], 'Pack.Manifest canonicalBytePolicy must be an object', {
      actual: typeof policy,
    });
  }

  for (const field of [
    'canonicalJson',
    'fullBytesCompared',
    'digestEqualityIsNotObjectEquality',
    'materializedOutputOnly',
    'generatorUntrusted',
  ]) {
    if (policy[field] !== true) {
      return validationReject0(['PackBytes', 'Manifest', 'canonicalBytePolicy', field], `Pack.Manifest canonicalBytePolicy must certify ${field}`, {
        actual: policy[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedManifestCanonicalBytePolicy0NF',
  });
}

function validateManifestPublicClaimBoundary0(manifest) {
  const boundary = manifest.publicClaimBoundary;

  if (!isPlainObject(boundary)) {
    return validationReject0(['PackBytes', 'Manifest', 'publicClaimBoundary'], 'Pack.Manifest publicClaimBoundary must be an object', {
      actual: typeof boundary,
    });
  }

  if (boundary.antecedent !== MATERIALIZED_PACK_PUBLIC_BOUNDARY0.antecedent) {
    return validationReject0(['PackBytes', 'Manifest', 'publicClaimBoundary', 'antecedent'], 'Pack.Manifest public claim antecedent mismatch', {
      expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0.antecedent,
      actual: boundary.antecedent,
    });
  }

  if (boundary.consequent !== MATERIALIZED_PACK_PUBLIC_BOUNDARY0.consequent) {
    return validationReject0(['PackBytes', 'Manifest', 'publicClaimBoundary', 'consequent'], 'Pack.Manifest public claim consequent mismatch', {
      expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0.consequent,
      actual: boundary.consequent,
    });
  }

  if (boundary.conditional !== true) {
    return validationReject0(['PackBytes', 'Manifest', 'publicClaimBoundary', 'conditional'], 'Pack.Manifest public claim boundary must be conditional', {
      actual: boundary.conditional,
    });
  }

  return validationAccept0({
    kind: 'MaterializedManifestPublicClaimBoundary0NF',
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