import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  CheckMaterializedBounds0,
  makeMaterializedBoundsShell0,
} from './pcc-materialized-bounds0.mjs';

import {
  sha256Utf8DigestRecord0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_NOMIN_EXPANSION_STAGES0 = Object.freeze([
  'macros',
  'aliases',
  'generatedTemplates',
  'imports',
]);

export const MATERIALIZED_NOMIN_OCCURRENCE_CLASSES0 = Object.freeze([
  'DefImport',
  'SoundImport',
  'ExecCall',
  'AssumeOnly',
  'EmitToken',
]);

export const MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0 = Object.freeze([
  'µ',
  'µ*',
  'µ#',
  'Can',
  'argmin',
  'maxG',
  'minimumEquivalent',
  'optimalCircuit',
  'exactMinSearch',
  'canonicalMinimizer',
  'maximizeGain',
]);

export const MATERIALIZED_NOMIN_POLICY0 = Object.freeze({
  kind: 'MaterializedNoHiddenMinPolicy0',
  version: CHECKER_VERSION,
  expansionStages: MATERIALIZED_NOMIN_EXPANSION_STAGES0,
  occurrenceClasses: MATERIALIZED_NOMIN_OCCURRENCE_CLASSES0,
  forbiddenSymbols: MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0,
  executableOnly: true,
  importsScanned: true,
  macrosExpanded: true,
  aliasesExpanded: true,
  generatedTemplatesExpanded: true,
});

const EXECUTABLE_KEYS0 = new Set([
  'exec',
  'execs',
  'execCall',
  'execCalls',
  'call',
  'calls',
  'callee',
  'operator',
  'operation',
  'program',
  'body',
  'macroBody',
  'templateBody',
  'generatedBody',
]);

export function makeMaterializedNoMinScan0({
  artefactName,
  occurrences = [],
  overrides = {},
} = {}) {
  if (typeof artefactName !== 'string' || artefactName.length === 0) {
    throw new TypeError('makeMaterializedNoMinScan0 requires a non-empty artefactName');
  }

  const material = {
    kind: 'MaterializedNoHiddenMinScan0',
    version: CHECKER_VERSION,
    artefactName,
    expansionStages: MATERIALIZED_NOMIN_EXPANSION_STAGES0,
    occurrenceClasses: MATERIALIZED_NOMIN_OCCURRENCE_CLASSES0,
    forbiddenSymbols: MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0,
    importsScanned: true,
    macrosExpanded: true,
    aliasesExpanded: true,
    generatedTemplatesExpanded: true,
    occurrences: [
      {
        identifier: 'finiteIteration',
        occurrenceClass: 'ExecCall',
        source: `${artefactName}.bounded-checker-language`,
      },
      {
        identifier: 'minimumEquivalent',
        expandedIdentifier: 'µ*',
        occurrenceClass: 'AssumeOnly',
        source: `${artefactName}.theorem-statement`,
      },
      ...occurrences,
    ],
    ...overrides,
  };

  return {
    ...material,
    digest: expectedNoMinScanDigest0(material),
  };
}

export function makeMaterializedNoHiddenMinShell0(overrides = {}) {
  const shell = makeMaterializedBoundsShell0();
  const packObject = JSON.parse(shell.PackBytes);
  const artefactOrder = packObject.Manifest.artefactOrder;
  const noMinScans = {};

  for (const artefactName of artefactOrder) {
    const scan = makeMaterializedNoMinScan0({
      artefactName,
    });

    noMinScans[artefactName] = scan;

    if (artefactName !== 'Core' && artefactName !== 'Manifest') {
      packObject[artefactName] = {
        ...packObject[artefactName],
        noMinScan: scan,
      };
    }
  }

  packObject.Manifest = {
    ...packObject.Manifest,
    noMinPolicy: {
      ...MATERIALIZED_NOMIN_POLICY0,
    },
    noMinScans,
  };

  shell.PackBytes = stableStringify0(packObject);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  return {
    ...shell,
    ...overrides,
  };
}

export async function CheckMaterializedNoHiddenMin0(shell, config = {}) {
  const checker = 'CheckMaterializedNoHiddenMin0';
  const ledger = [];

  const boundsRecord = await CheckMaterializedBounds0(shell, config.boundsConfig ?? {});
  const bounds = recordToValidation0(boundsRecord, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedBounds0',
    status: bounds.ok ? 'pass' : 'fail',
    digest: boundsRecord.Digest ?? boundsRecord.digest ?? digestCanonical0(boundsRecord),
  });

  if (!bounds.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.bounds`,
      path: bounds.path,
      witness: bounds.witness,
      ledger,
    });
  }

  const manifest = boundsRecord.Manifest;
  const packObject = boundsRecord.PackObject;

  const policy = validateNoMinPolicy0(manifest);

  ledger.push({
    phase: 'noMinPolicy',
    status: policy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
  });

  if (!policy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.noMinPolicy`,
      path: policy.path,
      witness: policy.witness,
      ledger,
    });
  }

  const manifestScans = validateManifestNoMinScans0(manifest);

  ledger.push({
    phase: 'manifestNoMinScans',
    status: manifestScans.ok ? 'pass' : 'fail',
    digest: digestCanonical0(manifestScans.nf ?? manifestScans.witness ?? null),
  });

  if (!manifestScans.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.manifestNoMinScans`,
      path: manifestScans.path,
      witness: manifestScans.witness,
      ledger,
    });
  }

  const artefactScans = validateArtefactNoMinScans0(packObject, manifest);

  ledger.push({
    phase: 'artefactNoMinScans',
    status: artefactScans.ok ? 'pass' : 'fail',
    digest: digestCanonical0(artefactScans.nf ?? artefactScans.witness ?? null),
  });

  if (!artefactScans.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.artefactNoMinScans`,
      path: artefactScans.path,
      witness: artefactScans.witness,
      ledger,
    });
  }

  const occurrences = validateNoMinOccurrences0(manifest);

  ledger.push({
    phase: 'occurrences',
    status: occurrences.ok ? 'pass' : 'fail',
    digest: digestCanonical0(occurrences.nf ?? occurrences.witness ?? null),
  });

  if (!occurrences.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.occurrences`,
      path: occurrences.path,
      witness: occurrences.witness,
      ledger,
    });
  }

  const executableScan = validateNoHiddenExecutableUse0(packObject, ['PackBytes']);

  ledger.push({
    phase: 'executableScan',
    status: executableScan.ok ? 'pass' : 'fail',
    digest: digestCanonical0(executableScan.nf ?? executableScan.witness ?? null),
  });

  if (!executableScan.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.executableScan`,
      path: executableScan.path,
      witness: executableScan.witness,
      ledger,
    });
  }

  const digests = validateNoMinScanDigests0(packObject, manifest);

  ledger.push({
    phase: 'scanDigests',
    status: digests.ok ? 'pass' : 'fail',
    digest: digestCanonical0(digests.nf ?? digests.witness ?? null),
  });

  if (!digests.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.scanDigests`,
      path: digests.path,
      witness: digests.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedNoHiddenMin0NF',
    checker,
    version: CHECKER_VERSION,
    artefactCount: manifest.artefactOrder.length,
    occurrenceCount: occurrenceCount0(manifest),
    forbiddenSymbols: MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0,
    expansionStages: MATERIALIZED_NOMIN_EXPANSION_STAGES0,
    noMinDigest: digestCanonical0(manifest.noMinScans),
    manifestDigest: digestCanonical0(manifest),
    packDigest: shell.PackDigest,
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    Manifest: manifest,
    PackObject: packObject,
    manifest,
    packObject,
  };
}

export async function CheckMaterializedNoHiddenMinFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedNoHiddenMinFile0';
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

  const checked = await CheckMaterializedNoHiddenMin0(loaded.Shell, config);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedNoHiddenMin0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.noHiddenMin`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedNoHiddenMinFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    noHiddenMinDigest: checked.Digest ?? checked.digest,
    artefactCount: checked.NF.artefactCount,
    occurrenceCount: checked.NF.occurrenceCount,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateNoMinPolicy0(manifest) {
  const policy = manifest.noMinPolicy;

  if (!isPlainObject(policy)) {
    return validationReject0(['PackBytes', 'Manifest', 'noMinPolicy'], 'Pack.Manifest noMinPolicy must be an object', {
      actual: typeof policy,
    });
  }

  if (policy.kind !== 'MaterializedNoHiddenMinPolicy0') {
    return validationReject0(['PackBytes', 'Manifest', 'noMinPolicy', 'kind'], 'noMinPolicy kind mismatch', {
      actual: policy.kind,
    });
  }

  if (policy.version !== CHECKER_VERSION) {
    return validationReject0(['PackBytes', 'Manifest', 'noMinPolicy', 'version'], `noMinPolicy version must be ${CHECKER_VERSION}`, {
      actual: policy.version,
    });
  }

  if (!arrayContainsAll0(policy.expansionStages, MATERIALIZED_NOMIN_EXPANSION_STAGES0)) {
    return validationReject0(['PackBytes', 'Manifest', 'noMinPolicy', 'expansionStages'], 'noMinPolicy must include every expansion stage', {
      expected: MATERIALIZED_NOMIN_EXPANSION_STAGES0,
      actual: policy.expansionStages,
    });
  }

  if (!arrayContainsAll0(policy.occurrenceClasses, MATERIALIZED_NOMIN_OCCURRENCE_CLASSES0)) {
    return validationReject0(['PackBytes', 'Manifest', 'noMinPolicy', 'occurrenceClasses'], 'noMinPolicy must include every occurrence class', {
      expected: MATERIALIZED_NOMIN_OCCURRENCE_CLASSES0,
      actual: policy.occurrenceClasses,
    });
  }

  if (!arrayContainsAll0(policy.forbiddenSymbols, MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0)) {
    return validationReject0(['PackBytes', 'Manifest', 'noMinPolicy', 'forbiddenSymbols'], 'noMinPolicy must include every forbidden symbol and alias', {
      expected: MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0,
      actual: policy.forbiddenSymbols,
    });
  }

  for (const field of [
    'executableOnly',
    'importsScanned',
    'macrosExpanded',
    'aliasesExpanded',
    'generatedTemplatesExpanded',
  ]) {
    if (policy[field] !== true) {
      return validationReject0(['PackBytes', 'Manifest', 'noMinPolicy', field], `noMinPolicy must certify ${field}`, {
        actual: policy[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedNoMinPolicy0NF',
  });
}

function validateManifestNoMinScans0(manifest) {
  if (!isPlainObject(manifest.noMinScans)) {
    return validationReject0(['PackBytes', 'Manifest', 'noMinScans'], 'Pack.Manifest noMinScans must be an object', {
      actual: typeof manifest.noMinScans,
    });
  }

  for (const artefactName of manifest.artefactOrder) {
    if (!Object.prototype.hasOwnProperty.call(manifest.noMinScans, artefactName)) {
      return validationReject0(['PackBytes', 'Manifest', 'noMinScans', artefactName], 'Pack.Manifest noMinScans is missing an artefact scan', {
        artefactName,
      });
    }

    const result = validateSingleNoMinScan0(
      manifest.noMinScans[artefactName],
      ['PackBytes', 'Manifest', 'noMinScans', artefactName],
      artefactName,
    );

    if (!result.ok) {
      return result;
    }
  }

  return validationAccept0({
    kind: 'MaterializedManifestNoMinScans0NF',
    artefactCount: manifest.artefactOrder.length,
  });
}

function validateArtefactNoMinScans0(packObject, manifest) {
  for (const artefactName of manifest.artefactOrder) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const artefact = packObject[artefactName];

    if (!isPlainObject(artefact)) {
      return validationReject0(['PackBytes', artefactName], 'materialized artefact must be an object before no-min checking', {
        artefactName,
        actual: typeof artefact,
      });
    }

    if (!Object.prototype.hasOwnProperty.call(artefact, 'noMinScan')) {
      return validationReject0(['PackBytes', artefactName, 'noMinScan'], 'materialized artefact must declare noMinScan', {
        artefactName,
      });
    }

    const result = validateSingleNoMinScan0(
      artefact.noMinScan,
      ['PackBytes', artefactName, 'noMinScan'],
      artefactName,
    );

    if (!result.ok) {
      return result;
    }

    if (stableStringify0(artefact.noMinScan) !== stableStringify0(manifest.noMinScans[artefactName])) {
      return validationReject0(['PackBytes', artefactName, 'noMinScan'], 'materialized artefact noMinScan must match Pack.Manifest noMinScans', {
        artefactName,
        expected: manifest.noMinScans[artefactName],
        actual: artefact.noMinScan,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedArtefactNoMinScans0NF',
  });
}

function validateSingleNoMinScan0(scan, path, artefactName) {
  if (!isPlainObject(scan)) {
    return validationReject0(path, 'materialized no-min scan must be an object', {
      artefactName,
      actual: typeof scan,
    });
  }

  if (scan.kind !== 'MaterializedNoHiddenMinScan0') {
    return validationReject0([...path, 'kind'], 'materialized no-min scan kind mismatch', {
      artefactName,
      actual: scan.kind,
    });
  }

  if (scan.version !== CHECKER_VERSION) {
    return validationReject0([...path, 'version'], `materialized no-min scan version must be ${CHECKER_VERSION}`, {
      artefactName,
      actual: scan.version,
    });
  }

  if (scan.artefactName !== artefactName) {
    return validationReject0([...path, 'artefactName'], 'materialized no-min scan artefactName mismatch', {
      expected: artefactName,
      actual: scan.artefactName,
    });
  }

  if (!arrayContainsAll0(scan.expansionStages, MATERIALIZED_NOMIN_EXPANSION_STAGES0)) {
    return validationReject0([...path, 'expansionStages'], 'materialized no-min scan must include every expansion stage', {
      artefactName,
      expected: MATERIALIZED_NOMIN_EXPANSION_STAGES0,
      actual: scan.expansionStages,
    });
  }

  if (!arrayContainsAll0(scan.occurrenceClasses, MATERIALIZED_NOMIN_OCCURRENCE_CLASSES0)) {
    return validationReject0([...path, 'occurrenceClasses'], 'materialized no-min scan must include every occurrence class', {
      artefactName,
      expected: MATERIALIZED_NOMIN_OCCURRENCE_CLASSES0,
      actual: scan.occurrenceClasses,
    });
  }

  if (!arrayContainsAll0(scan.forbiddenSymbols, MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0)) {
    return validationReject0([...path, 'forbiddenSymbols'], 'materialized no-min scan must include every forbidden symbol and alias', {
      artefactName,
      expected: MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0,
      actual: scan.forbiddenSymbols,
    });
  }

  for (const field of [
    'importsScanned',
    'macrosExpanded',
    'aliasesExpanded',
    'generatedTemplatesExpanded',
  ]) {
    if (scan[field] !== true) {
      return validationReject0([...path, field], `materialized no-min scan must certify ${field}`, {
        artefactName,
        actual: scan[field],
      });
    }
  }

  if (!Array.isArray(scan.occurrences)) {
    return validationReject0([...path, 'occurrences'], 'materialized no-min scan occurrences must be an array', {
      artefactName,
      actual: typeof scan.occurrences,
    });
  }

  if (!isDigestRecord0(scan.digest)) {
    return validationReject0([...path, 'digest'], 'materialized no-min scan digest must be a concrete SHA256 digest record', {
      artefactName,
      actual: scan.digest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedSingleNoMinScan0NF',
  });
}

function validateNoMinOccurrences0(manifest) {
  for (const artefactName of manifest.artefactOrder) {
    const scan = manifest.noMinScans[artefactName];

    for (let index = 0; index < scan.occurrences.length; index += 1) {
      const occurrence = scan.occurrences[index];

      if (!isPlainObject(occurrence)) {
        return validationReject0(['PackBytes', 'Manifest', 'noMinScans', artefactName, 'occurrences', index], 'no-min occurrence must be an object', {
          artefactName,
          actual: typeof occurrence,
        });
      }

      if (typeof occurrence.identifier !== 'string' || occurrence.identifier.length === 0) {
        return validationReject0(['PackBytes', 'Manifest', 'noMinScans', artefactName, 'occurrences', index, 'identifier'], 'no-min occurrence identifier must be non-empty', {
          artefactName,
          actual: occurrence.identifier,
        });
      }

      if (!MATERIALIZED_NOMIN_OCCURRENCE_CLASSES0.includes(occurrence.occurrenceClass)) {
        return validationReject0(['PackBytes', 'Manifest', 'noMinScans', artefactName, 'occurrences', index, 'occurrenceClass'], 'no-min occurrence class is not allowed', {
          artefactName,
          actual: occurrence.occurrenceClass,
        });
      }

      const expanded = occurrence.expandedIdentifier ?? occurrence.identifier;

      if (
        occurrence.occurrenceClass === 'ExecCall' &&
        (
          MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0.includes(occurrence.identifier) ||
          MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0.includes(expanded)
        )
      ) {
        return validationReject0(['PackBytes', 'Manifest', 'noMinScans', artefactName, 'occurrences', index, 'identifier'], 'forbidden minimization symbol appears in executable position', {
          artefactName,
          identifier: occurrence.identifier,
          expandedIdentifier: expanded,
        });
      }
    }
  }

  return validationAccept0({
    kind: 'MaterializedNoMinOccurrences0NF',
    occurrenceCount: occurrenceCount0(manifest),
  });
}

function validateNoHiddenExecutableUse0(value, path) {
  const hit = findForbiddenExecutableUse0(value, path, false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'MaterializedNoHiddenExecutableUse0NF',
  });
}

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && MATERIALIZED_NOMIN_FORBIDDEN_SYMBOLS0.includes(value)) {
      return {
        symbol: value,
        path,
      };
    }

    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findForbiddenExecutableUse0(value[index], [...path, index], inExecutablePosition);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const key of Object.keys(value)) {
    const nextExecutablePosition =
      inExecutablePosition ||
      EXECUTABLE_KEYS0.has(key) ||
      /exec|call|program|body|operator|operation/i.test(key);

    const hit = findForbiddenExecutableUse0(value[key], [...path, key], nextExecutablePosition);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function validateNoMinScanDigests0(packObject, manifest) {
  for (const artefactName of manifest.artefactOrder) {
    const manifestScan = manifest.noMinScans[artefactName];
    const manifestExpected = expectedNoMinScanDigest0(manifestScan);

    if (!sameDigestRecord0(manifestScan.digest, manifestExpected)) {
      return validationReject0(['PackBytes', 'Manifest', 'noMinScans', artefactName, 'digest'], 'manifest no-min scan digest mismatch', {
        artefactName,
        expected: manifestExpected,
        actual: manifestScan.digest,
      });
    }

    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const artefactScan = packObject[artefactName].noMinScan;
    const artefactExpected = expectedNoMinScanDigest0(artefactScan);

    if (!sameDigestRecord0(artefactScan.digest, artefactExpected)) {
      return validationReject0(['PackBytes', artefactName, 'noMinScan', 'digest'], 'artefact no-min scan digest mismatch', {
        artefactName,
        expected: artefactExpected,
        actual: artefactScan.digest,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedNoMinScanDigests0NF',
  });
}

function expectedNoMinScanDigest0(scan) {
  const material = {};

  for (const key of Object.keys(scan).sort()) {
    if (key !== 'digest') {
      material[key] = scan[key];
    }
  }

  return sha256Utf8DigestRecord0(stableStringify0(material));
}

function occurrenceCount0(manifest) {
  let count = 0;

  for (const artefactName of manifest.artefactOrder ?? []) {
    const scan = manifest.noMinScans?.[artefactName];

    if (Array.isArray(scan?.occurrences)) {
      count += scan.occurrences.length;
    }
  }

  return count;
}

function isDigestRecord0(value) {
  return (
    isPlainObject(value) &&
    value.alg === 'SHA256' &&
    typeof value.hex === 'string' &&
    /^[0-9a-f]{64}$/.test(value.hex)
  );
}

function sameDigestRecord0(actual, expected) {
  return (
    isPlainObject(actual) &&
    actual.alg === expected.alg &&
    actual.bytes === expected.bytes &&
    actual.hex === expected.hex
  );
}

function arrayContainsAll0(actual, required) {
  if (!Array.isArray(actual)) {
    return false;
  }

  return required.every((entry) => actual.includes(entry));
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