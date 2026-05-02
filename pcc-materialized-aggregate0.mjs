import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  CheckMaterializedPCCPackShell0,
} from './pcc-materialized-pack0.mjs';

import {
  ExtractMaterializedCore0,
} from './pcc-materialized-core-extractor0.mjs';

import {
  CheckMaterializedPhaseManifest0,
} from './pcc-materialized-phase-manifest0.mjs';

import {
  CheckMaterializedArtefactInventory0,
} from './pcc-materialized-artefact-inventory0.mjs';

import {
  CheckMaterializedArtefactDeps0,
} from './pcc-materialized-artefact-deps0.mjs';

import {
  CheckMaterializedProofRefs0,
} from './pcc-materialized-proof-refs0.mjs';

import {
  CheckMaterializedBounds0,
} from './pcc-materialized-bounds0.mjs';

import {
  CheckMaterializedNoHiddenMin0,
} from './pcc-materialized-no-hidden-min0.mjs';

import {
  CheckMaterializedImports0,
  makeMaterializedImportShell0,
} from './pcc-materialized-imports0.mjs';

import {
  CheckMaterializedCheckPCCPack0,
} from './pcc-materialized-checkpack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_AGGREGATE_PHASES0 = Object.freeze([
  'CheckMaterializedPCCPackShell0',
  'ExtractMaterializedCore0',
  'CheckMaterializedPhaseManifest0',
  'CheckMaterializedArtefactInventory0',
  'CheckMaterializedArtefactDeps0',
  'CheckMaterializedProofRefs0',
  'CheckMaterializedBounds0',
  'CheckMaterializedNoHiddenMin0',
  'CheckMaterializedImports0',
  'CheckMaterializedCheckPCCPack0',
]);

export function makeMaterializedAggregateShell0(overrides = {}) {
  return makeMaterializedImportShell0(overrides);
}

export async function CheckMaterializedAggregate0(shell, config = {}) {
  const checker = 'CheckMaterializedAggregate0';
  const ledger = [];

  const phaseDigests = [];

  const phases = [
    {
      phase: 'CheckMaterializedPCCPackShell0',
      path: ['Shell'],
      run: () => CheckMaterializedPCCPackShell0(shell),
    },
    {
      phase: 'ExtractMaterializedCore0',
      path: ['Shell'],
      run: () => ExtractMaterializedCore0(shell, config.coreExtractorConfig ?? {}),
    },
    {
      phase: 'CheckMaterializedPhaseManifest0',
      path: ['Shell'],
      run: () => CheckMaterializedPhaseManifest0(shell, config.phaseManifestConfig ?? {}),
    },
    {
      phase: 'CheckMaterializedArtefactInventory0',
      path: ['Shell'],
      run: () => CheckMaterializedArtefactInventory0(shell, config.artefactInventoryConfig ?? {}),
    },
    {
      phase: 'CheckMaterializedArtefactDeps0',
      path: ['Shell'],
      run: () => CheckMaterializedArtefactDeps0(shell, config.artefactDepsConfig ?? {}),
    },
    {
      phase: 'CheckMaterializedProofRefs0',
      path: ['Shell'],
      run: () => CheckMaterializedProofRefs0(shell, config.proofRefsConfig ?? {}),
    },
    {
      phase: 'CheckMaterializedBounds0',
      path: ['Shell'],
      run: () => CheckMaterializedBounds0(shell, config.boundsConfig ?? {}),
    },
    {
      phase: 'CheckMaterializedNoHiddenMin0',
      path: ['Shell'],
      run: () => CheckMaterializedNoHiddenMin0(shell, config.noHiddenMinConfig ?? {}),
    },
    {
      phase: 'CheckMaterializedImports0',
      path: ['Shell'],
      run: () => CheckMaterializedImports0(shell, config.importsConfig ?? {}),
    },

    {
      phase: 'CheckMaterializedCheckPCCPack0',
      path: ['Shell'],
      run: () => CheckMaterializedCheckPCCPack0(shell, config.checkPCCPackConfig ?? {}),
    },    
  ];

  let finalRecord = null;

  for (const entry of phases) {
    const record = await entry.run();
    const result = recordToValidation0(record, entry.path);

    ledger.push({
      phase: entry.phase,
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.${entry.phase}`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    phaseDigests.push({
      phase: entry.phase,
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    finalRecord = record;
  }

  const finalNF = finalRecord.NF ?? finalRecord.nf ?? {};

  const nf = {
    kind: 'MaterializedAggregate0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: MATERIALIZED_AGGREGATE_PHASES0,
    phaseCount: MATERIALIZED_AGGREGATE_PHASES0.length,
    phaseDigests,
    packDigest: finalNF.packDigest ?? shell?.PackDigest ?? null,
    manifestDigest: finalNF.manifestDigest ?? null,
    importDigest: finalNF.importDigest ?? null,
    artefactImportCount: finalNF.artefactImportCount ?? null,
    packageImportEdgeCount: finalNF.packageImportEdgeCount ?? null,
    finalPhaseDigest: finalRecord.Digest ?? finalRecord.digest,
    checkPCCPackStatus: finalNF.status ?? null,
    checkPCCPackAccepted: finalNF.accepted ?? false,
    checkPCCPackStrict: finalNF.strict ?? false,
    checkPCCPackDigest: finalRecord.Digest ?? finalRecord.digest,    
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckMaterializedAggregateFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedAggregateFile0';
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

  const checked = await CheckMaterializedAggregate0(loaded.Shell, config);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedAggregate0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.aggregate`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedAggregateFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    aggregateDigest: checked.Digest ?? checked.digest,
    phaseCount: checked.NF.phaseCount,
    packDigest: checked.NF.packDigest,
    checkPCCPackStatus: checked.NF.checkPCCPackStatus,
    checkPCCPackAccepted: checked.NF.checkPCCPackAccepted,    
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
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