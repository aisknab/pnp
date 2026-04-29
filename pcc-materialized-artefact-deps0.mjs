import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  PCCPACK_REQUIRED_FIELDS0,
} from './pcc-pack-sufficiency0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  CheckMaterializedArtefactInventory0,
  makeMaterializedArtefactInventoryShell0,
} from './pcc-materialized-artefact-inventory0.mjs';

import {
  sha256Utf8DigestRecord0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_ARTEFACT_ORDER0 = Object.freeze([
  ...PCCPACK_REQUIRED_FIELDS0,
]);

export const MATERIALIZED_ARTEFACT_DEPENDENCY_DEFAULTS0 = Object.freeze({
  Core: Object.freeze([]),
  Manifest: Object.freeze(['Core']),
  Boot0: Object.freeze(['Core', 'Manifest']),
  KBundle: Object.freeze(['Boot0']),
  HardCheck: Object.freeze(['KBundle']),
  RowPack: Object.freeze(['Boot0', 'KBundle', 'HardCheck']),
  GlobalProofDAG: Object.freeze(['KBundle', 'RowPack']),
  LocalPackages: Object.freeze(['RowPack', 'GlobalProofDAG']),
  GlobalFirewalls: Object.freeze(['LocalPackages']),
  GPack: Object.freeze(['GlobalFirewalls']),
  RowFamG: Object.freeze(['GPack', 'RowPack']),
  FinalIntegration: Object.freeze(['GPack', 'RowFamG']),
  FinalTheorem: Object.freeze(['FinalIntegration']),
  RowFamFinal: Object.freeze(['FinalTheorem']),
  PackSufficiencyTheorem: Object.freeze([
    'RowFamFinal',
    'FinalTheorem',
    'FinalIntegration',
    'GPack',
  ]),
});

export function makeMaterializedArtefactDependencyShell0(overrides = {}) {
  const shell = makeMaterializedArtefactInventoryShell0();
  const packObject = JSON.parse(shell.PackBytes);

  const artefactDependencies = {};

  for (const artefactName of MATERIALIZED_ARTEFACT_ORDER0) {
    const deps = MATERIALIZED_ARTEFACT_DEPENDENCY_DEFAULTS0[artefactName] ?? [];

    artefactDependencies[artefactName] = [...deps];

    if (
      artefactName !== 'Core' &&
      artefactName !== 'Manifest' &&
      isPlainObject(packObject[artefactName])
    ) {
      packObject[artefactName] = {
        ...packObject[artefactName],
        dependencies: [...deps],
      };
    }
  }

  packObject.Manifest = {
    ...packObject.Manifest,
    artefactOrder: [...MATERIALIZED_ARTEFACT_ORDER0],
    artefactDependencies,
  };

  shell.PackBytes = stableStringify0(packObject);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  return {
    ...shell,
    ...overrides,
  };
}

export async function CheckMaterializedArtefactDeps0(shell, config = {}) {
  const checker = 'CheckMaterializedArtefactDeps0';
  const ledger = [];

  const inventoryRecord = await CheckMaterializedArtefactInventory0(
    shell,
    config.inventoryConfig ?? {},
  );
  const inventory = recordToValidation0(inventoryRecord, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedArtefactInventory0',
    status: inventory.ok ? 'pass' : 'fail',
    digest: inventoryRecord.Digest ?? inventoryRecord.digest ?? digestCanonical0(inventoryRecord),
  });

  if (!inventory.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.inventory`,
      path: inventory.path,
      witness: inventory.witness,
      ledger,
    });
  }

  const packObject = inventoryRecord.PackObject;
  const manifest = inventoryRecord.Manifest;

  const order = validateArtefactOrder0(manifest);

  ledger.push({
    phase: 'artefactOrder',
    status: order.ok ? 'pass' : 'fail',
    digest: digestCanonical0(order.nf ?? order.witness ?? null),
  });

  if (!order.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.artefactOrder`,
      path: order.path,
      witness: order.witness,
      ledger,
    });
  }

  const dependencyShape = validateDependencyShape0(manifest);

  ledger.push({
    phase: 'dependencyShape',
    status: dependencyShape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(dependencyShape.nf ?? dependencyShape.witness ?? null),
  });

  if (!dependencyShape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.dependencyShape`,
      path: dependencyShape.path,
      witness: dependencyShape.witness,
      ledger,
    });
  }

  const dependencies = validateDependencyEdges0(manifest);

  ledger.push({
    phase: 'dependencyEdges',
    status: dependencies.ok ? 'pass' : 'fail',
    digest: digestCanonical0(dependencies.nf ?? dependencies.witness ?? null),
  });

  if (!dependencies.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.dependencyEdges`,
      path: dependencies.path,
      witness: dependencies.witness,
      ledger,
    });
  }

  const declared = validateDeclaredArtefactDependencies0(packObject, manifest);

  ledger.push({
    phase: 'declaredArtefactDependencies',
    status: declared.ok ? 'pass' : 'fail',
    digest: digestCanonical0(declared.nf ?? declared.witness ?? null),
  });

  if (!declared.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.declaredArtefactDependencies`,
      path: declared.path,
      witness: declared.witness,
      ledger,
    });
  }

  const cycle = validateDependencyAcyclicity0(manifest);

  ledger.push({
    phase: 'acyclicity',
    status: cycle.ok ? 'pass' : 'fail',
    digest: digestCanonical0(cycle.nf ?? cycle.witness ?? null),
  });

  if (!cycle.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.acyclicity`,
      path: cycle.path,
      witness: cycle.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedArtefactDeps0NF',
    checker,
    version: CHECKER_VERSION,
    artefactCount: manifest.artefactOrder.length,
    artefactOrder: manifest.artefactOrder,
    dependencyCount: dependencyCount0(manifest.artefactDependencies),
    dependencyDigest: digestCanonical0(manifest.artefactDependencies),
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

export async function CheckMaterializedArtefactDepsFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedArtefactDepsFile0';
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

  const checked = await CheckMaterializedArtefactDeps0(loaded.Shell, config);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedArtefactDeps0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.dependencies`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedArtefactDepsFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    dependencyDigest: checked.NF.dependencyDigest,
    dependencyCount: checked.NF.dependencyCount,
    artefactCount: checked.NF.artefactCount,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateArtefactOrder0(manifest) {
  if (!Array.isArray(manifest.artefactOrder)) {
    return validationReject0(['PackBytes', 'Manifest', 'artefactOrder'], 'Pack.Manifest artefactOrder must be an array', {
      actual: typeof manifest.artefactOrder,
    });
  }

  if (manifest.artefactOrder.length !== manifest.requiredArtefacts.length) {
    return validationReject0(['PackBytes', 'Manifest', 'artefactOrder'], 'Pack.Manifest artefactOrder length mismatch', {
      expected: manifest.requiredArtefacts.length,
      actual: manifest.artefactOrder.length,
    });
  }

  const seen = new Set();

  for (let index = 0; index < manifest.artefactOrder.length; index += 1) {
    const artefactName = manifest.artefactOrder[index];

    if (typeof artefactName !== 'string' || artefactName.length === 0) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactOrder', index], 'artefactOrder entry must be a non-empty string', {
        actual: artefactName,
      });
    }

    if (seen.has(artefactName)) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactOrder', index], 'artefactOrder entries must be unique', {
        artefactName,
      });
    }

    seen.add(artefactName);

    if (!manifest.requiredArtefacts.includes(artefactName)) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactOrder', index], 'artefactOrder entry is not a required artefact', {
        artefactName,
      });
    }

    if (MATERIALIZED_ARTEFACT_ORDER0[index] !== artefactName) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactOrder', index], 'artefactOrder must match the materialized checker order', {
        expected: MATERIALIZED_ARTEFACT_ORDER0[index],
        actual: artefactName,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedArtefactOrder0NF',
    artefactCount: manifest.artefactOrder.length,
  });
}

function validateDependencyShape0(manifest) {
  if (!isPlainObject(manifest.artefactDependencies)) {
    return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies'], 'Pack.Manifest artefactDependencies must be an object', {
      actual: typeof manifest.artefactDependencies,
    });
  }

  for (const key of Object.keys(manifest.artefactDependencies)) {
    if (!manifest.requiredArtefacts.includes(key)) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies', key], 'artefactDependencies contains an unknown artefact key', {
        artefactName: key,
      });
    }
  }

  for (const artefactName of manifest.requiredArtefacts) {
    if (!Object.prototype.hasOwnProperty.call(manifest.artefactDependencies, artefactName)) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies', artefactName], 'artefactDependencies is missing a required artefact key', {
        artefactName,
      });
    }

    if (!Array.isArray(manifest.artefactDependencies[artefactName])) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies', artefactName], 'artefact dependency list must be an array', {
        artefactName,
        actual: typeof manifest.artefactDependencies[artefactName],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedDependencyShape0NF',
  });
}

function validateDependencyEdges0(manifest) {
  const orderIndex = new Map(manifest.artefactOrder.map((artefactName, index) => [artefactName, index]));

  for (const artefactName of manifest.artefactOrder) {
    const deps = manifest.artefactDependencies[artefactName];
    const seenDeps = new Set();

    for (let index = 0; index < deps.length; index += 1) {
      const dep = deps[index];

      if (typeof dep !== 'string' || dep.length === 0) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies', artefactName, index], 'artefact dependency must be a non-empty string', {
          artefactName,
          actual: dep,
        });
      }

      if (dep === 'AcceptRun' || dep === 'AcceptRun0') {
        return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies', artefactName, index], 'artefact dependency must not point to AcceptRun', {
          artefactName,
          dep,
        });
      }

      if (!orderIndex.has(dep)) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies', artefactName, index], 'artefact dependency points to an unknown artefact', {
          artefactName,
          dep,
        });
      }

      if (dep === artefactName) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies', artefactName, index], 'artefact dependency must not be self-referential', {
          artefactName,
          dep,
        });
      }

      if (seenDeps.has(dep)) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies', artefactName, index], 'artefact dependency list must not contain duplicates', {
          artefactName,
          dep,
        });
      }

      seenDeps.add(dep);

      if (orderIndex.get(dep) >= orderIndex.get(artefactName)) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies', artefactName, index], 'artefact dependency must point to an earlier artefact', {
          artefactName,
          dep,
          artefactIndex: orderIndex.get(artefactName),
          dependencyIndex: orderIndex.get(dep),
        });
      }
    }
  }

  return validationAccept0({
    kind: 'MaterializedDependencyEdges0NF',
    dependencyCount: dependencyCount0(manifest.artefactDependencies),
  });
}

function validateDeclaredArtefactDependencies0(packObject, manifest) {
  for (const artefactName of manifest.artefactOrder) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const artefact = packObject[artefactName];

    if (!isPlainObject(artefact)) {
      return validationReject0(['PackBytes', artefactName], 'materialized artefact must be an object before dependency checking', {
        artefactName,
        actual: typeof artefact,
      });
    }

    if (!Object.prototype.hasOwnProperty.call(artefact, 'dependencies')) {
      return validationReject0(['PackBytes', artefactName, 'dependencies'], 'materialized artefact must declare its dependency list', {
        artefactName,
      });
    }

    if (!Array.isArray(artefact.dependencies)) {
      return validationReject0(['PackBytes', artefactName, 'dependencies'], 'materialized artefact dependency list must be an array', {
        artefactName,
        actual: typeof artefact.dependencies,
      });
    }

    if (stableStringify0(artefact.dependencies) !== stableStringify0(manifest.artefactDependencies[artefactName])) {
      return validationReject0(['PackBytes', artefactName, 'dependencies'], 'materialized artefact dependency list must match Pack.Manifest', {
        artefactName,
        expected: manifest.artefactDependencies[artefactName],
        actual: artefact.dependencies,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedDeclaredDependencies0NF',
  });
}

function validateDependencyAcyclicity0(manifest) {
  const graph = new Map();

  for (const artefactName of manifest.artefactOrder) {
    graph.set(artefactName, manifest.artefactDependencies[artefactName]);
  }

  const cycle = findCycle0(graph);

  if (cycle !== null) {
    return validationReject0(['PackBytes', 'Manifest', 'artefactDependencies'], 'artefact dependency graph contains a cycle', {
      cycle,
    });
  }

  return validationAccept0({
    kind: 'MaterializedDependencyAcyclicity0NF',
  });
}

function findCycle0(graph) {
  const visiting = new Set();
  const visited = new Set();

  function dfs(node, path) {
    if (visiting.has(node)) {
      return [...path, node];
    }

    if (visited.has(node)) {
      return null;
    }

    visiting.add(node);

    for (const next of graph.get(node) ?? []) {
      if (!graph.has(next)) {
        continue;
      }

      const hit = dfs(next, [...path, node]);

      if (hit !== null) {
        return hit;
      }
    }

    visiting.delete(node);
    visited.add(node);

    return null;
  }

  for (const node of graph.keys()) {
    const hit = dfs(node, []);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function dependencyCount0(dependencies) {
  let count = 0;

  for (const deps of Object.values(dependencies ?? {})) {
    if (Array.isArray(deps)) {
      count += deps.length;
    }
  }

  return count;
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