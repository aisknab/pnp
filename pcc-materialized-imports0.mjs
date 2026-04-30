import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  CheckMaterializedNoHiddenMin0,
  makeMaterializedNoHiddenMinShell0,
} from './pcc-materialized-no-hidden-min0.mjs';

import {
  sha256Utf8DigestRecord0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_IMPORT_FORBIDDEN_EDGES0 = Object.freeze([
  Object.freeze(['BC', 'UN']),
  Object.freeze(['UN', 'BC']),
  Object.freeze(['BCEL', 'R']),
  Object.freeze(['BUD', 'R']),
  Object.freeze(['O', 'G']),
  Object.freeze(['G', 'O']),
]);

export const MATERIALIZED_IMPORT_POLICY0 = Object.freeze({
  kind: 'MaterializedImportPolicy0',
  version: CHECKER_VERSION,
  acyclic: true,
  artefactImportsMatchDependencies: true,
  rejectsAcceptRunImports: true,
  rejectsForbiddenEdges: true,
  forbiddenEdges: MATERIALIZED_IMPORT_FORBIDDEN_EDGES0,
});

export function makeMaterializedImportShell0(overrides = {}) {
  const shell = makeMaterializedNoHiddenMinShell0();
  const packObject = JSON.parse(shell.PackBytes);
  const artefactOrder = packObject.Manifest.artefactOrder;

  const artefactImports = {};
  const importEdges = [];

  for (const artefactName of artefactOrder) {
    const deps = packObject.Manifest.artefactDependencies[artefactName] ?? [];

    artefactImports[artefactName] = [...deps];

    for (const dep of deps) {
      importEdges.push({
        from: artefactName,
        to: dep,
        edgeKind: 'ArtefactDependencyImport',
      });
    }

    if (artefactName !== 'Core' && artefactName !== 'Manifest') {
      packObject[artefactName] = {
        ...packObject[artefactName],
        imports: [...deps],
      };
    }
  }

  packObject.Manifest = {
    ...packObject.Manifest,
    importPolicy: {
      ...MATERIALIZED_IMPORT_POLICY0,
    },
    artefactImports,
    importEdges,
    packageImportEdges: [],
  };

  shell.PackBytes = stableStringify0(packObject);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  return {
    ...shell,
    ...overrides,
  };
}

export async function CheckMaterializedImports0(shell, config = {}) {
  const checker = 'CheckMaterializedImports0';
  const ledger = [];

  const noMinRecord = await CheckMaterializedNoHiddenMin0(shell, config.noHiddenMinConfig ?? {});
  const noMin = recordToValidation0(noMinRecord, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedNoHiddenMin0',
    status: noMin.ok ? 'pass' : 'fail',
    digest: noMinRecord.Digest ?? noMinRecord.digest ?? digestCanonical0(noMinRecord),
  });

  if (!noMin.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.noHiddenMin`,
      path: noMin.path,
      witness: noMin.witness,
      ledger,
    });
  }

  const manifest = noMinRecord.Manifest;
  const packObject = noMinRecord.PackObject;

  const policy = validateImportPolicy0(manifest);

  ledger.push({
    phase: 'importPolicy',
    status: policy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
  });

  if (!policy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.importPolicy`,
      path: policy.path,
      witness: policy.witness,
      ledger,
    });
  }

  const artefactImports = validateArtefactImports0(manifest);

  ledger.push({
    phase: 'artefactImports',
    status: artefactImports.ok ? 'pass' : 'fail',
    digest: digestCanonical0(artefactImports.nf ?? artefactImports.witness ?? null),
  });

  if (!artefactImports.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.artefactImports`,
      path: artefactImports.path,
      witness: artefactImports.witness,
      ledger,
    });
  }

  const edges = validateArtefactImportEdges0(manifest);

  ledger.push({
    phase: 'artefactImportEdges',
    status: edges.ok ? 'pass' : 'fail',
    digest: digestCanonical0(edges.nf ?? edges.witness ?? null),
  });

  if (!edges.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.artefactImportEdges`,
      path: edges.path,
      witness: edges.witness,
      ledger,
    });
  }

  const declarations = validateDeclaredArtefactImports0(packObject, manifest);

  ledger.push({
    phase: 'declaredArtefactImports',
    status: declarations.ok ? 'pass' : 'fail',
    digest: digestCanonical0(declarations.nf ?? declarations.witness ?? null),
  });

  if (!declarations.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.declaredArtefactImports`,
      path: declarations.path,
      witness: declarations.witness,
      ledger,
    });
  }

  const manifestEdges = validateManifestImportEdges0(manifest);

  ledger.push({
    phase: 'manifestImportEdges',
    status: manifestEdges.ok ? 'pass' : 'fail',
    digest: digestCanonical0(manifestEdges.nf ?? manifestEdges.witness ?? null),
  });

  if (!manifestEdges.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.manifestImportEdges`,
      path: manifestEdges.path,
      witness: manifestEdges.witness,
      ledger,
    });
  }

  const packageEdges = validatePackageImportEdges0(manifest);

  ledger.push({
    phase: 'packageImportEdges',
    status: packageEdges.ok ? 'pass' : 'fail',
    digest: digestCanonical0(packageEdges.nf ?? packageEdges.witness ?? null),
  });

  if (!packageEdges.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.packageImportEdges`,
      path: packageEdges.path,
      witness: packageEdges.witness,
      ledger,
    });
  }

  const acyclic = validateImportAcyclicity0(manifest);

  ledger.push({
    phase: 'acyclicity',
    status: acyclic.ok ? 'pass' : 'fail',
    digest: digestCanonical0(acyclic.nf ?? acyclic.witness ?? null),
  });

  if (!acyclic.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.acyclicity`,
      path: acyclic.path,
      witness: acyclic.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedImports0NF',
    checker,
    version: CHECKER_VERSION,
    artefactCount: manifest.artefactOrder.length,
    artefactImportCount: artefactImportCount0(manifest),
    manifestImportEdgeCount: manifest.importEdges.length,
    packageImportEdgeCount: manifest.packageImportEdges.length,
    forbiddenEdges: MATERIALIZED_IMPORT_FORBIDDEN_EDGES0,
    importDigest: digestCanonical0({
      artefactImports: manifest.artefactImports,
      importEdges: manifest.importEdges,
      packageImportEdges: manifest.packageImportEdges,
    }),
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

export async function CheckMaterializedImportsFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedImportsFile0';
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

  const checked = await CheckMaterializedImports0(loaded.Shell, config);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedImports0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.imports`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedImportsFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    importDigest: checked.Digest ?? checked.digest,
    artefactImportCount: checked.NF.artefactImportCount,
    packageImportEdgeCount: checked.NF.packageImportEdgeCount,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateImportPolicy0(manifest) {
  const policy = manifest.importPolicy;

  if (!isPlainObject(policy)) {
    return validationReject0(['PackBytes', 'Manifest', 'importPolicy'], 'Pack.Manifest importPolicy must be an object', {
      actual: typeof policy,
    });
  }

  if (policy.kind !== 'MaterializedImportPolicy0') {
    return validationReject0(['PackBytes', 'Manifest', 'importPolicy', 'kind'], 'importPolicy kind mismatch', {
      actual: policy.kind,
    });
  }

  if (policy.version !== CHECKER_VERSION) {
    return validationReject0(['PackBytes', 'Manifest', 'importPolicy', 'version'], `importPolicy version must be ${CHECKER_VERSION}`, {
      actual: policy.version,
    });
  }

  for (const field of [
    'acyclic',
    'artefactImportsMatchDependencies',
    'rejectsAcceptRunImports',
    'rejectsForbiddenEdges',
  ]) {
    if (policy[field] !== true) {
      return validationReject0(['PackBytes', 'Manifest', 'importPolicy', field], `importPolicy must certify ${field}`, {
        actual: policy[field],
      });
    }
  }

  if (!Array.isArray(policy.forbiddenEdges)) {
    return validationReject0(['PackBytes', 'Manifest', 'importPolicy', 'forbiddenEdges'], 'importPolicy forbiddenEdges must be an array', {
      actual: typeof policy.forbiddenEdges,
    });
  }

  for (const edge of MATERIALIZED_IMPORT_FORBIDDEN_EDGES0) {
    if (!policy.forbiddenEdges.some((actual) => edgeKey0(actual) === edgeKey0(edge))) {
      return validationReject0(['PackBytes', 'Manifest', 'importPolicy', 'forbiddenEdges'], 'importPolicy is missing a forbidden edge', {
        edge,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedImportPolicy0NF',
  });
}

function validateArtefactImports0(manifest) {
  if (!isPlainObject(manifest.artefactImports)) {
    return validationReject0(['PackBytes', 'Manifest', 'artefactImports'], 'Pack.Manifest artefactImports must be an object', {
      actual: typeof manifest.artefactImports,
    });
  }

  for (const artefactName of manifest.artefactOrder) {
    if (!Object.prototype.hasOwnProperty.call(manifest.artefactImports, artefactName)) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName], 'Pack.Manifest artefactImports is missing an artefact key', {
        artefactName,
      });
    }

    if (!Array.isArray(manifest.artefactImports[artefactName])) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName], 'artefact import list must be an array', {
        artefactName,
        actual: typeof manifest.artefactImports[artefactName],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedArtefactImportsShape0NF',
  });
}

function validateArtefactImportEdges0(manifest) {
  const orderIndex = new Map(manifest.artefactOrder.map((artefactName, index) => [artefactName, index]));
  const forbidden = new Set(MATERIALIZED_IMPORT_FORBIDDEN_EDGES0.map((edge) => edgeKey0(edge)));

  for (const artefactName of manifest.artefactOrder) {
    const imports = manifest.artefactImports[artefactName];
    const seen = new Set();

    for (let index = 0; index < imports.length; index += 1) {
      const target = imports[index];

      if (typeof target !== 'string' || target.length === 0) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName, index], 'artefact import target must be a non-empty string', {
          artefactName,
          actual: target,
        });
      }

      if (target === 'AcceptRun' || target === 'AcceptRun0') {
        return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName, index], 'artefact import must not target AcceptRun', {
          artefactName,
          target,
        });
      }

      if (forbidden.has(edgeKey0([artefactName, target]))) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName, index], 'artefact import uses a forbidden edge', {
          edge: [artefactName, target],
        });
      }

      if (!orderIndex.has(target)) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName, index], 'artefact import target is unknown', {
          artefactName,
          target,
        });
      }

      if (target === artefactName) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName, index], 'artefact import must not be self-referential', {
          artefactName,
          target,
        });
      }

      if (seen.has(target)) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName, index], 'artefact import list must not contain duplicates', {
          artefactName,
          target,
        });
      }

      seen.add(target);

      if (orderIndex.get(target) >= orderIndex.get(artefactName)) {
        return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName, index], 'artefact import must point to an earlier artefact', {
          artefactName,
          target,
          artefactIndex: orderIndex.get(artefactName),
          targetIndex: orderIndex.get(target),
        });
      }
    }

    const deps = manifest.artefactDependencies[artefactName] ?? [];

    if (stableStringify0(imports) !== stableStringify0(deps)) {
      return validationReject0(['PackBytes', 'Manifest', 'artefactImports', artefactName], 'artefact imports must match artefactDependencies', {
        artefactName,
        expected: deps,
        actual: imports,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedArtefactImportEdges0NF',
    importCount: artefactImportCount0(manifest),
  });
}

function validateDeclaredArtefactImports0(packObject, manifest) {
  for (const artefactName of manifest.artefactOrder) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const artefact = packObject[artefactName];

    if (!isPlainObject(artefact)) {
      return validationReject0(['PackBytes', artefactName], 'materialized artefact must be an object before import checking', {
        artefactName,
        actual: typeof artefact,
      });
    }

    if (!Object.prototype.hasOwnProperty.call(artefact, 'imports')) {
      return validationReject0(['PackBytes', artefactName, 'imports'], 'materialized artefact must declare imports', {
        artefactName,
      });
    }

    if (!Array.isArray(artefact.imports)) {
      return validationReject0(['PackBytes', artefactName, 'imports'], 'materialized artefact imports must be an array', {
        artefactName,
        actual: typeof artefact.imports,
      });
    }

    if (stableStringify0(artefact.imports) !== stableStringify0(manifest.artefactImports[artefactName])) {
      return validationReject0(['PackBytes', artefactName, 'imports'], 'materialized artefact imports must match Pack.Manifest artefactImports', {
        artefactName,
        expected: manifest.artefactImports[artefactName],
        actual: artefact.imports,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedDeclaredArtefactImports0NF',
  });
}

function validateManifestImportEdges0(manifest) {
  if (!Array.isArray(manifest.importEdges)) {
    return validationReject0(['PackBytes', 'Manifest', 'importEdges'], 'Pack.Manifest importEdges must be an array', {
      actual: typeof manifest.importEdges,
    });
  }

  const expected = new Set();

  for (const artefactName of manifest.artefactOrder) {
    for (const target of manifest.artefactImports[artefactName] ?? []) {
      expected.add(edgeKey0([artefactName, target]));
    }
  }

  const actual = new Set();

  for (let index = 0; index < manifest.importEdges.length; index += 1) {
    const edge = normalizeImportEdge0(manifest.importEdges[index]);

    if (edge === null) {
      return validationReject0(['PackBytes', 'Manifest', 'importEdges', index], 'importEdges entry must have from and to endpoints', {
        edge: manifest.importEdges[index],
      });
    }

    actual.add(edgeKey0(edge));

    if (!expected.has(edgeKey0(edge))) {
      return validationReject0(['PackBytes', 'Manifest', 'importEdges', index], 'Pack.Manifest importEdges contains an edge not declared in artefactImports', {
        edge,
      });
    }
  }

  for (const key of expected) {
    if (!actual.has(key)) {
      return validationReject0(['PackBytes', 'Manifest', 'importEdges'], 'Pack.Manifest importEdges is missing an artefact import edge', {
        edge: key,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedManifestImportEdges0NF',
    edgeCount: manifest.importEdges.length,
  });
}

function validatePackageImportEdges0(manifest) {
  if (!Array.isArray(manifest.packageImportEdges)) {
    return validationReject0(['PackBytes', 'Manifest', 'packageImportEdges'], 'Pack.Manifest packageImportEdges must be an array', {
      actual: typeof manifest.packageImportEdges,
    });
  }

  const forbidden = new Set(MATERIALIZED_IMPORT_FORBIDDEN_EDGES0.map((edge) => edgeKey0(edge)));
  const graph = new Map();

  for (let index = 0; index < manifest.packageImportEdges.length; index += 1) {
    const edge = normalizeImportEdge0(manifest.packageImportEdges[index]);

    if (edge === null) {
      return validationReject0(['PackBytes', 'Manifest', 'packageImportEdges', index], 'packageImportEdges entry must have from and to endpoints', {
        edge: manifest.packageImportEdges[index],
      });
    }

    if (!isNonEmptyString0(edge.from) || !isNonEmptyString0(edge.to)) {
      return validationReject0(['PackBytes', 'Manifest', 'packageImportEdges', index], 'package import edge endpoints must be non-empty strings', {
        edge,
      });
    }

    if (edge.from === 'AcceptRun' || edge.from === 'AcceptRun0' || edge.to === 'AcceptRun' || edge.to === 'AcceptRun0') {
      return validationReject0(['PackBytes', 'Manifest', 'packageImportEdges', index], 'package import edge must not mention AcceptRun', {
        edge,
      });
    }

    if (forbidden.has(edgeKey0(edge))) {
      return validationReject0(['PackBytes', 'Manifest', 'packageImportEdges', index], 'package import uses a forbidden edge', {
        edge,
      });
    }

    if (!graph.has(edge.from)) {
      graph.set(edge.from, []);
    }

    if (!graph.has(edge.to)) {
      graph.set(edge.to, []);
    }

    graph.get(edge.from).push(edge.to);
  }

  const cycle = findCycle0(graph);

  if (cycle !== null) {
    return validationReject0(['PackBytes', 'Manifest', 'packageImportEdges'], 'package import graph contains a cycle', {
      cycle,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPackageImportEdges0NF',
    edgeCount: manifest.packageImportEdges.length,
  });
}

function validateImportAcyclicity0(manifest) {
  const graph = new Map();

  for (const artefactName of manifest.artefactOrder) {
    graph.set(artefactName, [...(manifest.artefactImports[artefactName] ?? [])]);
  }

  const cycle = findCycle0(graph);

  if (cycle !== null) {
    return validationReject0(['PackBytes', 'Manifest', 'artefactImports'], 'artefact import graph contains a cycle', {
      cycle,
    });
  }

  return validationAccept0({
    kind: 'MaterializedImportAcyclicity0NF',
  });
}

function normalizeImportEdge0(edge) {
  if (Array.isArray(edge) && edge.length >= 2) {
    return {
      from: String(edge[0]),
      to: String(edge[1]),
    };
  }

  if (isPlainObject(edge)) {
    const from = edge.from ?? edge.src;
    const to = edge.to ?? edge.dst;

    if (from !== undefined && to !== undefined) {
      return {
        from: String(from),
        to: String(to),
      };
    }
  }

  return null;
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

function edgeKey0(edge) {
  if (Array.isArray(edge)) {
    return `${String(edge[0])}->${String(edge[1])}`;
  }

  return `${String(edge.from)}->${String(edge.to)}`;
}

function artefactImportCount0(manifest) {
  let count = 0;

  for (const imports of Object.values(manifest.artefactImports ?? {})) {
    if (Array.isArray(imports)) {
      count += imports.length;
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

function isNonEmptyString0(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}