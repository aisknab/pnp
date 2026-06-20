/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: aggregate three cross-package controls: import-graph discipline,
 * expanded no-hidden-minimization scanning, and finite/polynomial bound metadata.
 * Inputs: an ImportGraph, NoHiddenMinScan, Bounds record, and their wrapper pack.
 * Outputs: separate checker records and an aggregate GlobalFirewalls normal form.
 * Invariants enforced: required families, acyclic imports, forbidden dependency
 * edges, token-only BC/UN crossings, declared expansion stages, forbidden executable
 * identifiers, shared public schedule bounds, and absence of opaque proof markers.
 * Assumptions not checked: semantic equivalence of differently named algorithms,
 * completeness of generated-code expansion, mathematical polynomiality of a stated
 * bound, or soundness of package theorems protected by these firewalls.
 * Failure modes: the first structural, import, occurrence, schedule, bound, or
 * opaque-proof defect returns a reject record with the owning subchecker coordinate.
 * Naming: “firewall” means a proof/information-flow boundary, not network security.
 */

import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  LOCAL_PACKAGE_EXPANSION_STAGES0,
  LOCAL_PACKAGE_FORBIDDEN_EXEC_SYMBOLS0,
  LOCAL_PACKAGE_FORBIDDEN_IMPORT_EDGES0,
  LOCAL_PACKAGE_REQUIRED_FAMILIES0,
  LOCAL_PACKAGE_REQUIREMENTS0,
} from './pcc-local-packages0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_FIREWALL_PHASES0 = Object.freeze([
  'CheckImportGraph0',
  'CheckNoHiddenMin0',
  'CheckBounds0',
]);

export const GLOBAL_FIREWALL_CORE_BOUNDS0 = Object.freeze({
  B0: 64,
  K0: 512,
  R0: 64,
  H0: 128,
  O0: 64,
  Rel0: 16,
});

export const GLOBAL_FIREWALL_SELECTOR_BOUNDS0 = Object.freeze({
  bH: 8,
  bTheta: 12,
  selectorPolynomialExponent: 36,
});

export const GLOBAL_FIREWALL_FORBIDDEN_IMPORT_EDGES0 = Object.freeze(
  LOCAL_PACKAGE_FORBIDDEN_IMPORT_EDGES0.map((edge) => Object.freeze([...edge]))
);

export const GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0 = Object.freeze([
  ...LOCAL_PACKAGE_FORBIDDEN_EXEC_SYMBOLS0,
]);

export const GLOBAL_FIREWALL_EXPANSION_STAGES0 = Object.freeze([
  ...LOCAL_PACKAGE_EXPANSION_STAGES0,
]);

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

const GLOBAL_FIREWALL_REQUIRED_FIELDS0 = Object.freeze([
  'SchedHash',
  'IfaceHash',
  'ImportGraph',
  'NoHiddenMinScan',
  'Bounds',
  'PhaseOrder',
]);

export function makeSyntheticImportGraph0(overrides = {}) {
  const edges = [];

  for (const requirement of LOCAL_PACKAGE_REQUIREMENTS0) {
    for (const dep of requirement.defaultImports) {
      edges.push({
        from: requirement.family,
        to: dep,
        kind: 'Import',
        reason: `${requirement.family} imports ${dep}`,
      });
    }
  }

  return {
    kind: 'ImportGraph0',
    version: CHECKER_VERSION,
    families: [...LOCAL_PACKAGE_REQUIRED_FAMILIES0],
    edges,
    forbiddenEdges: GLOBAL_FIREWALL_FORBIDDEN_IMPORT_EDGES0,
    tokenOnlyEdges: [
      {
        from: 'BC',
        to: 'UN',
        token: 'UnaryWindow',
      },
      {
        from: 'UN',
        to: 'BC',
        token: 'BCLeak',
      },
    ],
    acyclic: true,
    ...overrides,
  };
}

export function makeSyntheticNoHiddenMinScan0(overrides = {}) {
  return {
    kind: 'NoHiddenMinScan0',
    version: CHECKER_VERSION,
    expansionStages: GLOBAL_FIREWALL_EXPANSION_STAGES0,
    forbiddenSymbols: GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0,
    occurrenceClasses: [
      'DefImport',
      'SoundImport',
      'ExecCall',
      'AssumeOnly',
      'EmitToken',
    ],
    aliases: {
      minimumEquivalent: 'µ*',
      optimalCircuit: 'µ#',
      exactMinSearch: 'µ',
      canonicalMinimizer: 'Can',
      maximizeGain: 'maxG',
    },
    occurrences: [
      {
        identifier: 'minimumEquivalent',
        expandedIdentifier: 'µ*',
        occurrenceClass: 'AssumeOnly',
        source: 'theorem statement',
      },
      {
        identifier: 'UnaryWindow',
        occurrenceClass: 'EmitToken',
        source: 'BC route token',
      },
      {
        identifier: 'BCLeak',
        occurrenceClass: 'EmitToken',
        source: 'UN route token',
      },
      {
        identifier: 'finiteIteration',
        occurrenceClass: 'ExecCall',
        source: 'bounded checker language',
      },
      {
        identifier: 'topologicalSort',
        occurrenceClass: 'ExecCall',
        source: 'bounded checker language',
      },
    ],
    expandedArtifacts: [],
    importsScanned: true,
    macrosExpanded: true,
    aliasesExpanded: true,
    generatedTemplatesExpanded: true,
    ...overrides,
  };
}

export function makeSyntheticBounds0(overrides = {}) {
  return {
    kind: 'Bounds0',
    version: CHECKER_VERSION,
    core: {
      ...GLOBAL_FIREWALL_CORE_BOUNDS0,
    },
    selector: {
      ...GLOBAL_FIREWALL_SELECTOR_BOUNDS0,
      polynomial: true,
      finite: true,
    },
    families: LOCAL_PACKAGE_REQUIREMENTS0.map((requirement) => {
      const expected = expectedBoundsForFamily0(requirement.family);

      return {
        family: requirement.family,
        packageId: requirement.packageId,
        batchId: requirement.batchId,
        scale: expected.scale,
        k: expected.k,
        beta: expected.beta,
        o: expected.o,
        h: expected.h,
        r: expected.r,
        finite: true,
        polynomial: true,
        privateSchedule: false,
        scheduleHash: 'sched.synthetic',
      };
    }),
    global: {
      finite: true,
      polynomial: true,
      maxExponent: 36,
      noPrivateSchedule: true,
    },
    PiBounds: {
      kind: 'PiBounds0',
      version: CHECKER_VERSION,
      note: 'synthetic global bounds proof marker',
    },
    ...overrides,
  };
}

export function makeSyntheticGlobalFirewalls0(overrides = {}) {
  const pack = {
    kind: 'GlobalFirewalls0',
    version: CHECKER_VERSION,
    SchedHash: {
      alg: 'SHA256',
      hex: '29a492bf0c6cb37f167c59da4ab014bcecb014e333a1503d7b9aac25e613ccc7',
    },
    IfaceHash: {
      alg: 'SHA256',
      hex: 'ed2221f06a028c9b9224cae6abdda43d767f8611a5d236bc7bd0affcb4d317b5',
    },
    ImportGraph: makeSyntheticImportGraph0(),
    NoHiddenMinScan: makeSyntheticNoHiddenMinScan0(),
    Bounds: makeSyntheticBounds0(),
    PhaseOrder: GLOBAL_FIREWALL_PHASES0,
    FirewallLedger: {
      kind: 'FirewallLedger0',
      version: CHECKER_VERSION,
      phases: GLOBAL_FIREWALL_PHASES0,
    },
    PiFirewalls: {
      kind: 'PiFirewalls0',
      version: CHECKER_VERSION,
      note: 'synthetic global firewall proof marker',
    },
  };

  return {
    ...pack,
    ...overrides,
  };
}

/**
 * Validates package dependencies and token-only crossings.
 * Input: ImportGraph0 with families, edges, forbidden edges, and token-only records.
 * Output: accepted graph summary or first structural/dependency reject.
 * Enforces: required families, permitted edges, graph acyclicity, and the explicit
 * BC/UN token-only boundary.
 * Does not check: semantic soundness of imported theorems or hidden dependencies not
 * represented in the supplied/import-scanned graph.
 * Failure modes: malformed family/edge data, forbidden edge, cycle, token violation,
 * or opaque proof marker.
 */
export async function CheckImportGraph0(importGraph) {
  const checker = 'CheckImportGraph0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateImportGraphShape0(importGraph)],
    ['families', `${checker}.families`, () => validateImportGraphFamilies0(importGraph)],
    ['edges', `${checker}.edges`, () => validateImportGraphEdges0(importGraph)],
    ['acyclic', `${checker}.acyclic`, () => validateImportGraphAcyclic0(importGraph)],
    ['tokenOnly', `${checker}.tokenOnly`, () => validateTokenOnlyEdges0(importGraph)],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(importGraph, ['ImportGraph'])],
  ];

  for (const [phase, coord, run] of phases) {
    const result = run();

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
  }

  const edges = getImportEdges0(importGraph);

  const nf = {
    kind: 'ImportGraph0NF',
    checker,
    version: CHECKER_VERSION,
    familyCount: LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
    edgeCount: edges.length,
    forbiddenEdges: GLOBAL_FIREWALL_FORBIDDEN_IMPORT_EDGES0,
    families: LOCAL_PACKAGE_REQUIRED_FAMILIES0,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

/**
 * Validates the global expanded no-hidden-minimization scan record.
 * Input: NoHiddenMinScan0 with stages, forbidden symbols, occurrences, and expansion.
 * Output: accepted scan summary or a named occurrence/metadata reject.
 * Enforces: required expansion stages/symbol list and rejection of forbidden executable
 * occurrences in the supplied expanded artefact record.
 * Does not check: that the supplied expansion contains every dynamic/generated call or
 * that a differently implemented exhaustive search is polynomial.
 * Failure modes: shape/stage/symbol/occurrence/expanded-exec/opaque-proof reject.
 */
export async function CheckNoHiddenMin0(scan) {
  const checker = 'CheckNoHiddenMin0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateNoHiddenMinShape0(scan)],
    ['expansionStages', `${checker}.expansionStages`, () => validateNoHiddenMinStages0(scan)],
    ['forbiddenSymbols', `${checker}.forbiddenSymbols`, () => validateNoHiddenMinSymbols0(scan)],
    ['occurrences', `${checker}.occurrences`, () => validateNoHiddenMinOccurrences0(scan)],
    ['expandedExecutableScan', `${checker}.exec`, () => validateNoHiddenMinExecutableScan0(scan)],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(scan, ['NoHiddenMinScan'])],
  ];

  for (const [phase, coord, run] of phases) {
    const result = run();

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
  }

  const nf = {
    kind: 'NoHiddenMin0NF',
    checker,
    version: CHECKER_VERSION,
    expansionStages: GLOBAL_FIREWALL_EXPANSION_STAGES0,
    forbiddenSymbolCount: GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0.length,
    occurrenceCount: scan.occurrences.length,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

/**
 * Validates the shared finite/polynomial bound record.
 * Input: core, selector, per-family, and global schedule-bound metadata.
 * Output: accepted bounds normal form or phase-specific reject record.
 * Enforces: exact public constants/formulas, required family coverage, finite and
 * polynomial flags, no private schedules, and displayed exponent limits.
 * Does not check: asymptotic runtime from source control flow or certificate-size
 * derivations; supplied bound theorems require independent proof.
 * Failure modes: missing/mismatched core, selector, family, global, or opaque fields.
 */
export async function CheckBounds0(bounds) {
  const checker = 'CheckBounds0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateBoundsShape0(bounds)],
    ['core', `${checker}.core`, () => validateCoreBounds0(bounds)],
    ['selector', `${checker}.selector`, () => validateSelectorBounds0(bounds)],
    ['families', `${checker}.families`, () => validateFamilyBounds0(bounds)],
    ['global', `${checker}.global`, () => validateGlobalBounds0(bounds)],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(bounds, ['Bounds'])],
  ];

  for (const [phase, coord, run] of phases) {
    const result = run();

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
  }

  const nf = {
    kind: 'Bounds0NF',
    checker,
    version: CHECKER_VERSION,
    core: bounds.core,
    selector: bounds.selector,
    familyCount: LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
    maxExponent: bounds.global.maxExponent,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

/**
 * Runs the aggregate import, no-hidden-minimization, and bound checks.
 * Input: GlobalFirewalls0 wrapper pack and its ledgers/proof marker.
 * Output: accepted aggregate normal form or a wrapped first child rejection.
 * Enforces: phase order, child acceptance, digest summaries, and no opaque proof data.
 * Does not check: theorem soundness or completeness of the represented call/import graph.
 * Failure modes: wrapper shape, child checker, or opaque-proof rejection.
 */
export async function CheckGlobalFirewalls0(pack) {
  const checker = 'CheckGlobalFirewalls0';
  const ledger = [];

  const shape = validateGlobalFirewallsShape0(pack);

  ledger.push({
    phase: 'shape',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const phases = [
    ['imports', `${checker}.imports`, ['ImportGraph'], await CheckImportGraph0(pack.ImportGraph)],
    ['noHiddenMin', `${checker}.noHiddenMin`, ['NoHiddenMinScan'], await CheckNoHiddenMin0(pack.NoHiddenMinScan)],
    ['bounds', `${checker}.bounds`, ['Bounds'], await CheckBounds0(pack.Bounds)],
  ];

  for (const [phase, coord, path, record] of phases) {
    const result = recordToValidation0(record, path);

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
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
  }

  const noOpaque = validateNoOpaqueProof0(pack, ['GlobalFirewalls0']);

  ledger.push({
    phase: 'opaque',
    status: noOpaque.ok ? 'pass' : 'fail',
    digest: digestCanonical0(noOpaque.nf ?? noOpaque.witness ?? null),
  });

  if (!noOpaque.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.opaqueProof`,
      path: noOpaque.path,
      witness: noOpaque.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'GlobalFirewalls0NF',
    checker,
    version: CHECKER_VERSION,
    phases: GLOBAL_FIREWALL_PHASES0,
    importGraphDigest: digestCanonical0(pack.ImportGraph),
    noHiddenMinDigest: digestCanonical0(pack.NoHiddenMinScan),
    boundsDigest: digestCanonical0(pack.Bounds),
    familyCount: LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
    forbiddenImportEdges: GLOBAL_FIREWALL_FORBIDDEN_IMPORT_EDGES0,
    forbiddenExecutableSymbols: GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0,
    piFirewallsDigest: digestCanonical0(getPiFirewalls0(pack)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateGlobalFirewallsShape0(pack) {
  if (!isPlainObject(pack)) {
    return validationReject0([], 'GlobalFirewalls0 must be an object', {
      actual: typeof pack,
    });
  }

  if (pack.kind !== undefined && pack.kind !== 'GlobalFirewalls0') {
    return validationReject0(['kind'], 'GlobalFirewalls0 kind must be GlobalFirewalls0 when present', {
      actual: pack.kind,
    });
  }

  if (pack.version !== undefined && pack.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `GlobalFirewalls0 version must be ${CHECKER_VERSION} when present`, {
      actual: pack.version,
    });
  }

  for (const field of GLOBAL_FIREWALL_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(pack, field)) {
      return validationReject0([field], 'GlobalFirewalls0 is missing a required field', {
        field,
      });
    }
  }

  if (!Array.isArray(pack.PhaseOrder)) {
    return validationReject0(['PhaseOrder'], 'GlobalFirewalls0 PhaseOrder must be an array', null);
  }

  for (let index = 0; index < GLOBAL_FIREWALL_PHASES0.length; index += 1) {
    if (pack.PhaseOrder[index] !== GLOBAL_FIREWALL_PHASES0[index]) {
      return validationReject0(['PhaseOrder', index], 'GlobalFirewalls0 PhaseOrder mismatch', {
        expected: GLOBAL_FIREWALL_PHASES0[index],
        actual: pack.PhaseOrder[index],
      });
    }
  }

  if (getPiFirewalls0(pack) === undefined) {
    return validationReject0(['PiFirewalls'], 'GlobalFirewalls0 is missing PiFirewalls or Πfirewalls', null);
  }

  return validationAccept0({
    kind: 'GlobalFirewallsShape0NF',
  });
}

function validateImportGraphShape0(importGraph) {
  if (!isPlainObject(importGraph)) {
    return validationReject0([], 'ImportGraph0 must be an object', {
      actual: typeof importGraph,
    });
  }

  if (importGraph.kind !== undefined && importGraph.kind !== 'ImportGraph0') {
    return validationReject0(['kind'], 'ImportGraph0 kind must be ImportGraph0 when present', {
      actual: importGraph.kind,
    });
  }

  if (importGraph.version !== undefined && importGraph.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ImportGraph0 version must be ${CHECKER_VERSION} when present`, {
      actual: importGraph.version,
    });
  }

  if (!Array.isArray(importGraph.families)) {
    return validationReject0(['families'], 'ImportGraph0 families must be an array', {
      actual: typeof importGraph.families,
    });
  }

  if (!Array.isArray(getImportEdges0(importGraph))) {
    return validationReject0(['edges'], 'ImportGraph0 edges must be an array', {
      actual: typeof getImportEdges0(importGraph),
    });
  }

  return validationAccept0({
    kind: 'ImportGraphShape0NF',
  });
}

function validateImportGraphFamilies0(importGraph) {
  const seen = new Set();

  for (let index = 0; index < importGraph.families.length; index += 1) {
    const family = importGraph.families[index];

    if (!isNonEmptyString(family)) {
      return validationReject0(['families', index], 'ImportGraph0 family must be a non-empty string', {
        actual: family,
      });
    }

    if (seen.has(family)) {
      return validationReject0(['families', index], 'ImportGraph0 families must be unique', {
        family,
      });
    }

    seen.add(family);
  }

  for (const family of LOCAL_PACKAGE_REQUIRED_FAMILIES0) {
    if (!seen.has(family)) {
      return validationReject0(['families', family], 'ImportGraph0 is missing a required package family', {
        family,
      });
    }
  }

  return validationAccept0({
    kind: 'ImportGraphFamilies0NF',
    familyCount: seen.size,
  });
}

function validateImportGraphEdges0(importGraph) {
  const families = new Set(importGraph.families);
  const forbidden = new Set(GLOBAL_FIREWALL_FORBIDDEN_IMPORT_EDGES0.map((edge) => edgeKey0(edge)));
  const edges = getImportEdges0(importGraph);

  for (let index = 0; index < edges.length; index += 1) {
    const edge = normalizeEdge0(edges[index]);

    if (edge === null) {
      return validationReject0(['edges', index], 'ImportGraph0 edge must have from and to endpoints', {
        edge: edges[index],
      });
    }

    if (forbidden.has(edgeKey0(edge))) {
      return validationReject0(['edges', index], 'ImportGraph contains a forbidden import edge', {
        edge,
      });
    }

    if (!families.has(edge.from)) {
      return validationReject0(['edges', index, 'from'], 'ImportGraph0 edge source is unknown', {
        edge,
      });
    }

    if (!families.has(edge.to)) {
      return validationReject0(['edges', index, 'to'], 'ImportGraph0 edge target is unknown', {
        edge,
      });
    }
  }

  return validationAccept0({
    kind: 'ImportGraphEdges0NF',
    edgeCount: edges.length,
  });
}

function validateImportGraphAcyclic0(importGraph) {
  if (importGraph.acyclic === false) {
    return validationReject0(['acyclic'], 'ImportGraph0 must be declared acyclic', null);
  }

  const graph = new Map();

  for (const family of importGraph.families) {
    graph.set(family, []);
  }

  for (const rawEdge of getImportEdges0(importGraph)) {
    const edge = normalizeEdge0(rawEdge);

    if (edge !== null && graph.has(edge.from)) {
      graph.get(edge.from).push(edge.to);
    }
  }

  const cycle = findCycle0(graph);

  if (cycle !== null) {
    return validationReject0(['edges', 'cycle'], 'ImportGraph0 contains an import cycle', {
      cycle,
    });
  }

  return validationAccept0({
    kind: 'ImportGraphAcyclic0NF',
  });
}

function validateTokenOnlyEdges0(importGraph) {
  const tokenOnlyEdges = importGraph.tokenOnlyEdges ?? [];

  if (!Array.isArray(tokenOnlyEdges)) {
    return validationReject0(['tokenOnlyEdges'], 'ImportGraph0 tokenOnlyEdges must be an array when present', {
      actual: typeof tokenOnlyEdges,
    });
  }

  const forbidden = new Set(GLOBAL_FIREWALL_FORBIDDEN_IMPORT_EDGES0.map((edge) => edgeKey0(edge)));

  for (let index = 0; index < tokenOnlyEdges.length; index += 1) {
    const edge = normalizeEdge0(tokenOnlyEdges[index]);

    if (edge === null) {
      return validationReject0(['tokenOnlyEdges', index], 'token-only edge must have from and to endpoints', {
        edge: tokenOnlyEdges[index],
      });
    }

    if (!isNonEmptyString(tokenOnlyEdges[index].token)) {
      return validationReject0(['tokenOnlyEdges', index, 'token'], 'token-only edge must carry a token label', {
        edge: tokenOnlyEdges[index],
      });
    }

    if (!forbidden.has(edgeKey0(edge))) {
      continue;
    }
  }

  return validationAccept0({
    kind: 'TokenOnlyEdges0NF',
    tokenOnlyCount: tokenOnlyEdges.length,
  });
}

function validateNoHiddenMinShape0(scan) {
  if (!isPlainObject(scan)) {
    return validationReject0([], 'NoHiddenMinScan0 must be an object', {
      actual: typeof scan,
    });
  }

  if (scan.kind !== undefined && scan.kind !== 'NoHiddenMinScan0') {
    return validationReject0(['kind'], 'NoHiddenMinScan0 kind must be NoHiddenMinScan0 when present', {
      actual: scan.kind,
    });
  }

  if (scan.version !== undefined && scan.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `NoHiddenMinScan0 version must be ${CHECKER_VERSION} when present`, {
      actual: scan.version,
    });
  }

  for (const field of ['expansionStages', 'forbiddenSymbols', 'occurrences']) {
    if (!Array.isArray(scan[field])) {
      return validationReject0([field], `NoHiddenMinScan0 ${field} must be an array`, {
        actual: typeof scan[field],
      });
    }
  }

  return validationAccept0({
    kind: 'NoHiddenMinShape0NF',
  });
}

function validateNoHiddenMinStages0(scan) {
  if (!arrayContainsAll0(scan.expansionStages, GLOBAL_FIREWALL_EXPANSION_STAGES0)) {
    return validationReject0(['expansionStages'], 'NoHiddenMinScan0 must expand macros, aliases, generated templates, and imports', {
      expected: GLOBAL_FIREWALL_EXPANSION_STAGES0,
      actual: scan.expansionStages,
    });
  }

  for (const field of [
    'importsScanned',
    'macrosExpanded',
    'aliasesExpanded',
    'generatedTemplatesExpanded',
  ]) {
    if (scan[field] !== true) {
      return validationReject0([field], `NoHiddenMinScan0 must set ${field}`, {
        actual: scan[field],
      });
    }
  }

  return validationAccept0({
    kind: 'NoHiddenMinStages0NF',
  });
}

function validateNoHiddenMinSymbols0(scan) {
  if (!arrayContainsAll0(scan.forbiddenSymbols, GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0)) {
    return validationReject0(['forbiddenSymbols'], 'NoHiddenMinScan0 is missing a forbidden executable symbol', {
      expected: GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0,
      actual: scan.forbiddenSymbols,
    });
  }

  return validationAccept0({
    kind: 'NoHiddenMinSymbols0NF',
    forbiddenSymbolCount: GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0.length,
  });
}

function validateNoHiddenMinOccurrences0(scan) {
  const aliases = isPlainObject(scan.aliases) ? scan.aliases : {};

  for (let index = 0; index < scan.occurrences.length; index += 1) {
    const occurrence = scan.occurrences[index];

    if (!isPlainObject(occurrence)) {
      return validationReject0(['occurrences', index], 'NoHiddenMin occurrence must be an object', {
        actual: typeof occurrence,
      });
    }

    if (!isNonEmptyString(occurrence.identifier)) {
      return validationReject0(['occurrences', index, 'identifier'], 'NoHiddenMin occurrence must have an identifier', {
        actual: occurrence.identifier,
      });
    }

    if (!isNonEmptyString(occurrence.occurrenceClass)) {
      return validationReject0(['occurrences', index, 'occurrenceClass'], 'NoHiddenMin occurrence must have an occurrenceClass', {
        actual: occurrence.occurrenceClass,
      });
    }

    const expanded = occurrence.expandedIdentifier ?? aliases[occurrence.identifier] ?? occurrence.identifier;

    if (
      occurrence.occurrenceClass === 'ExecCall' &&
      (
        GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0.includes(occurrence.identifier) ||
        GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0.includes(expanded)
      )
    ) {
      return validationReject0(['occurrences', index, 'identifier'], 'forbidden minimization symbol appears in executable position', {
        identifier: occurrence.identifier,
        expandedIdentifier: expanded,
        occurrenceClass: occurrence.occurrenceClass,
      });
    }
  }

  return validationAccept0({
    kind: 'NoHiddenMinOccurrences0NF',
    occurrenceCount: scan.occurrences.length,
  });
}

function validateNoHiddenMinExecutableScan0(scan) {
  const hit = findForbiddenExecutableUse0(scan, ['NoHiddenMinScan'], false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'NoHiddenMinExecutableScan0NF',
  });
}

function validateBoundsShape0(bounds) {
  if (!isPlainObject(bounds)) {
    return validationReject0([], 'Bounds0 must be an object', {
      actual: typeof bounds,
    });
  }

  if (bounds.kind !== undefined && bounds.kind !== 'Bounds0') {
    return validationReject0(['kind'], 'Bounds0 kind must be Bounds0 when present', {
      actual: bounds.kind,
    });
  }

  if (bounds.version !== undefined && bounds.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `Bounds0 version must be ${CHECKER_VERSION} when present`, {
      actual: bounds.version,
    });
  }

  for (const field of ['core', 'selector', 'families', 'global']) {
    if (!Object.prototype.hasOwnProperty.call(bounds, field)) {
      return validationReject0([field], 'Bounds0 is missing a required field', {
        field,
      });
    }
  }

  if (!Array.isArray(bounds.families)) {
    return validationReject0(['families'], 'Bounds0 families must be an array', {
      actual: typeof bounds.families,
    });
  }

  return validationAccept0({
    kind: 'BoundsShape0NF',
  });
}

function validateCoreBounds0(bounds) {
  if (!isPlainObject(bounds.core)) {
    return validationReject0(['core'], 'Bounds0 core must be an object', {
      actual: typeof bounds.core,
    });
  }

  for (const [field, expected] of Object.entries(GLOBAL_FIREWALL_CORE_BOUNDS0)) {
    if (bounds.core[field] !== expected) {
      return validationReject0(['core', field], 'Bounds0 core constant mismatch', {
        field,
        expected,
        actual: bounds.core[field],
      });
    }
  }

  return validationAccept0({
    kind: 'CoreBounds0NF',
    core: bounds.core,
  });
}

function validateSelectorBounds0(bounds) {
  if (!isPlainObject(bounds.selector)) {
    return validationReject0(['selector'], 'Bounds0 selector must be an object', {
      actual: typeof bounds.selector,
    });
  }

  for (const [field, expected] of Object.entries(GLOBAL_FIREWALL_SELECTOR_BOUNDS0)) {
    if (bounds.selector[field] !== expected) {
      return validationReject0(['selector', field], 'Bounds0 selector constant mismatch', {
        field,
        expected,
        actual: bounds.selector[field],
      });
    }
  }

  if (bounds.selector.finite !== true || bounds.selector.polynomial !== true) {
    return validationReject0(['selector'], 'Bounds0 selector bounds must be finite and polynomial', {
      finite: bounds.selector.finite,
      polynomial: bounds.selector.polynomial,
    });
  }

  return validationAccept0({
    kind: 'SelectorBounds0NF',
    selector: bounds.selector,
  });
}

function validateFamilyBounds0(bounds) {
  const seen = new Set();

  for (let index = 0; index < bounds.families.length; index += 1) {
    const entry = bounds.families[index];

    if (!isPlainObject(entry)) {
      return validationReject0(['families', index], 'Bounds0 family entry must be an object', {
        actual: typeof entry,
      });
    }

    if (!LOCAL_PACKAGE_REQUIRED_FAMILIES0.includes(entry.family)) {
      return validationReject0(['families', index, 'family'], 'Bounds0 family entry is unknown', {
        family: entry.family,
      });
    }

    if (seen.has(entry.family)) {
      return validationReject0(['families', index, 'family'], 'Bounds0 family entries must be unique', {
        family: entry.family,
      });
    }

    seen.add(entry.family);

    if (entry.finite !== true || entry.polynomial !== true) {
      return validationReject0(['families', index], 'Bounds0 family bounds must be finite and polynomial', {
        family: entry.family,
        finite: entry.finite,
        polynomial: entry.polynomial,
      });
    }

    if (entry.privateSchedule === true) {
      return validationReject0(['families', index, 'privateSchedule'], 'Bounds0 forbids private schedule enlargement', {
        family: entry.family,
      });
    }

    const expected = expectedBoundsForFamily0(entry.family);

    for (const field of ['scale', 'k', 'beta', 'o', 'h', 'r']) {
      if (entry[field] !== expected[field]) {
        return validationReject0(['families', index, field], 'family bound does not match public schedule', {
          family: entry.family,
          field,
          expected: expected[field],
          actual: entry[field],
        });
      }
    }

    for (const field of ['k', 'beta', 'o', 'h', 'r']) {
      if (!Number.isInteger(entry[field]) || entry[field] <= 0) {
        return validationReject0(['families', index, field], 'family bound must be a positive integer', {
          family: entry.family,
          field,
          actual: entry[field],
        });
      }
    }

    if (entry.beta > 64) {
      return validationReject0(['families', index, 'beta'], 'family beta bound must be at most 64', {
        family: entry.family,
        beta: entry.beta,
      });
    }
  }

  for (const family of LOCAL_PACKAGE_REQUIRED_FAMILIES0) {
    if (!seen.has(family)) {
      return validationReject0(['families', family], 'Bounds0 is missing a required family bound', {
        family,
      });
    }
  }

  return validationAccept0({
    kind: 'FamilyBounds0NF',
    familyCount: LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
  });
}

function validateGlobalBounds0(bounds) {
  if (!isPlainObject(bounds.global)) {
    return validationReject0(['global'], 'Bounds0 global must be an object', {
      actual: typeof bounds.global,
    });
  }

  if (bounds.global.finite !== true || bounds.global.polynomial !== true) {
    return validationReject0(['global'], 'Bounds0 global bounds must be finite and polynomial', {
      finite: bounds.global.finite,
      polynomial: bounds.global.polynomial,
    });
  }

  if (bounds.global.noPrivateSchedule !== true) {
    return validationReject0(['global', 'noPrivateSchedule'], 'Bounds0 must reject private schedule enlargement', {
      actual: bounds.global.noPrivateSchedule,
    });
  }

  if (!Number.isInteger(bounds.global.maxExponent) || bounds.global.maxExponent <= 0) {
    return validationReject0(['global', 'maxExponent'], 'Bounds0 global maxExponent must be positive', {
      actual: bounds.global.maxExponent,
    });
  }

  return validationAccept0({
    kind: 'GlobalBounds0NF',
    maxExponent: bounds.global.maxExponent,
  });
}

function expectedBoundsForFamily0(family) {
  const scale = scaleForFamily0(family);
  const core = GLOBAL_FIREWALL_CORE_BOUNDS0;

  return {
    scale,
    k: scale * core.K0,
    beta: Math.min(4 * scale + 12, 64),
    o: scale * core.O0,
    h: scale * core.H0,
    r: scale * core.Rel0,
  };
}

function scaleForFamily0(family) {
  if (family === 'E' || family === 'N' || family === 'FT') {
    return 1;
  }

  if (family === 'FTX' || family === 'X' || family === 'Splice') {
    return 2;
  }

  if (family === 'BC' || family === 'UN' || family === 'HNShape') {
    return 4;
  }

  if (
    family === 'HN' ||
    family === 'HResolve' ||
    family === 'BUD' ||
    family === 'NORFF' ||
    family === 'RW' ||
    family === 'BN2' ||
    family === 'BN3' ||
    family === 'BN4' ||
    family === 'BN5' ||
    family === 'BN6'
  ) {
    return 8;
  }

  return 16;
}

function getImportEdges0(importGraph) {
  return importGraph.edges ?? importGraph.Edges ?? [];
}

function normalizeEdge0(edge) {
  if (Array.isArray(edge) && edge.length >= 2) {
    return {
      from: String(edge[0]),
      to: String(edge[1]),
      kind: 'Import',
    };
  }

  if (isPlainObject(edge)) {
    const from = edge.from ?? edge.src;
    const to = edge.to ?? edge.dst;

    if (from !== undefined && to !== undefined) {
      return {
        from: String(from),
        to: String(to),
        kind: edge.kind ?? 'Import',
      };
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

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && GLOBAL_FIREWALL_FORBIDDEN_EXEC_SYMBOLS0.includes(value)) {
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

function findOpaqueProof0(value, path = []) {
  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findOpaqueProof0(value[index], [...path, index]);

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
    if (/opaqueproof|proofblob|trustedblob|assumeproof/i.test(key)) {
      return {
        key,
        path: [...path, key],
        value: value[key],
      };
    }

    const hit = findOpaqueProof0(value[key], [...path, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function validateNoOpaqueProof0(value, path) {
  const hit = findOpaqueProof0(value, path);

  if (hit !== null) {
    return validationReject0(hit.path, 'opaque proof material is not allowed in global firewalls', hit);
  }

  return validationAccept0({
    kind: 'NoOpaqueProof0NF',
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

function getPiFirewalls0(pack) {
  return pack.PiFirewalls ?? pack['Πfirewalls'] ?? pack.piFirewalls;
}

function arrayContainsAll0(actual, required) {
  if (!Array.isArray(actual)) {
    return false;
  }

  return required.every((entry) => actual.includes(entry));
}

function isNonEmptyString(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}