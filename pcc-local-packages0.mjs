import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  ROW_FAMILY_SPECS0,
} from './pcc-rows0.mjs';

import {
  GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0,
} from './pcc-global-proof-dag0.mjs';

const CHECKER_VERSION = 0;

export const LOCAL_PACKAGE_FORBIDDEN_IMPORT_EDGES0 = Object.freeze([
  Object.freeze(['BC', 'UN']),
  Object.freeze(['UN', 'BC']),
  Object.freeze(['BCEL', 'R']),
  Object.freeze(['BUD', 'R']),
  Object.freeze(['O', 'G']),
  Object.freeze(['G', 'O']),
]);

export const LOCAL_PACKAGE_FORBIDDEN_EXEC_SYMBOLS0 = Object.freeze([
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

export const LOCAL_PACKAGE_EXPANSION_STAGES0 = Object.freeze([
  'macros',
  'aliases',
  'generatedTemplates',
  'imports',
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

const LOCAL_PACKAGE_REQUIRED_FIELDS0 = Object.freeze([
  'SchedHash',
  'IfaceHash',
  'RowPackDigest',
  'PackageInv',
  'Packages',
  'FamilyChecks',
  'ImportLedger',
  'BoundsLedger',
  'NoMinLedger',
  'ReflectionLedger',
]);

const LOCAL_THEOREM_BY_FAMILY0 = Object.freeze({
  E: 'E.VerifyDWSoundness',
  N: 'N.TraceableNormalization',
  Splice: 'Splice.BoundedAndComposed',
  FT: 'FT.FiniteTableCoverage',
  FTX: 'FTX.CriticalWindowTables',
  X: 'X.CriticalWindowRouting',
  BC: 'BC.BranchCycleRouting',
  UN: 'UN.UnaryDecoderRouting',
  HNShape: 'HNShape.TokenSoundness',
  HN: 'HN.LeafTightness',
  HResolve: 'HResolve.GlobalHereditaryResolver',
  BUD: 'BUD.BudgetResolver',
  NORFF: 'NORFF.FrontierFaithfulComparison',
  RW: 'RW.BCELReady',
  BN2: 'BN2.SideTightCoherentOptimum',
  BN3: 'BN3.SimultaneousEnvelope',
  BN4: 'BN4.ActivationExact',
  BN5: 'BN5.FullShadowLocalization',
  PkgC: 'PkgC.SeparatingConsumers',
  BN6: 'BN6.HypergraphPacket',
  Packet: 'Packet.SelectorSeeds',
  R: 'R.SelectorRealization',
  HB: 'HB.NegativeClosure',
  O: 'O.ZeroSlackOracle',
  G: 'G.LockedNANDThreshold',
  Final: 'Final.FrameworkMatch',
  PACK: 'PACK.PackageSufficiency',
});

const LOCAL_CONTRACTS_BY_FAMILY0 = Object.freeze({
  E: ['verify-dw', 'obligation-lifecycle', 'charge-ledger', 'residual-descent'],
  N: ['traceable-normalization', 'pullback-expansion', 'termination-rank'],
  Splice: ['bounded-splice', 'seam-atlas', 'strict-component-compilation'],
  FT: ['finite-table-coverage', 'truth-vector-evaluator', 'normalization-transport'],
  FTX: ['critical-table-coverage', 'finite-exhaustion', 'resource-routing'],
  X: ['critical-window-routing', 'candidate-towers', 'hall-witness'],
  BC: ['finite-transition-category', 'cycle-audit', 'no-un-import'],
  UN: ['unary-decoder', 'blocked-interval', 'no-bc-import'],
  HNShape: ['shape-token', 'hereditary-shape-recognition'],
  HN: ['hereditary-grammar', 'bwl-exactness', 'leaf-tightness'],
  HResolve: ['h-disjoint-family', 'no-hereditary-sidecar', 'exact-or-gain'],
  BUD: ['budget-envelope-dp', 'no-budget-sidecar', 'exact-or-gain'],
  NORFF: ['strong-neutral-overlay', 'first-loss-routing', 'frontier-faithful-comparison'],
  RW: ['terminal-mu-bridge', 'saturate-positive', 'bcel-ready'],
  BN2: ['side-tight-squares', 'coherent-optimum'],
  BN3: ['request-envelope', 'minimal-consumer-antichains'],
  BN4: ['activation-exact-cancellation', 'residual-cells'],
  BN5: ['full-shadow-localization', 'cut-silence'],
  PkgC: ['separating-consumers', 'restoration-towers', 'hall-localization'],
  BN6: ['hypergraph-cellization', 'constant-cut-rigidity', 'packet-prototypes'],
  Packet: ['pair-seed', 'balanced-triple-seed', 'full-span-spine-seed'],
  R: ['selector-realizer', 'typed-bottom', 'charge-surplus'],
  HB: ['blocker-graph', 'rank-negative-closure', 'selector-silence'],
  O: ['rank-ordered-oracle', 'zero-slack', 'residual-band-minimization'],
  G: ['locked-nand', 'macro-truth-tables', 'threshold'],
  Final: ['framework-match', 'sat-decision', 'final-theorem'],
  PACK: ['top-level-package-sufficiency', 'reflection', 'bounds'],
});

const DEFAULT_IMPORTS_BY_FAMILY0 = Object.freeze({
  E: [],
  N: ['E'],
  Splice: ['E', 'N'],
  FT: ['E'],
  FTX: ['FT'],
  X: ['FTX', 'Splice'],
  BC: ['X'],
  UN: ['X'],
  HNShape: ['BC'],
  HN: ['HNShape'],
  HResolve: ['HN'],
  BUD: ['HResolve'],
  NORFF: ['BUD'],
  RW: ['NORFF'],
  BN2: ['RW'],
  BN3: ['BN2'],
  BN4: ['BN3'],
  BN5: ['BN4'],
  PkgC: ['BN5'],
  BN6: ['PkgC'],
  Packet: ['BN6'],
  R: ['Packet'],
  HB: ['R'],
  O: ['HB'],
  G: ['Packet'],
  Final: ['O', 'G'],
  PACK: ['Final'],
});

export const LOCAL_PACKAGE_REQUIREMENTS0 = Object.freeze(
  ROW_FAMILY_SPECS0.map((spec, index) => Object.freeze({
    index,
    family: spec.family,
    batchId: spec.batchId,
    packageId: spec.packageId,
    schemaId: spec.schemaId,
    kindKey: spec.kindKey,
    arityKey: spec.arityKey,
    payloadKey: spec.payloadKey,
    proofRule: spec.proofRule,
    bound: spec.bound,
    theorem: LOCAL_THEOREM_BY_FAMILY0[spec.family] ?? `${spec.family}.LocalSoundness`,
    contracts: LOCAL_CONTRACTS_BY_FAMILY0[spec.family] ?? ['local-soundness'],
    defaultImports: DEFAULT_IMPORTS_BY_FAMILY0[spec.family] ?? [],
  }))
);

export const LOCAL_PACKAGE_REQUIRED_FAMILIES0 = Object.freeze(
  LOCAL_PACKAGE_REQUIREMENTS0.map((entry) => entry.family)
);

export function makeLocalPackage0(requirement, overrides = {}) {
  const req = normalizeRequirement0(requirement);

  const localPackage = {
    kind: 'LocalPackage0',
    version: CHECKER_VERSION,
    family: req.family,
    packageId: req.packageId,
    batchId: req.batchId,
    schemaId: req.schemaId,
    kindKey: req.kindKey,
    arityKey: req.arityKey,
    payloadKey: req.payloadKey,
    theorem: req.theorem,
    checkerId: `CheckRowFam${safeId0(req.family)}0`,
    imports: [...req.defaultImports],
    rowRefs: [
      {
        batchId: req.batchId,
        family: req.family,
        packageId: req.packageId,
        schemaId: req.schemaId,
        kindKey: req.kindKey,
      },
    ],
    contracts: req.contracts.map((contract) => ({
      name: contract,
      accepted: true,
      digest: digestCanonical0({
        family: req.family,
        contract,
      }),
    })),
    routes: {
      highestPriority: true,
      constructiveRoutesCompileToVerifyDW: true,
      exactRoutesAccepted: true,
      descentRanks: true,
      entries: [],
    },
    proof: {
      typed: true,
      acyclic: true,
      modeSafe: true,
      hashIndependent: true,
      reflectionAccepted: true,
      publicConclusion: {
        theorem: req.theorem,
      },
    },
    bounds: {
      finite: true,
      polynomial: true,
      exponent: 8,
      ref: req.bound,
    },
    noHiddenMin: {
      expanded: LOCAL_PACKAGE_EXPANSION_STAGES0,
      forbiddenSymbols: LOCAL_PACKAGE_FORBIDDEN_EXEC_SYMBOLS0,
    },
    sidecars: {
      total: true,
      blockerAcyclic: true,
      rankDecreasing: true,
    },
    payload: {
      tag: 'LocalPackagePayload0',
      family: req.family,
      theorem: req.theorem,
    },
  };

  return {
    ...localPackage,
    ...overrides,
  };
}

export function makeLocalPackageInventory0(packages) {
  return {
    kind: 'LocalPackageInventory0',
    version: CHECKER_VERSION,
    entries: packages.map((entry, index) => ({
      index,
      family: entry.family,
      packageId: entry.packageId,
      batchId: entry.batchId,
      schemaId: entry.schemaId,
      checkerId: entry.checkerId,
      theorem: entry.theorem,
    })),
  };
}

export function makeSyntheticLocalPackages0(overrides = {}) {
  const packages = LOCAL_PACKAGE_REQUIREMENTS0.map((requirement) => makeLocalPackage0(requirement));

  const pack = {
    kind: 'LocalPackagePack0',
    version: CHECKER_VERSION,
    SchedHash: {
      alg: 'SHA256',
      hex: '43da1d5b7b91a0f11729290d4b90afd6ddca86a1de8a8441ff5bb1fd88d95bc3',
    },
    IfaceHash: {
      alg: 'SHA256',
      hex: '202b39296313eb7096ea0b9de1294d4edd74efba18a48b323a57e64c5dd73b2b',
    },
    RowPackDigest: {
      alg: 'SHA256',
      hex: '073f9ca20cfda96871cbac63e05ca107aac55a9e9315750cd09d3f5894e848ce',
    },
    PackageInv: makeLocalPackageInventory0(packages),
    Packages: packages,
    FamilyChecks: packages.map((entry) => ({
      family: entry.family,
      checkerId: entry.checkerId,
      accepted: true,
    })),
    ImportLedger: {
      kind: 'LocalImportLedger0',
      acyclic: true,
      forbiddenEdges: LOCAL_PACKAGE_FORBIDDEN_IMPORT_EDGES0,
    },
    BoundsLedger: {
      kind: 'LocalBoundsLedger0',
      finite: true,
      polynomial: true,
      exponent: 8,
    },
    NoMinLedger: {
      kind: 'LocalNoMinLedger0',
      expanded: LOCAL_PACKAGE_EXPANSION_STAGES0,
      forbiddenSymbols: LOCAL_PACKAGE_FORBIDDEN_EXEC_SYMBOLS0,
    },
    ReflectionLedger: {
      kind: 'LocalReflectionLedger0',
      exact: true,
      publicConclusion: true,
      replayable: true,
      theorems: packages.map((entry) => entry.theorem),
    },
    PiLocalPackages: {
      kind: 'PiLocalPackages0',
      version: CHECKER_VERSION,
      note: 'synthetic local package proof marker',
    },
  };

  return {
    ...pack,
    ...overrides,
  };
}

export async function CheckLocalPackageFamily0(localPackage) {
  const checker = 'CheckLocalPackageFamily0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateLocalPackageShape0(localPackage)],
    ['identity', `${checker}.identity`, () => validateLocalPackageIdentity0(localPackage)],
    ['contracts', `${checker}.contracts`, () => validateLocalPackageContracts0(localPackage)],
    ['rowRefs', `${checker}.rowRefs`, () => validateLocalPackageRowRefs0(localPackage)],
    ['routes', `${checker}.routes`, () => validateLocalPackageRoutes0(localPackage)],
    ['proof', `${checker}.proof`, () => validateLocalPackageProof0(localPackage)],
    ['bounds', `${checker}.bounds`, () => validateLocalPackageBounds0(localPackage)],
    ['noHiddenMinMetadata', `${checker}.noHiddenMinMetadata`, () => validateLocalPackageNoMinMetadata0(localPackage)],
    ['noHiddenMin', `${checker}.noHiddenMin`, () => validateNoHiddenExecutableMin0(localPackage, ['LocalPackage'])],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(localPackage, ['LocalPackage'])],
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

  const requirement = requirementByFamily0(localPackage.family);

  const nf = {
    kind: 'LocalPackageFamily0NF',
    checker,
    version: CHECKER_VERSION,
    family: localPackage.family,
    packageId: localPackage.packageId,
    batchId: localPackage.batchId,
    schemaId: localPackage.schemaId,
    theorem: localPackage.theorem,
    checkerId: localPackage.checkerId,
    contractCount: requirement.contracts.length,
    importCount: localPackage.imports.length,
    rowRefCount: localPackage.rowRefs.length,
    digest: digestCanonical0(localPackage),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckLocalPackages0(pack) {
  const checker = 'CheckLocalPackages0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateLocalPackShape0(pack)],
    ['inventory', `${checker}.inventory`, () => validateLocalPackageInventory0(pack)],
    ['coverage', `${checker}.coverage`, () => validateLocalPackageCoverage0(pack)],
    ['imports', `${checker}.imports`, () => validateLocalPackageImports0(pack)],
    ['noHiddenMin', `${checker}.noHiddenMin`, () => validateNoHiddenExecutableMin0(pack, ['LocalPackagePack0'])],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(pack, ['LocalPackagePack0'])],
    ['packages', `${checker}.packages`, async () => validateLocalPackages0(pack)],
    ['globalTheorems', `${checker}.globalTheorems`, () => validateGlobalTheoremAlignment0(pack)],
    ['ledgers', `${checker}.ledgers`, () => validateLocalPackageLedgers0(pack)],
  ];

  for (const [phase, coord, run] of phases) {
    const result = await run();

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
    kind: 'LocalPackages0NF',
    checker,
    version: CHECKER_VERSION,
    packageCount: pack.Packages.length,
    familyCount: LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
    families: LOCAL_PACKAGE_REQUIRED_FAMILIES0,
    globalTheorems: GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0,
    packageDigests: pack.Packages.map((entry, index) => ({
      index,
      family: entry.family,
      packageId: entry.packageId,
      checkerId: entry.checkerId,
      theorem: entry.theorem,
      digest: digestCanonical0(entry),
    })),
    piLocalPackagesDigest: digestCanonical0(getPiLocalPackages0(pack)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateLocalPackShape0(pack) {
  if (!isPlainObject(pack)) {
    return validationReject0([], 'LocalPackagePack0 must be an object', {
      actual: typeof pack,
    });
  }

  if (pack.kind !== undefined && pack.kind !== 'LocalPackagePack0') {
    return validationReject0(['kind'], 'LocalPackagePack0 kind must be LocalPackagePack0 when present', {
      actual: pack.kind,
    });
  }

  if (pack.version !== undefined && pack.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `LocalPackagePack0 version must be ${CHECKER_VERSION} when present`, {
      actual: pack.version,
    });
  }

  for (const field of LOCAL_PACKAGE_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(pack, field)) {
      return validationReject0([field], 'LocalPackagePack0 is missing a required field', {
        field,
      });
    }
  }

  if (!Array.isArray(pack.Packages)) {
    return validationReject0(['Packages'], 'LocalPackagePack0 Packages must be an array', {
      actual: typeof pack.Packages,
    });
  }

  if (getPiLocalPackages0(pack) === undefined) {
    return validationReject0(['PiLocalPackages'], 'LocalPackagePack0 is missing PiLocalPackages or Πlocal', null);
  }

  return validationAccept0({
    kind: 'LocalPackagePackShape0NF',
  });
}

function validateLocalPackageInventory0(pack) {
  const entries = getInventoryEntries0(pack.PackageInv);

  if (!Array.isArray(entries)) {
    return validationReject0(['PackageInv'], 'PackageInv must provide an entries array', {
      actual: typeof entries,
    });
  }

  const seen = new Set();

  for (let index = 0; index < entries.length; index += 1) {
    const entry = entries[index];

    if (!isPlainObject(entry)) {
      return validationReject0(['PackageInv', 'entries', index], 'PackageInv entry must be an object', {
        actual: typeof entry,
      });
    }

    if (!isNonEmptyString(entry.family)) {
      return validationReject0(['PackageInv', 'entries', index, 'family'], 'PackageInv entry must name a family', {
        actual: entry.family,
      });
    }

    if (seen.has(entry.family)) {
      return validationReject0(['PackageInv', 'entries', index, 'family'], 'PackageInv family entries must be unique', {
        family: entry.family,
      });
    }

    seen.add(entry.family);
  }

  for (const family of LOCAL_PACKAGE_REQUIRED_FAMILIES0) {
    if (!seen.has(family)) {
      return validationReject0(['PackageInv', 'coverage', family], 'PackageInv is missing a required family', {
        family,
      });
    }
  }

  return validationAccept0({
    kind: 'LocalPackageInventory0NF',
    inventoryCount: entries.length,
  });
}

function validateLocalPackageCoverage0(pack) {
  const byFamily = packageMap0(pack.Packages);

  for (const family of LOCAL_PACKAGE_REQUIRED_FAMILIES0) {
    if (!byFamily.has(family)) {
      return validationReject0(['Packages', 'coverage', family], 'LocalPackagePack0 is missing a required local package family', {
        family,
      });
    }
  }

  return validationAccept0({
    kind: 'LocalPackageCoverage0NF',
    familyCount: LOCAL_PACKAGE_REQUIRED_FAMILIES0.length,
  });
}

function validateLocalPackageImports0(pack) {
  const byFamily = packageMap0(pack.Packages);
  const order = new Map(LOCAL_PACKAGE_REQUIRED_FAMILIES0.map((family, index) => [family, index]));
  const forbidden = new Set(LOCAL_PACKAGE_FORBIDDEN_IMPORT_EDGES0.map((edge) => edgeKey0(edge)));

  for (const pkg of pack.Packages) {
    if (!Array.isArray(pkg.imports)) {
      return validationReject0(['Packages', pkg.family, 'imports'], 'local package imports must be an array', {
        family: pkg.family,
      });
    }

    for (let importIndex = 0; importIndex < pkg.imports.length; importIndex += 1) {
      const dep = String(pkg.imports[importIndex]);

      if (!byFamily.has(dep)) {
        return validationReject0(['Packages', pkg.family, 'imports', importIndex], 'local package import references an unknown family', {
          family: pkg.family,
          dep,
        });
      }

      if (forbidden.has(edgeKey0([pkg.family, dep]))) {
        return validationReject0(['Packages', pkg.family, 'imports', importIndex], 'local package import uses a forbidden package edge', {
          family: pkg.family,
          dep,
          edge: [pkg.family, dep],
        });
      }

      if ((order.get(dep) ?? Number.MAX_SAFE_INTEGER) >= (order.get(pkg.family) ?? -1)) {
        return validationReject0(['Packages', pkg.family, 'imports', importIndex], 'local package imports must point to earlier package families', {
          family: pkg.family,
          dep,
        });
      }
    }
  }

  return validationAccept0({
    kind: 'LocalPackageImports0NF',
    packageCount: pack.Packages.length,
  });
}

async function validateLocalPackages0(pack) {
  for (const pkg of pack.Packages) {
    const out = await CheckLocalPackageFamily0(pkg);

    if (isRejectRecord0(out)) {
      return validationReject0(['Packages', pkg.family ?? null], 'local package checker rejected', {
        inner: compactReject0(out),
      });
    }
  }

  return validationAccept0({
    kind: 'LocalPackagesChecked0NF',
    packageCount: pack.Packages.length,
  });
}

function validateGlobalTheoremAlignment0(pack) {
  const theoremSet = new Set(pack.Packages.map((entry) => String(entry.theorem)));

  for (const theorem of GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0) {
    if (!theoremSet.has(theorem)) {
      return validationReject0(['Packages', 'theorems', theorem], 'LocalPackages0 is missing a global package theorem', {
        theorem,
      });
    }
  }

  return validationAccept0({
    kind: 'LocalPackageGlobalTheoremAlignment0NF',
    theoremCount: GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0.length,
  });
}

function validateLocalPackageLedgers0(pack) {
  if (!isPlainObject(pack.ImportLedger)) {
    return validationReject0(['ImportLedger'], 'ImportLedger must be an object', null);
  }

  if (pack.ImportLedger.acyclic !== true) {
    return validationReject0(['ImportLedger', 'acyclic'], 'ImportLedger must be acyclic', null);
  }

  if (!isPlainObject(pack.BoundsLedger)) {
    return validationReject0(['BoundsLedger'], 'BoundsLedger must be an object', null);
  }

  if (pack.BoundsLedger.finite !== true || pack.BoundsLedger.polynomial !== true) {
    return validationReject0(['BoundsLedger'], 'BoundsLedger must enforce finite polynomial bounds', {
      finite: pack.BoundsLedger.finite,
      polynomial: pack.BoundsLedger.polynomial,
    });
  }

  if (!isPlainObject(pack.NoMinLedger)) {
    return validationReject0(['NoMinLedger'], 'NoMinLedger must be an object', null);
  }

  if (!arrayContainsAll0(pack.NoMinLedger.expanded, LOCAL_PACKAGE_EXPANSION_STAGES0)) {
    return validationReject0(['NoMinLedger', 'expanded'], 'NoMinLedger must expand macros, aliases, generated templates, and imports', {
      actual: pack.NoMinLedger.expanded,
    });
  }

  if (!arrayContainsAll0(pack.NoMinLedger.forbiddenSymbols, LOCAL_PACKAGE_FORBIDDEN_EXEC_SYMBOLS0)) {
    return validationReject0(['NoMinLedger', 'forbiddenSymbols'], 'NoMinLedger is missing a forbidden executable symbol', {
      actual: pack.NoMinLedger.forbiddenSymbols,
    });
  }

  if (!isPlainObject(pack.ReflectionLedger)) {
    return validationReject0(['ReflectionLedger'], 'ReflectionLedger must be an object', null);
  }

  for (const field of ['exact', 'publicConclusion', 'replayable']) {
    if (pack.ReflectionLedger[field] !== true) {
      return validationReject0(['ReflectionLedger', field], `ReflectionLedger must enforce ${field}`, {
        actual: pack.ReflectionLedger[field],
      });
    }
  }

  return validationAccept0({
    kind: 'LocalPackageLedgers0NF',
  });
}

function validateLocalPackageShape0(pkg) {
  if (!isPlainObject(pkg)) {
    return validationReject0([], 'LocalPackage0 must be an object', {
      actual: typeof pkg,
    });
  }

  if (pkg.kind !== undefined && pkg.kind !== 'LocalPackage0') {
    return validationReject0(['kind'], 'LocalPackage0 kind must be LocalPackage0 when present', {
      actual: pkg.kind,
    });
  }

  if (pkg.version !== undefined && pkg.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `LocalPackage0 version must be ${CHECKER_VERSION} when present`, {
      actual: pkg.version,
    });
  }

  for (const field of [
    'family',
    'packageId',
    'batchId',
    'schemaId',
    'kindKey',
    'theorem',
    'checkerId',
    'imports',
    'rowRefs',
    'contracts',
    'routes',
    'proof',
    'bounds',
    'noHiddenMin',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(pkg, field)) {
      return validationReject0([field], 'LocalPackage0 is missing a required field', {
        field,
      });
    }
  }

  return validationAccept0({
    kind: 'LocalPackageShape0NF',
  });
}

function validateLocalPackageIdentity0(pkg) {
  const requirement = requirementByFamily0(pkg.family);

  if (requirement === null) {
    return validationReject0(['family'], 'LocalPackage0 family is unknown', {
      family: pkg.family,
    });
  }

  const checks = [
    ['packageId', requirement.packageId],
    ['batchId', requirement.batchId],
    ['schemaId', requirement.schemaId],
    ['kindKey', requirement.kindKey],
    ['arityKey', requirement.arityKey],
    ['payloadKey', requirement.payloadKey],
    ['theorem', requirement.theorem],
  ];

  for (const [field, expected] of checks) {
    if (pkg[field] !== expected) {
      return validationReject0([field], 'LocalPackage0 identity field mismatch', {
        field,
        expected,
        actual: pkg[field],
      });
    }
  }

  if (pkg.checkerId !== `CheckRowFam${safeId0(pkg.family)}0`) {
    return validationReject0(['checkerId'], 'LocalPackage0 checkerId mismatch', {
      expected: `CheckRowFam${safeId0(pkg.family)}0`,
      actual: pkg.checkerId,
    });
  }

  return validationAccept0({
    kind: 'LocalPackageIdentity0NF',
    family: pkg.family,
  });
}

function validateLocalPackageContracts0(pkg) {
  const requirement = requirementByFamily0(pkg.family);

  if (!Array.isArray(pkg.contracts)) {
    return validationReject0(['contracts'], 'LocalPackage0 contracts must be an array', null);
  }

  const accepted = new Set();

  for (let index = 0; index < pkg.contracts.length; index += 1) {
    const entry = pkg.contracts[index];

    if (!isPlainObject(entry)) {
      return validationReject0(['contracts', index], 'contract entry must be an object', {
        actual: typeof entry,
      });
    }

    if (!isNonEmptyString(entry.name)) {
      return validationReject0(['contracts', index, 'name'], 'contract entry must have a non-empty name', {
        actual: entry.name,
      });
    }

    if (entry.accepted !== true) {
      return validationReject0(['contracts', index, 'accepted'], 'contract entry must be accepted', {
        contract: entry.name,
        actual: entry.accepted,
      });
    }

    accepted.add(entry.name);
  }

  for (const contract of requirement.contracts) {
    if (!accepted.has(contract)) {
      return validationReject0(['contracts', contract], 'LocalPackage0 is missing a required local contract', {
        family: pkg.family,
        contract,
      });
    }
  }

  return validationAccept0({
    kind: 'LocalPackageContracts0NF',
    contractCount: requirement.contracts.length,
  });
}

function validateLocalPackageRowRefs0(pkg) {
  const requirement = requirementByFamily0(pkg.family);

  if (!Array.isArray(pkg.rowRefs)) {
    return validationReject0(['rowRefs'], 'LocalPackage0 rowRefs must be an array', null);
  }

  const hit = pkg.rowRefs.find((entry) => (
    isPlainObject(entry) &&
    entry.batchId === requirement.batchId &&
    entry.family === requirement.family &&
    entry.packageId === requirement.packageId &&
    entry.schemaId === requirement.schemaId &&
    entry.kindKey === requirement.kindKey
  ));

  if (hit === undefined) {
    return validationReject0(['rowRefs'], 'LocalPackage0 is missing its generated row-family reference', {
      family: requirement.family,
      batchId: requirement.batchId,
      packageId: requirement.packageId,
      schemaId: requirement.schemaId,
      kindKey: requirement.kindKey,
    });
  }

  return validationAccept0({
    kind: 'LocalPackageRowRefs0NF',
    rowRefCount: pkg.rowRefs.length,
  });
}

function validateLocalPackageRoutes0(pkg) {
  if (!isPlainObject(pkg.routes)) {
    return validationReject0(['routes'], 'LocalPackage0 routes must be an object', {
      actual: typeof pkg.routes,
    });
  }

  for (const field of [
    'highestPriority',
    'constructiveRoutesCompileToVerifyDW',
    'exactRoutesAccepted',
    'descentRanks',
  ]) {
    if (pkg.routes[field] !== true) {
      return validationReject0(['routes', field], `LocalPackage0 routes must enforce ${field}`, {
        family: pkg.family,
        actual: pkg.routes[field],
      });
    }
  }

  const entries = pkg.routes.entries ?? pkg.routes.routeEntries ?? [];

  if (!Array.isArray(entries)) {
    return validationReject0(['routes', 'entries'], 'LocalPackage0 route entries must be an array when present', null);
  }

  for (let index = 0; index < entries.length; index += 1) {
    const route = entries[index];

    if (!isPlainObject(route)) {
      return validationReject0(['routes', 'entries', index], 'route entry must be an object', {
        actual: typeof route,
      });
    }

    if (route.kind === 'Gain' && route.verifyDWAccepted !== true) {
      return validationReject0(['routes', 'entries', index, 'verifyDWAccepted'], 'constructive Gain routes must compile to VerifyDW acceptance', {
        family: pkg.family,
      });
    }

    if (route.kind === 'ExactRoute' && route.exactCertificateAccepted !== true) {
      return validationReject0(['routes', 'entries', index, 'exactCertificateAccepted'], 'ExactRoute entries must carry accepted exact certificates', {
        family: pkg.family,
      });
    }

    if (route.kind === 'Descent') {
      if (route.rankDecreases !== true) {
        return validationReject0(['routes', 'entries', index, 'rankDecreases'], 'Descent route entries must certify rank decrease', {
          family: pkg.family,
        });
      }

      if (Array.isArray(route.rankBefore) && Array.isArray(route.rankAfter)) {
        if (compareLexRank0(route.rankAfter, route.rankBefore) >= 0) {
          return validationReject0(['routes', 'entries', index, 'rankAfter'], 'Descent rankAfter must be smaller than rankBefore', {
            family: pkg.family,
            rankBefore: route.rankBefore,
            rankAfter: route.rankAfter,
          });
        }
      }
    }
  }

  return validationAccept0({
    kind: 'LocalPackageRoutes0NF',
    routeEntryCount: entries.length,
  });
}

function validateLocalPackageProof0(pkg) {
  if (!isPlainObject(pkg.proof)) {
    return validationReject0(['proof'], 'LocalPackage0 proof must be an object', {
      actual: typeof pkg.proof,
    });
  }

  for (const field of [
    'typed',
    'acyclic',
    'modeSafe',
    'hashIndependent',
    'reflectionAccepted',
  ]) {
    if (pkg.proof[field] !== true) {
      return validationReject0(['proof', field], `LocalPackage0 proof must enforce ${field}`, {
        family: pkg.family,
        actual: pkg.proof[field],
      });
    }
  }

  if (pkg.proof.publicConclusion === undefined) {
    return validationReject0(['proof', 'publicConclusion'], 'LocalPackage0 proof must expose a public conclusion', {
      family: pkg.family,
    });
  }

  return validationAccept0({
    kind: 'LocalPackageProof0NF',
  });
}

function validateLocalPackageBounds0(pkg) {
  if (!isPlainObject(pkg.bounds)) {
    return validationReject0(['bounds'], 'LocalPackage0 bounds must be an object', {
      actual: typeof pkg.bounds,
    });
  }

  if (pkg.bounds.finite !== true) {
    return validationReject0(['bounds', 'finite'], 'LocalPackage0 bounds must be finite', {
      family: pkg.family,
      actual: pkg.bounds.finite,
    });
  }

  if (pkg.bounds.polynomial !== true) {
    return validationReject0(['bounds', 'polynomial'], 'LocalPackage0 bounds must be polynomial', {
      family: pkg.family,
      actual: pkg.bounds.polynomial,
    });
  }

  if (!Number.isInteger(pkg.bounds.exponent) || pkg.bounds.exponent <= 0) {
    return validationReject0(['bounds', 'exponent'], 'LocalPackage0 bounds exponent must be positive', {
      family: pkg.family,
      actual: pkg.bounds.exponent,
    });
  }

  return validationAccept0({
    kind: 'LocalPackageBounds0NF',
    exponent: pkg.bounds.exponent,
  });
}

function validateLocalPackageNoMinMetadata0(pkg) {
  if (!isPlainObject(pkg.noHiddenMin)) {
    return validationReject0(['noHiddenMin'], 'LocalPackage0 noHiddenMin metadata must be an object', {
      actual: typeof pkg.noHiddenMin,
    });
  }

  if (!arrayContainsAll0(pkg.noHiddenMin.expanded, LOCAL_PACKAGE_EXPANSION_STAGES0)) {
    return validationReject0(['noHiddenMin', 'expanded'], 'LocalPackage0 noHiddenMin must expand macros, aliases, generated templates, and imports', {
      actual: pkg.noHiddenMin.expanded,
    });
  }

  if (!arrayContainsAll0(pkg.noHiddenMin.forbiddenSymbols, LOCAL_PACKAGE_FORBIDDEN_EXEC_SYMBOLS0)) {
    return validationReject0(['noHiddenMin', 'forbiddenSymbols'], 'LocalPackage0 noHiddenMin is missing a forbidden executable symbol', {
      actual: pkg.noHiddenMin.forbiddenSymbols,
    });
  }

  return validationAccept0({
    kind: 'LocalPackageNoMinMetadata0NF',
  });
}

function validateNoHiddenExecutableMin0(value, path) {
  const hit = findForbiddenExecutableUse0(value, path, false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'LocalNoHiddenExecutableMin0NF',
  });
}

function validateNoOpaqueProof0(value, path) {
  const hit = findOpaqueProof0(value, path);

  if (hit !== null) {
    return validationReject0(hit.path, 'opaque proof material is not allowed in local packages', hit);
  }

  return validationAccept0({
    kind: 'LocalNoOpaqueProof0NF',
  });
}

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && LOCAL_PACKAGE_FORBIDDEN_EXEC_SYMBOLS0.includes(value)) {
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

function normalizeRequirement0(requirement) {
  if (typeof requirement === 'string') {
    const found = requirementByFamily0(requirement);

    if (found === null) {
      throw new TypeError(`unknown local package family: ${requirement}`);
    }

    return found;
  }

  if (isPlainObject(requirement)) {
    return requirement;
  }

  throw new TypeError('makeLocalPackage0 requires a requirement object or family string');
}

function requirementByFamily0(family) {
  return LOCAL_PACKAGE_REQUIREMENTS0.find((entry) => entry.family === family) ?? null;
}

function packageMap0(packages) {
  const out = new Map();

  for (const pkg of packages) {
    if (isPlainObject(pkg) && isNonEmptyString(pkg.family)) {
      out.set(pkg.family, pkg);
    }
  }

  return out;
}

function getInventoryEntries0(packageInv) {
  if (Array.isArray(packageInv)) {
    return packageInv;
  }

  if (!isPlainObject(packageInv)) {
    return null;
  }

  return packageInv.entries ?? packageInv.Entries ?? packageInv.packages ?? packageInv.Packages;
}

function getPiLocalPackages0(pack) {
  return pack.PiLocalPackages ?? pack['Πlocal'] ?? pack.piLocalPackages;
}

function edgeKey0(edge) {
  if (Array.isArray(edge)) {
    return `${String(edge[0])}->${String(edge[1])}`;
  }

  if (isPlainObject(edge)) {
    return `${String(edge.from ?? edge.src)}->${String(edge.to ?? edge.dst)}`;
  }

  return String(edge);
}

function arrayContainsAll0(actual, required) {
  if (!Array.isArray(actual)) {
    return false;
  }

  return required.every((entry) => actual.includes(entry));
}

function compareLexRank0(a, b) {
  const n = Math.max(a.length, b.length);

  for (let index = 0; index < n; index += 1) {
    const aa = Number(a[index] ?? 0);
    const bb = Number(b[index] ?? 0);

    if (aa < bb) {
      return -1;
    }

    if (aa > bb) {
      return 1;
    }
  }

  return 0;
}

function safeId0(value) {
  return String(value).replace(/[^A-Za-z0-9_]/g, '');
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