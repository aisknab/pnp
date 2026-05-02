import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  BOOT_BATCH0_REQUIRED_ROWS,
  CheckBootBatch0,
  makeBootRow0,
  makeBootstrapB0Rows0,
} from './pcc-boot0.mjs';

import {
  CheckDuplicateRows0,
  CheckRowKey0,
  DigestObject0,
} from './pcc-core.mjs';

const CHECKER_VERSION = 0;

export const ROW_BATCH_IDS0 = Object.freeze([
  'B0',
  'B1',
  'B2',
  'B3',
  'B4',
  'B5',
  'B6',
  'B7',
  'B8',
  'B9',
  'B10',
  'B11',
  'B12',
]);

export const ROW_ROUTE_PRIORITY0 = Object.freeze([
  'Accept',
  'Gain',
  'Minimum',
  'ZeroSlack',
  'NoBudget',
  'NoHereditary',
  'SelectorSilent',
  'Faithful',
  'Token',
  'Neutral',
  'Reject',
]);

export const ROW_FORBIDDEN_IMPORT_EDGES0 = Object.freeze([
  Object.freeze(['BC', 'UN']),
  Object.freeze(['UN', 'BC']),
  Object.freeze(['BCEL', 'R']),
  Object.freeze(['BUD', 'R']),
  Object.freeze(['O', 'G']),
  Object.freeze(['G', 'O']),
]);

export const ROW_ALLOWED_PROOF_REF_KINDS0 = Object.freeze([
  'KPrimitive',
  'SigmaInstance',
  'ReflectionInstance',
  'EarlierRowProof',
  'ProofRef0',
]);

export const ROW_FAMILY_SPECS0 = Object.freeze([
  Object.freeze({
    batchId: 'B1',
    family: 'E',
    packageId: 'PE',
    schemaId: 'DirectWireVerifierRow',
    kindKey: 'direct-wire-verifier',
    arityKey: 3,
    payloadKey: 'PackageE.VerifyDW',
    purpose: 'direct-wire verifier and R1-R9 certificates',
    proofRule: 'Transport',
    bound: 'B1.E',
  }),
  Object.freeze({
    batchId: 'B1',
    family: 'N',
    packageId: 'PN',
    schemaId: 'TraceNormalizationRow',
    kindKey: 'trace-normalization',
    arityKey: 2,
    payloadKey: 'PackageN.NormalizeOrGain',
    purpose: 'traceable normalization',
    proofRule: 'TraceInd',
    bound: 'B1.N',
  }),
  Object.freeze({
    batchId: 'B1',
    family: 'Splice',
    packageId: 'PSplice',
    schemaId: 'SpliceAtlasRow',
    kindKey: 'splice-atlas',
    arityKey: 2,
    payloadKey: 'Splice.Atlas',
    purpose: 'bounded and composed splice atlases',
    proofRule: 'Transport',
    bound: 'B1.Splice',
  }),
  Object.freeze({
    batchId: 'B2',
    family: 'FT',
    packageId: 'PFT',
    schemaId: 'FiniteTableRow',
    kindKey: 'finite-table',
    arityKey: 4,
    payloadKey: 'FT.TableEngine',
    purpose: 'finite local table engine',
    proofRule: 'FiniteExhaust',
    bound: 'B2.FT',
  }),
  Object.freeze({
    batchId: 'B2',
    family: 'FTX',
    packageId: 'PFTX',
    schemaId: 'FiniteTableCriticalRow',
    kindKey: 'finite-table-critical',
    arityKey: 4,
    payloadKey: 'FTX.CriticalTables',
    purpose: 'finite critical-window table engine',
    proofRule: 'FiniteExhaust',
    bound: 'B2.FTX',
  }),
  Object.freeze({
    batchId: 'B2',
    family: 'X',
    packageId: 'PX',
    schemaId: 'CriticalWindowRow',
    kindKey: 'critical-window',
    arityKey: 4,
    payloadKey: 'X.CandidateTowers',
    purpose: 'CritC, Q, E, L and X1-X4 routing',
    proofRule: 'Hall',
    bound: 'B2.X',
  }),
  Object.freeze({
    batchId: 'B3',
    family: 'BC',
    packageId: 'PBC',
    schemaId: 'BranchCycleRow',
    kindKey: 'branch-cycle',
    arityKey: 4,
    payloadKey: 'BC.TransitionCategory',
    purpose: 'branch-cycle finite transition category',
    proofRule: 'FiniteRel',
    bound: 'B3.BC',
  }),
  Object.freeze({
    batchId: 'B3',
    family: 'UN',
    packageId: 'PUN',
    schemaId: 'UnaryDecoderRow',
    kindKey: 'unary-decoder',
    arityKey: 4,
    payloadKey: 'UN.BlockedIntervals',
    purpose: 'unary full/projected lift decoder',
    proofRule: 'DPInd',
    bound: 'B3.UN',
  }),
  Object.freeze({
    batchId: 'B3',
    family: 'HNShape',
    packageId: 'PHNShape',
    schemaId: 'HereditaryShapeTokenRow',
    kindKey: 'hereditary-shape-token',
    arityKey: 1,
    payloadKey: 'HNShape.Token',
    purpose: 'hereditary shape tokens',
    proofRule: 'Record',
    bound: 'B3.HNShape',
  }),
  Object.freeze({
    batchId: 'B4',
    family: 'HN',
    packageId: 'PHN',
    schemaId: 'HereditaryLeafRow',
    kindKey: 'hereditary-leaf',
    arityKey: 4,
    payloadKey: 'HN.LeafTightness',
    purpose: 'hereditary grammar and leaf tightness',
    proofRule: 'DPInd',
    bound: 'B4.HN',
  }),
  Object.freeze({
    batchId: 'B4',
    family: 'HResolve',
    packageId: 'PHResolve',
    schemaId: 'HereditaryResolverRow',
    kindKey: 'hereditary-resolver',
    arityKey: 3,
    payloadKey: 'HResolve.Sidecar',
    purpose: 'global hereditary resolver',
    proofRule: 'RankInd',
    bound: 'B4.HResolve',
  }),
  Object.freeze({
    batchId: 'B5',
    family: 'BUD',
    packageId: 'PBUD',
    schemaId: 'BudgetResolverRow',
    kindKey: 'budget-resolver',
    arityKey: 3,
    payloadKey: 'BUD.EnvelopeDP',
    purpose: 'budget resolver and envelope dynamic program',
    proofRule: 'DPInd',
    bound: 'B5.BUD',
  }),
  Object.freeze({
    batchId: 'B5',
    family: 'NORFF',
    packageId: 'PNORFF',
    schemaId: 'NeutralFrontierRow',
    kindKey: 'neutral-frontier',
    arityKey: 3,
    payloadKey: 'NORFF.FrontierFaithful',
    purpose: 'strong neutral overlay and FF-LOSS',
    proofRule: 'Transport',
    bound: 'B5.NORFF',
  }),
  Object.freeze({
    batchId: 'B5',
    family: 'RW',
    packageId: 'PRW',
    schemaId: 'ResidualWitnessRow',
    kindKey: 'residual-witness',
    arityKey: 4,
    payloadKey: 'RW.BCELReady',
    purpose: 'residual witness and BCEL-ready nuclei',
    proofRule: 'RankInd',
    bound: 'B5.RW',
  }),
  Object.freeze({
    batchId: 'B6',
    family: 'BN2',
    packageId: 'PBN2',
    schemaId: 'SideTightSquareRow',
    kindKey: 'side-tight-square',
    arityKey: 4,
    payloadKey: 'BN2.CoherentOptimum',
    purpose: 'side-tight coherent optima',
    proofRule: 'IntArith',
    bound: 'B6.BN2',
  }),
  Object.freeze({
    batchId: 'B6',
    family: 'BN3',
    packageId: 'PBN3',
    schemaId: 'RequestEnvelopeRow',
    kindKey: 'request-envelope',
    arityKey: 4,
    payloadKey: 'BN3.SimultaneousEnvelope',
    purpose: 'simultaneous finite request envelopes',
    proofRule: 'FiniteRel',
    bound: 'B6.BN3',
  }),
  Object.freeze({
    batchId: 'B7',
    family: 'BN4',
    packageId: 'PBN4',
    schemaId: 'ActivationCancellationRow',
    kindKey: 'activation-cancellation',
    arityKey: 4,
    payloadKey: 'BN4.ActivationExact',
    purpose: 'activation-exact cancellation',
    proofRule: 'FiniteRel',
    bound: 'B7.BN4',
  }),
  Object.freeze({
    batchId: 'B7',
    family: 'BN5',
    packageId: 'PBN5',
    schemaId: 'FullShadowLocalizationRow',
    kindKey: 'full-shadow-localization',
    arityKey: 4,
    payloadKey: 'BN5.FullShadow',
    purpose: 'full-shadow localization',
    proofRule: 'Hall',
    bound: 'B7.BN5',
  }),
  Object.freeze({
    batchId: 'B7',
    family: 'PkgC',
    packageId: 'PPkgC',
    schemaId: 'SeparatingConsumerRow',
    kindKey: 'separating-consumer',
    arityKey: 4,
    payloadKey: 'PkgC.SeparatingConsumers',
    purpose: 'separating consumer package',
    proofRule: 'Hall',
    bound: 'B7.PkgC',
  }),
  Object.freeze({
    batchId: 'B8',
    family: 'BN6',
    packageId: 'PBN6',
    schemaId: 'HypergraphPacketRow',
    kindKey: 'hypergraph-packet',
    arityKey: 4,
    payloadKey: 'BN6.HypergraphPacket',
    purpose: 'hypergraph cellization and packet collapse',
    proofRule: 'FiniteRel',
    bound: 'B8.BN6',
  }),
  Object.freeze({
    batchId: 'B8',
    family: 'Packet',
    packageId: 'PPacket',
    schemaId: 'SelectorSeedPacketRow',
    kindKey: 'selector-seed-packet',
    arityKey: 4,
    payloadKey: 'Packet.SelectorSeeds',
    purpose: 'pair, balanced-triple, and full-span selector seeds',
    proofRule: 'RankInd',
    bound: 'B8.Packet',
  }),
  Object.freeze({
    batchId: 'B9',
    family: 'R',
    packageId: 'PR',
    schemaId: 'SelectorRealizerRow',
    kindKey: 'selector-realizer',
    arityKey: 4,
    payloadKey: 'R.Realizer',
    purpose: 'selector blueprint realization',
    proofRule: 'Transport',
    bound: 'B9.R',
  }),
  Object.freeze({
    batchId: 'B9',
    family: 'HB',
    packageId: 'PHB',
    schemaId: 'HereditaryBudgetBlockerRow',
    kindKey: 'hereditary-budget-blocker',
    arityKey: 4,
    payloadKey: 'HB.BlockerGraph',
    purpose: 'simultaneous HN-BUD negative closure',
    proofRule: 'DAGInd',
    bound: 'B9.HB',
  }),
  Object.freeze({
    batchId: 'B10',
    family: 'O',
    packageId: 'PO',
    schemaId: 'OracleRow',
    kindKey: 'oracle',
    arityKey: 4,
    payloadKey: 'O.PCCOracle',
    purpose: 'rank-ordered oracle and ZeroSlack',
    proofRule: 'RankInd',
    bound: 'B10.O',
  }),
  Object.freeze({
    batchId: 'B11',
    family: 'G',
    packageId: 'PG',
    schemaId: 'LockedNANDRow',
    kindKey: 'locked-nand',
    arityKey: 4,
    payloadKey: 'G.LockedNAND',
    purpose: 'locked NAND SAT embedding',
    proofRule: 'TruthVec',
    bound: 'B11.G',
  }),
  Object.freeze({
    batchId: 'B12',
    family: 'Final',
    packageId: 'PFinal',
    schemaId: 'FinalFrameworkMatchRow',
    kindKey: 'final-framework-match',
    arityKey: 4,
    payloadKey: 'Final.FrameworkMatch',
    purpose: 'final framework match and SAT decision',
    proofRule: 'Transport',
    bound: 'B12.Final',
  }),
  Object.freeze({
    batchId: 'B12',
    family: 'PACK',
    packageId: 'PPACK',
    schemaId: 'PackageSufficiencyRow',
    kindKey: 'package-sufficiency',
    arityKey: 4,
    payloadKey: 'PACK.Sufficiency',
    purpose: 'top-level generated package sufficiency',
    proofRule: 'MinCounterexample',
    bound: 'B12.PACK',
  }),
]);

export const ROW_REQUIRED_FAMILY_SPECS0 = Object.freeze([
  ...BOOT_BATCH0_REQUIRED_ROWS.map((spec) => Object.freeze({
    batchId: 'B0',
    family: spec.family,
    packageId: spec.packageId,
    schemaId: spec.schemaId,
    kindKey: spec.kindKey,
    arityKey: spec.arityKey,
    payloadKey: spec.payloadKey,
    purpose: spec.purpose,
    proofRule: spec.proofRule,
    bound: spec.bound,
  })),
  ...ROW_FAMILY_SPECS0,
]);

export const ROW_REQUIRED_FAMILIES0 = Object.freeze(
  ROW_REQUIRED_FAMILY_SPECS0.map((spec) => spec.family)
);

const DEFAULT_BATCH_IMPORTS0 = Object.freeze({
  B0: Object.freeze([]),
  B1: Object.freeze(['B0']),
  B2: Object.freeze(['B1']),
  B3: Object.freeze(['B2']),
  B4: Object.freeze(['B3']),
  B5: Object.freeze(['B4']),
  B6: Object.freeze(['B5']),
  B7: Object.freeze(['B6']),
  B8: Object.freeze(['B7']),
  B9: Object.freeze(['B8']),
  B10: Object.freeze(['B9']),
  B11: Object.freeze(['B0']),
  B12: Object.freeze(['B10', 'B11']),
});

export const ROW_BATCH_SPECS0 = Object.freeze(
  ROW_BATCH_IDS0.map((batchId) => Object.freeze({
    batchId,
    index: Number(batchId.slice(1)),
    imports: DEFAULT_BATCH_IMPORTS0[batchId],
    families: ROW_REQUIRED_FAMILY_SPECS0
      .filter((spec) => spec.batchId === batchId)
      .map((spec) => spec.family),
  }))
);

const ROWPACK_REQUIRED_FIELDS0 = Object.freeze([
  'SchedHash',
  'IfaceHash',
  'SchemaInv',
  'BatchInv',
  'Rows',
  'NFMap',
  'HashIndex',
  'DupLedger',
  'CoverageLedger',
  'RouteLedger',
  'ProofRefLedger',
  'BoundsLedger',
]);

const ROW_REQUIRED_FIELDS0 = Object.freeze([
  'BatchID',
  'FamilyID',
  'PackageID',
  'SchemaID',
  'RawObj',
  'NormObj',
  'RowKey',
  'TransportProof',
  'CandidateRoutes',
  'ActiveRouteSet',
  'SelectedRoute',
  'ProofRef',
  'BoundsRef',
  'HashKey',
]);

const FORBIDDEN_EXECUTABLE_SYMBOLS0 = Object.freeze([
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

export function makeB0RowPackRows0() {
  const b0Rows = makeBootstrapB0Rows0();

  return b0Rows.map((row, index) => ({
    ...row,
    BatchID: 'B0',
    FamilyID: BOOT_BATCH0_REQUIRED_ROWS[index].family,
    RowFamily: BOOT_BATCH0_REQUIRED_ROWS[index].family,
    ImportRefs: [],
  }));
}

export function makeGeneratedRow0(spec, {
  IfaceHash = 'IfaceDict0.synthetic',
  SelectedRoute = 'Accept',
} = {}) {
  const rawObj = {
    tag: 'GeneratedRow0',
    batchId: spec.batchId,
    family: spec.family,
    packageId: spec.packageId,
    schemaId: spec.schemaId,
    purpose: spec.purpose,
    proofRule: spec.proofRule,
    bound: spec.bound,
  };

  const row = makeBootRow0({
    IfaceHash,
    PackageID: spec.packageId,
    SchemaID: spec.schemaId,
    KindKey: spec.kindKey,
    ArityKey: spec.arityKey,
    ModeKey: 'Full',
    PayloadKey: spec.payloadKey,
    RawObj: rawObj,
    NormObj: {
      ...rawObj,
      normalized: true,
    },
    TransportProof: {
      tag: 'TransportProof0',
      kind: 'identity',
      family: spec.family,
    },
    CandidateRoutes: [SelectedRoute],
    ActiveRouteSet: [SelectedRoute],
    SelectedRoute,
    ProofRef: {
      tag: 'ProofRef0',
      refKind: 'KPrimitive',
      id: `${spec.batchId}.${spec.family}.proof`,
      rule: spec.proofRule,
    },
    BoundsRef: {
      tag: 'BoundsRef0',
      id: `${spec.batchId}.${spec.family}.bounds`,
      bound: spec.bound,
      polynomial: true,
    },
  });

  return {
    ...row,
    BatchID: spec.batchId,
    FamilyID: spec.family,
    RowFamily: spec.family,
    ImportRefs: DEFAULT_BATCH_IMPORTS0[spec.batchId] ?? [],
  };
}

export function makeGeneratedPackageRows0(options = {}) {
  return ROW_FAMILY_SPECS0.map((spec) => makeGeneratedRow0(spec, options));
}

export function makeSchemaInventory0() {
  return {
    kind: 'SchemaInventory0',
    version: CHECKER_VERSION,
    schemas: ROW_REQUIRED_FAMILY_SPECS0.map((spec) => ({
      family: spec.family,
      batchId: spec.batchId,
      PackageID: spec.packageId,
      SchemaID: spec.schemaId,
      KindKey: spec.kindKey,
      ArityKey: spec.arityKey,
      PayloadKey: spec.payloadKey,
    })),
  };
}

export function makeBatchInventory0() {
  return {
    kind: 'BatchInventory0',
    version: CHECKER_VERSION,
    batches: ROW_BATCH_SPECS0.map((spec) => ({
      kind: 'BatchInvEntry0',
      batchId: spec.batchId,
      index: spec.index,
      imports: [...spec.imports],
      families: [...spec.families],
    })),
  };
}

export function makeSyntheticRowPack0(overrides = {}) {
  const rows = [
    ...makeB0RowPackRows0(),
    ...makeGeneratedPackageRows0(),
  ];

  const rowPack = {
    kind: 'RowPack0',
    version: CHECKER_VERSION,
    SchedHash: {
      alg: 'SHA256',
      hex: '6bb960d1e8414fe1044625c0fd549f0d05a5a3aadccb806c461847b5ab21fdac',
    },
    IfaceHash: {
      alg: 'SHA256',
      hex: '12384535df3bb742e73236a20a9a8ee47949f7273e77020aecb60b90e9ab7502',
    },
    SchemaInv: makeSchemaInventory0(),
    BatchInv: makeBatchInventory0(),
    Rows: rows,
    NFMap: makeNFMap0(rows),
    HashIndex: makeHashIndex0(rows),
    DupLedger: makeDupLedger0(rows),
    CoverageLedger: makeCoverageLedger0(rows),
    RouteLedger: makeRouteLedger0(rows),
    ProofRefLedger: makeProofRefLedger0(rows),
    BoundsLedger: makeBoundsLedger0(rows),
    PiRows: {
      kind: 'PiRows0',
      version: CHECKER_VERSION,
      note: 'synthetic row-package proof marker',
    },
  };

  return {
    ...rowPack,
    ...overrides,
  };
}

export async function CheckRows0(rowPack) {
  const checker = 'CheckRows0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateRowPackShape0(rowPack)],
    ['schemaInv', `${checker}.schemaInv`, () => validateSchemaInventory0(rowPack.SchemaInv)],
    ['batchDeps', `${checker}.batchDeps`, async () => recordToValidation0(await CheckBatchDeps0(rowPack.BatchInv))],
    ['rows', `${checker}.rows`, () => validateRows0(rowPack.Rows)],
    ['bootBatch', `${checker}.bootBatch`, async () => validateBootBatchRows0(rowPack.Rows)],
    ['duplicates', `${checker}.duplicates`, () => validateDuplicateRows0(rowPack.Rows)],
    ['families', `${checker}.families`, async () => recordToValidation0(await CheckRowFamilies0(rowPack))],
    ['routes', `${checker}.routes`, () => validateRouteLedger0(rowPack)],
    ['proofRefs', `${checker}.proofRefs`, () => validateProofRefLedger0(rowPack)],
    ['hashIndex', `${checker}.hashIndex`, () => validateHashIndex0(rowPack)],
    ['bounds', `${checker}.bounds`, () => validateBoundsLedger0(rowPack)],
    ['noHiddenMin', `${checker}.noHiddenMin`, () => validateNoHiddenMin0(rowPack)],
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

  const rows = rowPack.Rows;

  const nf = {
    kind: 'RowPack0NF',
    checker,
    version: CHECKER_VERSION,
    rowCount: rows.length,
    batchCount: ROW_BATCH_IDS0.length,
    familyCount: ROW_REQUIRED_FAMILIES0.length,
    batches: ROW_BATCH_IDS0,
    families: ROW_REQUIRED_FAMILIES0,
    packages: sortedUnique0(rows.map((row) => row.PackageID)),
    schemas: sortedUnique0(rows.map((row) => `${row.PackageID}:${row.SchemaID}`)),
    rowDigests: rows.map((row, index) => ({
      index,
      batchId: row.BatchID,
      family: row.FamilyID,
      packageId: row.PackageID,
      schemaId: row.SchemaID,
      selectedRoute: row.SelectedRoute,
      rowKeyDigest: digestCanonical0(row.RowKey),
      hashKey: row.HashKey,
    })),
    piRowsDigest: digestCanonical0(getPiRows0(rowPack)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckBatchDeps0(batchInv) {
  const checker = 'CheckBatchDeps0';
  const ledger = [];

  const result = validateBatchDeps0(batchInv);

  ledger.push({
    phase: result.phase ?? 'batchDeps',
    status: result.ok ? 'pass' : 'fail',
    digest: digestCanonical0(result.nf ?? result.witness ?? null),
  });

  if (!result.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.${result.coordSuffix ?? 'input'}`,
      path: result.path,
      witness: result.witness,
      ledger,
    });
  }

  return makeAcceptRecord({
    checker,
    nf: result.nf,
    ledger,
  });
}

export async function CheckRowFamilies0(rowPack) {
  const checker = 'CheckRowFamilies0';
  const ledger = [];

  const result = validateFamilyCoverage0(rowPack);

  ledger.push({
    phase: 'coverage',
    status: result.ok ? 'pass' : 'fail',
    digest: digestCanonical0(result.nf ?? result.witness ?? null),
  });

  if (!result.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.coverage`,
      path: result.path,
      witness: result.witness,
      ledger,
    });
  }

  return makeAcceptRecord({
    checker,
    nf: result.nf,
    ledger,
  });
}

function validateRowPackShape0(rowPack) {
  if (!isPlainObject(rowPack)) {
    return validationReject0([], 'RowPack0 must be an object', {
      actual: typeof rowPack,
    });
  }

  if (rowPack.kind !== undefined && rowPack.kind !== 'RowPack0') {
    return validationReject0(['kind'], 'RowPack0 kind must be RowPack0 when present', {
      actual: rowPack.kind,
    });
  }

  if (rowPack.version !== undefined && rowPack.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `RowPack0 version must be ${CHECKER_VERSION} when present`, {
      actual: rowPack.version,
    });
  }

  for (const field of ROWPACK_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(rowPack, field)) {
      return validationReject0([field], 'RowPack0 is missing a required field', {
        field,
      });
    }
  }

  if (getPiRows0(rowPack) === undefined) {
    return validationReject0(['PiRows'], 'RowPack0 is missing PiRows or Πrows', null);
  }

  if (!Array.isArray(rowPack.Rows)) {
    return validationReject0(['Rows'], 'RowPack0 Rows must be an array', {
      actual: typeof rowPack.Rows,
    });
  }

  return validationAccept0({
    kind: 'RowPackShape0NF',
  });
}

function validateSchemaInventory0(schemaInv) {
  const entries = getSchemaEntries0(schemaInv);

  if (!Array.isArray(entries)) {
    return validationReject0(['SchemaInv'], 'SchemaInv must provide a schemas array', {
      actual: typeof entries,
    });
  }

  const seen = new Set();

  for (let index = 0; index < entries.length; index += 1) {
    const entry = entries[index];

    if (!isPlainObject(entry)) {
      return validationReject0(['SchemaInv', 'schemas', index], 'schema inventory entry must be an object', {
        actual: typeof entry,
      });
    }

    const key = schemaKey0(entry.PackageID ?? entry.packageId, entry.SchemaID ?? entry.schemaId);

    if (seen.has(key)) {
      return validationReject0(['SchemaInv', 'schemas', index], 'schema inventory entries must be unique', {
        key,
      });
    }

    seen.add(key);
  }

  for (const spec of ROW_REQUIRED_FAMILY_SPECS0) {
    const key = schemaKey0(spec.packageId, spec.schemaId);

    if (!seen.has(key)) {
      return validationReject0(['SchemaInv', 'coverage', spec.family], 'SchemaInv is missing a required row-family schema', {
        family: spec.family,
        packageId: spec.packageId,
        schemaId: spec.schemaId,
      });
    }
  }

  return validationAccept0({
    kind: 'SchemaInventory0NF',
    schemaCount: entries.length,
    requiredFamilyCount: ROW_REQUIRED_FAMILIES0.length,
  });
}

function validateBatchDeps0(batchInv) {
  const entries = getBatchEntries0(batchInv);

  if (!Array.isArray(entries)) {
    return validationRejectWithCoord0('input', ['BatchInv'], 'BatchInv must provide a batches array', {
      actual: typeof entries,
    });
  }

  const byId = new Map();

  for (let index = 0; index < entries.length; index += 1) {
    const entry = entries[index];

    if (!isPlainObject(entry)) {
      return validationRejectWithCoord0('input', ['BatchInv', index], 'batch inventory entry must be an object', {
        actual: typeof entry,
      });
    }

    const batchId = entry.batchId ?? entry.BatchID ?? entry.id;

    if (!ROW_BATCH_IDS0.includes(batchId)) {
      return validationRejectWithCoord0('input', ['BatchInv', index, 'batchId'], 'unknown batch id', {
        batchId,
      });
    }

    if (byId.has(batchId)) {
      return validationRejectWithCoord0('input', ['BatchInv', index, 'batchId'], 'batch ids must be unique', {
        batchId,
      });
    }

    byId.set(batchId, {
      ...entry,
      batchId,
      index: entry.index ?? Number(String(batchId).slice(1)),
      imports: normalizeImportList0(entry.imports ?? entry.deps ?? entry.dependsOn ?? []),
      families: normalizeFamilyList0(entry.families ?? entry.Families ?? familiesForBatch0(batchId)),
    });
  }

  for (const batchId of ROW_BATCH_IDS0) {
    if (!byId.has(batchId)) {
      return validationRejectWithCoord0('coverage', ['BatchInv', 'coverage', batchId], 'BatchInv is missing a required batch', {
        batchId,
      });
    }
  }

  for (const [batchId, entry] of byId.entries()) {
    const batchIndex = Number(batchId.slice(1));

    for (let importIndex = 0; importIndex < entry.imports.length; importIndex += 1) {
      const dep = entry.imports[importIndex];

      if (!byId.has(dep)) {
        return validationRejectWithCoord0('imports', ['BatchInv', batchId, 'imports', importIndex], 'batch import references an unknown batch', {
          batchId,
          dep,
        });
      }

      const depIndex = Number(String(dep).slice(1));

      if (depIndex >= batchIndex) {
        return validationRejectWithCoord0('acyclic', ['BatchInv', batchId, 'imports', importIndex], 'batch imports must point to earlier batches', {
          batchId,
          dep,
        });
      }

      const forbidden = firstForbiddenFamilyEdge0(entry.families, byId.get(dep).families);

      if (forbidden !== null) {
        return validationRejectWithCoord0('imports', ['BatchInv', batchId, 'imports', importIndex], 'batch import uses a forbidden package edge', {
          batchId,
          dep,
          edge: forbidden,
        });
      }
    }
  }

  return {
    ok: true,
    phase: 'batchDeps',
    nf: {
      kind: 'BatchDeps0NF',
      batchCount: ROW_BATCH_IDS0.length,
      batches: ROW_BATCH_IDS0.map((batchId) => ({
        batchId,
        index: byId.get(batchId).index,
        imports: byId.get(batchId).imports,
        families: byId.get(batchId).families,
      })),
    },
  };
}

function validateRows0(rows) {
  if (!Array.isArray(rows)) {
    return validationReject0(['Rows'], 'Rows must be an array', {
      actual: typeof rows,
    });
  }

  if (rows.length === 0) {
    return validationReject0(['Rows'], 'Rows must be non-empty', null);
  }

  for (let index = 0; index < rows.length; index += 1) {
    const row = rows[index];

    if (!isPlainObject(row)) {
      return validationReject0(['Rows', index], 'row must be an object', {
        actual: typeof row,
      });
    }

    for (const field of ROW_REQUIRED_FIELDS0) {
      if (!Object.prototype.hasOwnProperty.call(row, field)) {
        return validationReject0(['Rows', index, field], 'row is missing a required field', {
          field,
        });
      }
    }

    if (!ROW_BATCH_IDS0.includes(row.BatchID)) {
      return validationReject0(['Rows', index, 'BatchID'], 'row BatchID is unknown', {
        actual: row.BatchID,
      });
    }

    if (!isNonEmptyString(row.FamilyID)) {
      return validationReject0(['Rows', index, 'FamilyID'], 'row FamilyID must be a non-empty string', {
        actual: row.FamilyID,
      });
    }

    if (!Array.isArray(row.CandidateRoutes)) {
      return validationReject0(['Rows', index, 'CandidateRoutes'], 'CandidateRoutes must be an array', null);
    }

    if (!Array.isArray(row.ActiveRouteSet)) {
      return validationReject0(['Rows', index, 'ActiveRouteSet'], 'ActiveRouteSet must be an array', null);
    }

    if (!row.ActiveRouteSet.some((route) => stableStringify0(route) === stableStringify0(row.SelectedRoute))) {
      return validationReject0(['Rows', index, 'SelectedRoute'], 'SelectedRoute must be active', {
        selectedRoute: row.SelectedRoute,
        activeRouteSet: row.ActiveRouteSet,
      });
    }

    const rowKeyResult = CheckRowKey0(row, row.RowKey);

    if (isRejectRecord0(rowKeyResult)) {
      return validationReject0(['Rows', index, 'RowKey'], 'row key check rejected', {
        inner: compactReject0(rowKeyResult),
      });
    }

    const expectedHashKey = DigestObject0(row.RowKey);

    if (!isPlainObject(row.HashKey) || row.HashKey.hex !== expectedHashKey.hex) {
      return validationReject0(['Rows', index, 'HashKey'], 'HashKey must be the digest of RowKey', {
        expected: expectedHashKey,
        actual: row.HashKey,
      });
    }
  }

  return validationAccept0({
    kind: 'Rows0NF',
    rowCount: rows.length,
  });
}

async function validateBootBatchRows0(rows) {
  const b0Rows = rows.filter((row) => row.BatchID === 'B0');
  const out = await CheckBootBatch0({
    kind: 'BootBatch0',
    version: CHECKER_VERSION,
    batchId: 'B0',
    rows: b0Rows,
  });

  if (isRejectRecord0(out)) {
    return validationReject0(['Rows', 'B0'], 'B0 boot batch rejected', {
      inner: compactReject0(out),
    });
  }

  return validationAccept0({
    kind: 'BootBatchRows0NF',
    b0RowCount: b0Rows.length,
    digest: out.Digest,
  });
}

function validateDuplicateRows0(rows) {
  const out = CheckDuplicateRows0(rows);

  if (isRejectRecord0(out)) {
    return validationReject0(['Rows', 'duplicates'], 'duplicate row conflict', {
      inner: compactReject0(out),
    });
  }

  return validationAccept0({
    kind: 'DuplicateRows0NF',
    rowCount: rows.length,
  });
}

function validateFamilyCoverage0(rowPack) {
  if (!isPlainObject(rowPack) || !Array.isArray(rowPack.Rows)) {
    return validationReject0(['Rows'], 'RowPack0 must provide Rows for family coverage', null);
  }

  const rows = rowPack.Rows;
  const covered = new Map();

  for (let index = 0; index < rows.length; index += 1) {
    const row = rows[index];

    if (isPlainObject(row) && isNonEmptyString(row.FamilyID) && !covered.has(row.FamilyID)) {
      covered.set(row.FamilyID, {
        index,
        row,
      });
    }
  }

  for (const spec of ROW_REQUIRED_FAMILY_SPECS0) {
    const direct = covered.get(spec.family);

    if (direct === undefined || !rowMatchesFamilySpec0(direct.row, spec)) {
      return validationReject0(['Rows', 'coverage', spec.family], 'RowPack0 is missing a required row family', {
        family: spec.family,
        batchId: spec.batchId,
        packageId: spec.packageId,
        schemaId: spec.schemaId,
        kindKey: spec.kindKey,
      });
    }
  }

  const ledgerFamilies = getCoverageLedgerFamilies0(rowPack.CoverageLedger);

  if (Array.isArray(ledgerFamilies)) {
    for (const family of ROW_REQUIRED_FAMILIES0) {
      if (!ledgerFamilies.includes(family)) {
        return validationReject0(['CoverageLedger', 'families', family], 'CoverageLedger is missing a required row family', {
          family,
        });
      }
    }
  }

  return validationAccept0({
    kind: 'RowFamilyCoverage0NF',
    familyCount: ROW_REQUIRED_FAMILIES0.length,
    families: ROW_REQUIRED_FAMILIES0.map((family) => ({
      family,
      index: covered.get(family).index,
      batchId: covered.get(family).row.BatchID,
      packageId: covered.get(family).row.PackageID,
      schemaId: covered.get(family).row.SchemaID,
    })),
  });
}

function validateRouteLedger0(rowPack) {
  const ledger = rowPack.RouteLedger;

  if (!isPlainObject(ledger)) {
    return validationReject0(['RouteLedger'], 'RouteLedger must be an object', {
      actual: typeof ledger,
    });
  }

  if (ledger.highestActiveRoute === false) {
    return validationReject0(['RouteLedger', 'highestActiveRoute'], 'RouteLedger must enforce highest active route selection', null);
  }

  const priority = Array.isArray(ledger.priority) ? ledger.priority : ROW_ROUTE_PRIORITY0;

  for (let index = 0; index < rowPack.Rows.length; index += 1) {
    const row = rowPack.Rows[index];
    const highest = highestRoute0(row.ActiveRouteSet, priority);

    if (highest !== row.SelectedRoute) {
      return validationReject0(['Rows', index, 'SelectedRoute'], 'SelectedRoute must be the highest-priority active route', {
        family: row.FamilyID,
        selectedRoute: row.SelectedRoute,
        highest,
        activeRouteSet: row.ActiveRouteSet,
      });
    }
  }

  return validationAccept0({
    kind: 'RouteLedger0NF',
    priority,
    rowCount: rowPack.Rows.length,
  });
}

function validateProofRefLedger0(rowPack) {
  const ledger = rowPack.ProofRefLedger;

  if (!isPlainObject(ledger)) {
    return validationReject0(['ProofRefLedger'], 'ProofRefLedger must be an object', {
      actual: typeof ledger,
    });
  }

  if (ledger.acyclic === false) {
    return validationReject0(['ProofRefLedger', 'acyclic'], 'ProofRefLedger must enforce acyclic proof references', null);
  }

  const seenRowProofIds = new Set();

  for (let index = 0; index < rowPack.Rows.length; index += 1) {
    const row = rowPack.Rows[index];
    const proofRef = row.ProofRef;

    if (!isPlainObject(proofRef)) {
      return validationReject0(['Rows', index, 'ProofRef'], 'ProofRef must be an object', {
        actual: typeof proofRef,
      });
    }

    const kind = normalizeProofRefKind0(proofRef);

    if (!ROW_ALLOWED_PROOF_REF_KINDS0.includes(kind)) {
      return validationReject0(['Rows', index, 'ProofRef', 'refKind'], 'ProofRef kind is not allowed', {
        kind,
      });
    }

    const opaque = findOpaqueProof0(proofRef, ['Rows', index, 'ProofRef']);

    if (opaque !== null) {
      return validationReject0(opaque.path, 'opaque proof material is not allowed in ProofRef', opaque);
    }

    if (kind === 'EarlierRowProof') {
      const refIndex = proofRef.rowIndex ?? proofRef.index;

      if (!Number.isInteger(refIndex) || refIndex >= index || refIndex < 0) {
        return validationReject0(['Rows', index, 'ProofRef', 'rowIndex'], 'EarlierRowProof must reference an earlier row', {
          index,
          refIndex,
        });
      }

      const refId = proofRef.id ?? proofRef.ref ?? String(refIndex);

      if (!seenRowProofIds.has(refId) && !seenRowProofIds.has(String(refIndex))) {
        return validationReject0(['Rows', index, 'ProofRef', 'id'], 'EarlierRowProof target is not available', {
          refId,
        });
      }
    }

    seenRowProofIds.add(proofRef.id ?? String(index));
    seenRowProofIds.add(String(index));
  }

  return validationAccept0({
    kind: 'ProofRefLedger0NF',
    rowCount: rowPack.Rows.length,
  });
}

function validateHashIndex0(rowPack) {
  const buckets = getHashBuckets0(rowPack.HashIndex);

  if (!isPlainObject(buckets)) {
    return validationReject0(['HashIndex', 'buckets'], 'HashIndex must provide a bucket object', {
      actual: typeof buckets,
    });
  }

  for (let index = 0; index < rowPack.Rows.length; index += 1) {
    const row = rowPack.Rows[index];
    const hashHex = getDigestHex0(row.HashKey);
    const bucket = buckets[hashHex];

    if (!Array.isArray(bucket)) {
      return validationReject0(['HashIndex', 'buckets', hashHex], 'HashIndex is missing a bucket for a row hash', {
        index,
        hashHex,
      });
    }

    const entryIndex = bucket.findIndex((entry) => {
      if (Number.isInteger(entry)) {
        return entry === index;
      }

      return isPlainObject(entry) && (entry.index === index || entry.rowIndex === index);
    });

    if (entryIndex === -1) {
      return validationReject0(['HashIndex', 'buckets', hashHex], 'HashIndex bucket is missing the row index', {
        index,
        hashHex,
      });
    }

    const entry = bucket[entryIndex];

    if (isPlainObject(entry)) {
      if (entry.fullKeyCompared !== true && entry.canonicalByteCompared !== true) {
        return validationReject0(['HashIndex', 'buckets', hashHex, entryIndex, 'fullKeyCompared'], 'HashIndex lookup must be followed by full key or canonical byte comparison', {
          index,
          hashHex,
          entry,
        });
      }

      if (entry.rowKeyDigest !== undefined && !sameDigest0(entry.rowKeyDigest, digestCanonical0(row.RowKey))) {
        return validationReject0(['HashIndex', 'buckets', hashHex, entryIndex, 'rowKeyDigest'], 'HashIndex rowKeyDigest mismatch', {
          index,
          expected: digestCanonical0(row.RowKey),
          actual: entry.rowKeyDigest,
        });
      }
    }
  }

  return validationAccept0({
    kind: 'HashIndex0NF',
    bucketCount: Object.keys(buckets).length,
  });
}

function validateBoundsLedger0(rowPack) {
  const ledger = rowPack.BoundsLedger;

  if (!isPlainObject(ledger)) {
    return validationReject0(['BoundsLedger'], 'BoundsLedger must be an object', {
      actual: typeof ledger,
    });
  }

  if (ledger.polynomial === false) {
    return validationReject0(['BoundsLedger', 'polynomial'], 'BoundsLedger must enforce polynomial bounds', null);
  }

  if (ledger.finite === false) {
    return validationReject0(['BoundsLedger', 'finite'], 'BoundsLedger must enforce finite row universes', null);
  }

  for (let index = 0; index < rowPack.Rows.length; index += 1) {
    const row = rowPack.Rows[index];

    if (!isPlainObject(row.BoundsRef)) {
      return validationReject0(['Rows', index, 'BoundsRef'], 'BoundsRef must be an object', {
        actual: typeof row.BoundsRef,
      });
    }

    if (row.BoundsRef.polynomial === false) {
      return validationReject0(['Rows', index, 'BoundsRef', 'polynomial'], 'row BoundsRef must be polynomial', {
        index,
        family: row.FamilyID,
      });
    }
  }

  return validationAccept0({
    kind: 'BoundsLedger0NF',
    rowCount: rowPack.Rows.length,
  });
}

function validateNoHiddenMin0(rowPack) {
  const hit = findForbiddenExecutableUse0(rowPack, ['RowPack0'], false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'RowsNoHiddenMin0NF',
  });
}

function makeNFMap0(rows) {
  return {
    kind: 'NFMap0',
    version: CHECKER_VERSION,
    entries: rows.map((row, index) => ({
      index,
      batchId: row.BatchID,
      family: row.FamilyID,
      rawDigest: digestCanonical0(row.RawObj),
      normDigest: digestCanonical0(row.NormObj),
      transportDigest: digestCanonical0(row.TransportProof),
    })),
  };
}

function makeHashIndex0(rows) {
  const buckets = {};

  for (let index = 0; index < rows.length; index += 1) {
    const row = rows[index];
    const hex = getDigestHex0(row.HashKey);

    if (!buckets[hex]) {
      buckets[hex] = [];
    }

    buckets[hex].push({
      index,
      rowKeyDigest: digestCanonical0(row.RowKey),
      fullKeyCompared: true,
      canonicalByteCompared: true,
    });
  }

  return {
    kind: 'HashIndex0',
    version: CHECKER_VERSION,
    buckets,
  };
}

function makeDupLedger0(rows) {
  return {
    kind: 'DupLedger0',
    version: CHECKER_VERSION,
    fullRowKeyComparison: true,
    conflictCount: 0,
    rowCount: rows.length,
  };
}

function makeCoverageLedger0(rows) {
  return {
    kind: 'CoverageLedger0',
    version: CHECKER_VERSION,
    familyCount: ROW_REQUIRED_FAMILIES0.length,
    families: rows.map((row) => row.FamilyID),
  };
}

function makeRouteLedger0(rows) {
  return {
    kind: 'RouteLedger0',
    version: CHECKER_VERSION,
    priority: ROW_ROUTE_PRIORITY0,
    highestActiveRoute: true,
    rows: rows.map((row, index) => ({
      index,
      family: row.FamilyID,
      activeRouteSet: row.ActiveRouteSet,
      selectedRoute: row.SelectedRoute,
      highestActiveRoute: highestRoute0(row.ActiveRouteSet, ROW_ROUTE_PRIORITY0),
    })),
  };
}

function makeProofRefLedger0(rows) {
  return {
    kind: 'ProofRefLedger0',
    version: CHECKER_VERSION,
    acyclic: true,
    allowedRefKinds: ROW_ALLOWED_PROOF_REF_KINDS0,
    rows: rows.map((row, index) => ({
      index,
      family: row.FamilyID,
      proofRef: row.ProofRef,
    })),
  };
}

function makeBoundsLedger0(rows) {
  return {
    kind: 'BoundsLedger0',
    version: CHECKER_VERSION,
    finite: true,
    polynomial: true,
    rows: rows.map((row, index) => ({
      index,
      family: row.FamilyID,
      boundsRef: row.BoundsRef,
    })),
  };
}

function getSchemaEntries0(schemaInv) {
  if (Array.isArray(schemaInv)) {
    return schemaInv;
  }

  if (!isPlainObject(schemaInv)) {
    return null;
  }

  return schemaInv.schemas ?? schemaInv.Schemas ?? schemaInv.entries ?? schemaInv.Entries;
}

function getBatchEntries0(batchInv) {
  if (Array.isArray(batchInv)) {
    return batchInv;
  }

  if (!isPlainObject(batchInv)) {
    return null;
  }

  return batchInv.batches ?? batchInv.Batches ?? batchInv.entries ?? batchInv.Entries;
}

function getHashBuckets0(hashIndex) {
  if (!isPlainObject(hashIndex)) {
    return null;
  }

  return hashIndex.buckets ?? hashIndex.Buckets ?? hashIndex.index ?? hashIndex.Index;
}

function getCoverageLedgerFamilies0(coverageLedger) {
  if (!isPlainObject(coverageLedger)) {
    return null;
  }

  return coverageLedger.families ?? coverageLedger.Families;
}

function getPiRows0(rowPack) {
  return rowPack.PiRows ?? rowPack['Πrows'] ?? rowPack.piRows;
}

function normalizeImportList0(value) {
  if (!Array.isArray(value)) {
    return [];
  }

  return value.map((entry) => String(entry));
}

function normalizeFamilyList0(value) {
  if (!Array.isArray(value)) {
    return [];
  }

  return value.map((entry) => String(entry));
}

function familiesForBatch0(batchId) {
  return ROW_REQUIRED_FAMILY_SPECS0
    .filter((spec) => spec.batchId === batchId)
    .map((spec) => spec.family);
}

function firstForbiddenFamilyEdge0(fromFamilies, toFamilies) {
  for (const from of fromFamilies) {
    for (const to of toFamilies) {
      for (const edge of ROW_FORBIDDEN_IMPORT_EDGES0) {
        if (edge[0] === from && edge[1] === to) {
          return edge;
        }
      }
    }
  }

  return null;
}

function rowMatchesFamilySpec0(row, spec) {
  return (
    row &&
    typeof row === 'object' &&
    row.BatchID === spec.batchId &&
    row.FamilyID === spec.family &&
    row.PackageID === spec.packageId &&
    row.SchemaID === spec.schemaId &&
    row.KindKey === spec.kindKey
  );
}

function highestRoute0(activeRoutes, priority) {
  if (!Array.isArray(activeRoutes) || activeRoutes.length === 0) {
    return null;
  }

  let best = activeRoutes[0];
  let bestIndex = priorityIndex0(best, priority);

  for (const route of activeRoutes.slice(1)) {
    const index = priorityIndex0(route, priority);

    if (index < bestIndex) {
      best = route;
      bestIndex = index;
    }
  }

  return best;
}

function priorityIndex0(route, priority) {
  const index = priority.findIndex((entry) => stableStringify0(entry) === stableStringify0(route));
  return index === -1 ? Number.MAX_SAFE_INTEGER : index;
}

function normalizeProofRefKind0(proofRef) {
  if (proofRef.refKind !== undefined) {
    return String(proofRef.refKind);
  }

  if (proofRef.kind === 'ProofRef0' || proofRef.tag === 'ProofRef0') {
    return 'KPrimitive';
  }

  return String(proofRef.kind ?? proofRef.tag ?? 'KPrimitive');
}

function getDigestHex0(digest) {
  if (isPlainObject(digest) && typeof digest.hex === 'string') {
    return digest.hex;
  }

  return digestCanonical0(digest).hex;
}

function sameDigest0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.alg === b.alg &&
    a.hex === b.hex
  );
}

function schemaKey0(packageId, schemaId) {
  return `${String(packageId)}:${String(schemaId)}`;
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
    if (/opaque|proofblob|trustedblob|assumeproof/i.test(key)) {
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

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && FORBIDDEN_EXECUTABLE_SYMBOLS0.includes(value)) {
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

function recordToValidation0(record) {
  if (isRejectRecord0(record)) {
    return validationReject0(record.Path ?? record.path ?? [], 'inner checker rejected', {
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

function validationRejectWithCoord0(coordSuffix, path, reason, detail) {
  return {
    ok: false,
    coordSuffix,
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

function sortedUnique0(values) {
  return Array.from(new Set(values.map((value) => String(value)))).sort();
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

export {
  makeNFMap0,
  makeHashIndex0,
  makeDupLedger0,
  makeCoverageLedger0,
  makeRouteLedger0,
  makeProofRefLedger0,
  makeBoundsLedger0,
};