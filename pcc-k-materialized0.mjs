import fs from 'node:fs/promises';
import path from 'node:path';
import { createHash } from 'node:crypto';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckKBundle0,
  KERNEL_RULES0,
  REFLECTION_REQUIRED_CHECKERS0,
  SIGMA_REQUIRED_THEOREMS0,
  makeKernelProofNode0,
  makeKernelRuleTable0,
} from './pcc-kimpl0.mjs';

import {
  CheckMaterializedBoot0,
  makeMaterializedBoot0,
} from './pcc-boot-materialized0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_KBUNDLE_REQUIRED_FILES0 = Object.freeze([
  'MaterializedKBundle0.json',
  'KImpl0.json',
  'K0.json',
  'SigmaRegistry0.json',
  'ReflectionRegistry0.json',
  'MaterializedKBundle0.check.json',
]);

export const MATERIALIZED_KBUNDLE_PHASES0 = Object.freeze([
  'CheckMaterializedBoot0',
  'CheckKBundle0',
  'CheckMaterializedKBootLinks0',
  'CheckMaterializedKJson0',
  'CheckMaterializedKNoFixtureMarkers0',
]);

export const MATERIALIZED_KBUNDLE_FORBIDDEN_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

export function makeMaterializedKernelRuleTable0(overrides = {}) {
  return makeKernelRuleTable0().map((rule) => ({
    ...rule,
    materialized: true,
    source: 'Boot0.KernelSeed0',
    ...overrides[rule.name],
  }));
}

export function makeMaterializedKImpl0({
  Boot0,
  overrides = {},
} = {}) {
  if (!isPlainObject(Boot0)) {
    throw new TypeError('makeMaterializedKImpl0 requires a materialized Boot0 object');
  }

  const ifaceHash = digestCanonical0(Boot0.IfaceDict0);
  const schedHash = digestCanonical0(Boot0.Sched0);

  return {
    kind: 'KImpl0',
    version: CHECKER_VERSION,
    IfaceHash: ifaceHash,
    SchedHash: schedHash,
    Sorts: {
      Term: 'Term',
      Formula: 'Formula',
      Judgment: 'Judgment',
      SideCond: 'SideCond',
      ProofNode: 'ProofNode',
      SigmaTheorem: 'SigmaTheorem',
      Reflection: 'Reflection',
    },
    Constructors: {
      Var: 'Var',
      App: 'App',
      Eq: 'Eq',
      And: 'And',
      Implies: 'Implies',
      ForallFinite: 'ForallFinite',
      Judgment: 'Judgment',
      ProofNode: 'ProofNode',
      SigmaInstance: 'SigmaInstance',
      ReflectionInstance: 'ReflectionInstance',
    },
    TermGrammar: {
      kind: 'TermGrammar0',
      constructors: [
        'Var',
        'App',
        'Tuple',
        'Record',
        'DigestRef',
      ],
      finite: true,
      materialized: true,
    },
    FormulaGrammar: {
      kind: 'FormulaGrammar0',
      constructors: [
        'Eq',
        'And',
        'Implies',
        'ForallFinite',
        'BoundedExists',
      ],
      finite: true,
      materialized: true,
    },
    JudgmentGrammar: {
      kind: 'JudgmentGrammar0',
      constructors: [
        'Derives',
        'Accepts',
        'Rejects',
        'Bounds',
        'Reflects',
      ],
      finite: true,
      materialized: true,
    },
    RuleTable: makeMaterializedKernelRuleTable0(),
    SideLang: {
      kind: 'SideLang0',
      allowedOps: [
        'finiteIteration',
        'truthVectorEval',
        'finiteRelationLookup',
        'topologicalSort',
        'matching',
        'dynamicProgramming',
        'integerArithmetic',
        'transportCheck',
        'rankComparison',
      ],
      noMinSymbolPolicy: {
        kind: 'NoHiddenMinSymbolPolicy0',
        expansionBeforeScan: true,
        occurrenceClasses: [
          'DefImport',
          'SoundImport',
          'ExecCall',
          'AssumeOnly',
          'EmitToken',
        ],
        forbiddenSymbols: [
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
        ],
      },
    },
    ProofDAGChecker: {
      kind: 'ProofDAGChecker0',
      total: true,
      deterministic: true,
      acyclic: true,
      earlierPremiseOnly: true,
    },
    SigmaChecker: {
      kind: 'SigmaChecker0',
      total: true,
      deterministic: true,
      requiresV53: true,
      requiresV54: true,
    },
    ReflectionChecker: {
      kind: 'ReflectionChecker0',
      total: true,
      deterministic: true,
      publicConclusionRequired: true,
    },
    InstanceChecker: {
      kind: 'InstanceChecker0',
      total: true,
      deterministic: true,
      typedInstancesOnly: true,
    },
    BoundsK: {
      kind: 'BoundsK0',
      nodeLimit: 4096,
      premiseLimit: 16,
      sideConditionLimit: 64,
      importLimit: 16,
      polynomialExponent: 6,
    },
    PiK: {
      kind: 'PiK0',
      materialized: true,
      externalJson: true,
      note: 'materialized proof-kernel implementation references',
      refs: [
        {
          label: 'IfaceDict0',
          digest: ifaceHash,
        },
        {
          label: 'Sched0',
          digest: schedHash,
        },
        {
          label: 'KernelSeed0',
          digest: digestCanonical0(Boot0.KernelSeed0),
        },
        {
          label: 'RuleTable',
          digest: digestCanonical0(makeMaterializedKernelRuleTable0()),
        },
      ],
    },
    ...overrides,
  };
}

export function makeMaterializedK0({
  Boot0,
  overrides = {},
} = {}) {
  if (!isPlainObject(Boot0)) {
    throw new TypeError('makeMaterializedK0 requires a materialized Boot0 object');
  }

  const kernelRules = Array.isArray(Boot0.KernelSeed0?.rules)
    ? Boot0.KernelSeed0.rules
    : KERNEL_RULES0;

  return {
    kind: 'KConformance0',
    version: CHECKER_VERSION,
    suiteId: 'K0.materialized.primitive-conformance',
    bootKernelSeedDigest: digestCanonical0(Boot0.KernelSeed0),
    nodes: kernelRules.map((ruleName, index) => makeKernelProofNode0({
      id: `k0.conf.${ruleName}`,
      RuleName: ruleName,
      Conclusion: {
        tag: 'PrimitiveConformanceJudgment0',
        rule: ruleName,
        materialized: true,
      },
      Payload: {
        ruleIndex: index,
        source: 'Boot0.KernelSeed0',
        bootRulePresent: true,
      },
      BoundsRef: {
        tag: 'BoundsRef0',
        id: `K0.${ruleName}.bounds`,
        source: 'Boot0.Sched0',
      },
    })),
    ...overrides,
  };
}

export function makeMaterializedSigmaRegistry0({
  Boot0,
  overrides = {},
} = {}) {
  if (!isPlainObject(Boot0)) {
    throw new TypeError('makeMaterializedSigmaRegistry0 requires a materialized Boot0 object');
  }

  const bootKernelSeedDigest = digestCanonical0(Boot0.KernelSeed0);

  return {
    kind: 'SigmaRegistry0',
    version: CHECKER_VERSION,
    materialized: true,
    bootKernelSeedDigest,
    theorems: [
      {
        kind: 'SigmaTheorem0',
        id: 'Sigma.V53',
        theorem: 'V53.ConstantCutHypergraphRigidity',
        conclusion: {
          tag: 'HypergraphRigidityConclusion0',
          statement: 'constant-cut nonnegative hypergraph rigidity',
          finite: true,
        },
        proofRefs: [
          'k0.conf.FiniteExhaust',
          'k0.conf.IntArith',
        ],
        modeSafe: true,
        finiteSchema: true,
      },
      {
        kind: 'SigmaTheorem0',
        id: 'Sigma.V54',
        theorem: 'V54.ConsumerAntichainNormalForm',
        conclusion: {
          tag: 'ConsumerAntichainConclusion0',
          statement: 'monotone consumer antichain normal form',
          finite: true,
        },
        proofRefs: [
          'k0.conf.FiniteExhaust',
          'k0.conf.Record',
        ],
        modeSafe: true,
        finiteSchema: true,
      },
    ],
    ...overrides,
  };
}

export function makeMaterializedReflectionRegistry0({
  Boot0,
  overrides = {},
} = {}) {
  if (!isPlainObject(Boot0)) {
    throw new TypeError('makeMaterializedReflectionRegistry0 requires a materialized Boot0 object');
  }

  return {
    kind: 'ReflectionRegistry0',
    version: CHECKER_VERSION,
    materialized: true,
    bootDigest: digestCanonical0(Boot0),
    reflections: REFLECTION_REQUIRED_CHECKERS0.map((checker) => ({
      kind: 'Reflection0',
      checker,
      theorem: `${checker}.Soundness`,
      publicConclusion: {
        tag: 'CheckerSoundnessConclusion0',
        checker,
        acceptedRecordImpliesSoundJudgment: true,
      },
      proofRefs: [
        'k0.conf.Record',
        'k0.conf.Subst',
      ],
      modeSafe: true,
      deterministic: true,
    })),
    ...overrides,
  };
}

export async function makeMaterializedKBundle0(overrides = {}) {
  const Boot0 = overrides.Boot0 ?? await makeMaterializedBoot0(overrides.bootOverrides ?? {});
  const KImpl = overrides.KImpl ?? makeMaterializedKImpl0({
    Boot0,
    overrides: overrides.kimplOverrides ?? {},
  });
  const K0 = overrides.K0 ?? makeMaterializedK0({
    Boot0,
    overrides: overrides.k0Overrides ?? {},
  });
  const PSigma = overrides.PSigma ?? overrides['PΣ'] ?? makeMaterializedSigmaRegistry0({
    Boot0,
    overrides: overrides.sigmaOverrides ?? {},
  });
  const ReflectionRegistry = overrides.ReflectionRegistry ?? makeMaterializedReflectionRegistry0({
    Boot0,
    overrides: overrides.reflectionOverrides ?? {},
  });

  const material = {
    kind: 'MaterializedKBundle0',
    version: CHECKER_VERSION,
    materializedPath: true,
    Boot0,
    KImpl,
    K0,
    PSigma,
    ReflectionRegistry,
    PiKBundle: {
      kind: 'PiKBundle0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          label: 'Boot0',
          digest: digestCanonical0(Boot0),
        },
        {
          label: 'KImpl',
          digest: digestCanonical0(KImpl),
        },
        {
          label: 'K0',
          digest: digestCanonical0(K0),
        },
        {
          label: 'PSigma',
          digest: digestCanonical0(PSigma),
        },
        {
          label: 'ReflectionRegistry',
          digest: digestCanonical0(ReflectionRegistry),
        },
      ],
    },
    ...withoutKBundleOverrideFields0(overrides),
  };

  return material;
}

export async function CheckMaterializedKBundle0(bundle, config = {}) {
  const checker = 'CheckMaterializedKBundle0';
  const ledger = [];
  const normalized = normalizeKBundle0(bundle, config);

  if (!normalized.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: normalized.path,
      witness: normalized.witness,
      ledger,
    });
  }

  const value = normalized.value;
  const boot = value.Boot0;

  const bootRecord = await CheckMaterializedBoot0(boot, config.bootConfig ?? {});
  const bootResult = recordToValidation0(bootRecord, ['Boot0']);

  ledger.push({
    phase: 'CheckMaterializedBoot0',
    status: bootResult.ok ? 'pass' : 'fail',
    digest: bootRecord.Digest ?? bootRecord.digest ?? digestCanonical0(bootRecord),
  });

  if (!bootResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.CheckMaterializedBoot0`,
      path: bootResult.path,
      witness: bootResult.witness,
      ledger,
    });
  }

  const bundleRecord = await CheckKBundle0(value);
  const bundleResult = recordToValidation0(bundleRecord, ['KBundle']);

  ledger.push({
    phase: 'CheckKBundle0',
    status: bundleResult.ok ? 'pass' : 'fail',
    digest: bundleRecord.Digest ?? bundleRecord.digest ?? digestCanonical0(bundleRecord),
  });

  if (!bundleResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.CheckKBundle0`,
      path: bundleResult.path,
      witness: bundleResult.witness,
      ledger,
    });
  }

  const links = validateBootLinks0(value);

  ledger.push({
    phase: 'CheckMaterializedKBootLinks0',
    status: links.ok ? 'pass' : 'fail',
    digest: digestCanonical0(links.nf ?? links.witness ?? null),
  });

  if (!links.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.bootLinks`,
      path: links.path,
      witness: links.witness,
      ledger,
    });
  }

  const json = validateJsonMaterializable0(value);

  ledger.push({
    phase: 'CheckMaterializedKJson0',
    status: json.ok ? 'pass' : 'fail',
    digest: digestCanonical0(json.nf ?? json.witness ?? null),
  });

  if (!json.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.json`,
      path: json.path,
      witness: json.witness,
      ledger,
    });
  }

  const markers = validateNoFixtureMarkers0(value, config);

  ledger.push({
    phase: 'CheckMaterializedKNoFixtureMarkers0',
    status: markers.ok ? 'pass' : 'fail',
    digest: digestCanonical0(markers.nf ?? markers.witness ?? null),
  });

  if (!markers.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.noFixtureMarkers`,
      path: markers.path,
      witness: markers.witness,
      ledger,
    });
  }

  const bundleNF = bundleRecord.NF ?? bundleRecord.nf;
  const bootNF = bootRecord.NF ?? bootRecord.nf;
  const canonicalBytes = stableStringify0(value);

  const nf = {
    kind: 'MaterializedKBundle0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: MATERIALIZED_KBUNDLE_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,
    bootDigest: bootRecord.Digest ?? bootRecord.digest,
    bootCanonicalByteDigest: bootNF.canonicalByteDigest,
    kbundleDigest: bundleRecord.Digest ?? bundleRecord.digest,
    canonicalByteDigest: sha256Utf8DigestRecord0(canonicalBytes),
    byteLength: Buffer.byteLength(canonicalBytes, 'utf8'),
    ifaceHash: digestCanonical0(boot.IfaceDict0),
    schedHash: digestCanonical0(boot.Sched0),
    kimplDigest: bundleNF.kimplDigest,
    conformanceDigest: bundleNF.conformanceDigest,
    sigmaDigest: bundleNF.sigmaDigest,
    reflectionDigest: bundleNF.reflectionDigest,
    kernelRuleCount: KERNEL_RULES0.length,
    conformanceNodeCount: value.K0.nodes.length,
    sigmaTheoremCount: value.PSigma.theorems.length,
    reflectionCount: value.ReflectionRegistry.reflections.length,
    noFixtureMarkers: true,
    jsonMaterializable: true,
    bootLinked: true,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeMaterializedKBundleFiles0(outputDir, config = {}) {
  const outDir = typeof outputDir === 'string' && outputDir.length > 0
    ? outputDir
    : './materialized-kbundle0';

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const bundle = config.bundle ?? await makeMaterializedKBundle0(config.bundleOverrides ?? {});
  const checked = await CheckMaterializedKBundle0(bundle, config.checkConfig ?? {});

  if (checked.tag !== 'accept') {
    return checked;
  }

  const files = [
    ['MaterializedKBundle0.json', bundle],
    ['KImpl0.json', bundle.KImpl],
    ['K0.json', bundle.K0],
    ['SigmaRegistry0.json', bundle.PSigma],
    ['ReflectionRegistry0.json', bundle.ReflectionRegistry],
    ['MaterializedKBundle0.check.json', checked],
  ];

  const written = [];

  for (const [fileName, value] of files) {
    const filePath = path.join(outDir, fileName);
    const bytes = `${stableStringify0(value)}\n`;

    await fs.writeFile(filePath, bytes, 'utf8');

    written.push({
      path: filePath,
      byteLength: Buffer.byteLength(bytes, 'utf8'),
      fileDigest: sha256Utf8DigestRecord0(bytes),
    });
  }

  const nf = {
    kind: 'MaterializedKBundleWrite0NF',
    checker: 'WriteMaterializedKBundleFiles0',
    version: CHECKER_VERSION,
    outputDir: outDir,
    fileCount: written.length,
    files: written,
    materializedKBundleDigest: checked.Digest,
    kbundleDigest: checked.NF.kbundleDigest,
    bootDigest: checked.NF.bootDigest,
    kimplDigest: checked.NF.kimplDigest,
    sigmaDigest: checked.NF.sigmaDigest,
    reflectionDigest: checked.NF.reflectionDigest,
  };

  return makeAcceptRecord({
    checker: 'WriteMaterializedKBundleFiles0',
    nf,
    ledger: [
      {
        phase: 'CheckMaterializedKBundle0',
        status: 'pass',
        digest: checked.Digest,
      },
      {
        phase: 'writeFiles',
        status: 'pass',
        digest: digestCanonical0(written),
      },
    ],
  });
}

function normalizeKBundle0(bundle, config) {
  if (!isPlainObject(bundle)) {
    return validationReject0([], 'MaterializedKBundle0 must be an object', {
      actual: typeof bundle,
    });
  }

  const Boot0 = bundle.Boot0 ?? config.Boot0 ?? config.boot;

  if (!isPlainObject(Boot0)) {
    return validationReject0(['Boot0'], 'MaterializedKBundle0 must contain Boot0 or receive one in config', {
      actual: typeof Boot0,
    });
  }

  for (const field of [
    'KImpl',
    'K0',
    'PSigma',
    'ReflectionRegistry',
  ]) {
    if (!isPlainObject(bundle[field])) {
      return validationReject0([field], `MaterializedKBundle0 ${field} must be an object`, {
        actual: typeof bundle[field],
      });
    }
  }

  return validationAccept0({
    ...bundle,
    Boot0,
  });
}

function validateBootLinks0(bundle) {
  const expectedIface = digestCanonical0(bundle.Boot0.IfaceDict0);
  const expectedSched = digestCanonical0(bundle.Boot0.Sched0);

  if (!sameDigestRecord0(bundle.KImpl.IfaceHash, expectedIface)) {
    return validationReject0(['KImpl', 'IfaceHash'], 'KImpl IfaceHash must match materialized Boot0 IfaceDict0 digest', {
      expected: expectedIface,
      actual: bundle.KImpl.IfaceHash,
    });
  }

  if (!sameDigestRecord0(bundle.KImpl.SchedHash, expectedSched)) {
    return validationReject0(['KImpl', 'SchedHash'], 'KImpl SchedHash must match materialized Boot0 Sched0 digest', {
      expected: expectedSched,
      actual: bundle.KImpl.SchedHash,
    });
  }

  if (!sameDigestRecord0(bundle.K0.bootKernelSeedDigest, digestCanonical0(bundle.Boot0.KernelSeed0))) {
    return validationReject0(['K0', 'bootKernelSeedDigest'], 'K0 must link to materialized Boot0 KernelSeed0 digest', {
      expected: digestCanonical0(bundle.Boot0.KernelSeed0),
      actual: bundle.K0.bootKernelSeedDigest,
    });
  }

  return validationAccept0({
    kind: 'MaterializedKBootLinks0NF',
    ifaceHash: expectedIface,
    schedHash: expectedSched,
    kernelSeedDigest: digestCanonical0(bundle.Boot0.KernelSeed0),
  });
}

function validateJsonMaterializable0(value) {
  const hit = findNonJsonValue0(value, []);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized K bundle must be JSON-materializable data', {
      actual: hit.actual,
    });
  }

  const canonical = stableStringify0(value);
  let reparsed;

  try {
    reparsed = JSON.parse(canonical);
  } catch (error) {
    return validationReject0([], 'materialized K bundle canonical bytes must parse as JSON', {
      error: error.message,
    });
  }

  if (stableStringify0(reparsed) !== canonical) {
    return validationReject0([], 'materialized K bundle JSON roundtrip must be byte-stable', null);
  }

  return validationAccept0({
    kind: 'MaterializedKBundleJson0NF',
    byteLength: Buffer.byteLength(canonical, 'utf8'),
    byteDigest: sha256Utf8DigestRecord0(canonical),
  });
}

function validateNoFixtureMarkers0(value, config = {}) {
  const allow = new Set(config.allowedMarkerPaths ?? []);
  const hit = findFixtureMarker0(value, [], allow);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized K bundle must not contain fixture-level marker text', {
      marker: hit.marker,
      value: hit.value,
    });
  }

  return validationAccept0({
    kind: 'MaterializedKBundleNoFixtureMarkers0NF',
  });
}

function findFixtureMarker0(value, pathNow, allow) {
  const pathKey = pathNow.join('.');

  if (allow.has(pathKey)) {
    return null;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of MATERIALIZED_KBUNDLE_FORBIDDEN_MARKERS0) {
      if (lower.includes(marker)) {
        return {
          path: pathNow,
          marker,
          value,
        };
      }
    }

    return null;
  }

  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'number' || typeof value === 'boolean') {
    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findFixtureMarker0(value[index], [...pathNow, index], allow);

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
    const keyHit = findFixtureMarker0(key, [...pathNow, key], allow);

    if (keyHit !== null) {
      return keyHit;
    }

    const valueHit = findFixtureMarker0(value[key], [...pathNow, key], allow);

    if (valueHit !== null) {
      return valueHit;
    }
  }

  return null;
}

function findNonJsonValue0(value, pathNow) {
  if (value === undefined) {
    return {
      path: pathNow,
      actual: 'undefined',
    };
  }

  if (typeof value === 'function') {
    return {
      path: pathNow,
      actual: 'function',
    };
  }

  if (typeof value === 'symbol') {
    return {
      path: pathNow,
      actual: 'symbol',
    };
  }

  if (typeof value === 'bigint') {
    return {
      path: pathNow,
      actual: 'bigint',
    };
  }

  if (value === null || typeof value === 'string' || typeof value === 'boolean') {
    return null;
  }

  if (typeof value === 'number') {
    if (!Number.isFinite(value) || Object.is(value, -0)) {
      return {
        path: pathNow,
        actual: String(value),
      };
    }

    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findNonJsonValue0(value[index], [...pathNow, index]);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return {
      path: pathNow,
      actual: Object.prototype.toString.call(value),
    };
  }

  for (const key of Object.keys(value)) {
    const hit = findNonJsonValue0(value[key], [...pathNow, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function sameDigestRecord0(actual, expected) {
  return (
    isPlainObject(actual) &&
    isPlainObject(expected) &&
    actual.alg === expected.alg &&
    actual.bytes === expected.bytes &&
    actual.hex === expected.hex
  );
}

function withoutKBundleOverrideFields0(overrides) {
  const out = {
    ...overrides,
  };

  for (const key of [
    'Boot0',
    'KImpl',
    'K0',
    'PSigma',
    'PΣ',
    'ReflectionRegistry',
    'bootOverrides',
    'kimplOverrides',
    'k0Overrides',
    'sigmaOverrides',
    'reflectionOverrides',
  ]) {
    delete out[key];
  }

  return out;
}

function sha256Utf8DigestRecord0(value) {
  return {
    alg: 'SHA256',
    bytes: 'utf8',
    hex: createHash('sha256').update(String(value), 'utf8').digest('hex'),
  };
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
    value: nf,
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
