import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckKBundle0,
  KERNEL_RULES0,
  REFLECTION_REQUIRED_CHECKERS0,
  SIGMA_REQUIRED_THEOREMS0,
} from './pcc-kimpl0.mjs';

import {
  CheckMaterializedKBundle0,
  makeMaterializedKBundle0,
} from './pcc-k-materialized0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_K_FORBIDDEN_MARKERS0 = Object.freeze([
  'synthetic',
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const OPAQUE_PROOF_MARKERS0 = Object.freeze([
  'opaque-proof',
  'opaque proof',
  'proof blob',
  'admit',
  'sorry',
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

export function makeConcreteMaterializedKBundleConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedKBundleConfig0',
    version: CHECKER_VERSION,
    checkMaterializedKBundle: true,
    checkKBundle: true,
    checkProofInventory: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    materializedKBundleConfig: {},
    ...overrides,
  };
}

export async function makeConcreteMaterializedKBundle0({
  Boot0 = null,
  MaterializedKBundleEnvelope = null,
  overrides = {},
} = {}) {
  const materializedKBundleEnvelope = MaterializedKBundleEnvelope ?? await makeMaterializedKBundle0(
    Boot0 === null ? {} : { Boot0 },
  );

  const proofInventory = makeConcreteKBundleProofInventory0(materializedKBundleEnvelope);

  const linkage = {
    kind: 'ConcreteMaterializedKBundleLinkage0',
    version: CHECKER_VERSION,
    materializedKBundleDigest: digestCanonical0(materializedKBundleEnvelope),
    bootDigest: digestCanonical0(materializedKBundleEnvelope.Boot0),
    kimplDigest: digestCanonical0(materializedKBundleEnvelope.KImpl),
    k0Digest: digestCanonical0(materializedKBundleEnvelope.K0),
    sigmaDigest: digestCanonical0(materializedKBundleEnvelope.PSigma),
    reflectionDigest: digestCanonical0(materializedKBundleEnvelope.ReflectionRegistry),
    proofInventoryDigest: digestCanonical0(proofInventory),
    kernelRuleCount: proofInventory.kernelRuleCount,
    conformanceNodeCount: proofInventory.conformanceNodeCount,
    sigmaTheoremCount: proofInventory.sigmaTheoremCount,
    reflectionCount: proofInventory.reflectionCount,
  };

  return {
    kind: 'ConcreteMaterializedKBundle0',
    version: CHECKER_VERSION,
    MaterializedKBundleEnvelope: materializedKBundleEnvelope,

    Boot0: materializedKBundleEnvelope.Boot0,
    KImpl: materializedKBundleEnvelope.KImpl,
    K0: materializedKBundleEnvelope.K0,
    PSigma: materializedKBundleEnvelope.PSigma,
    ReflectionRegistry: materializedKBundleEnvelope.ReflectionRegistry,

    ProofInventory: proofInventory,
    Linkage: linkage,

    PiConcreteMaterializedKBundle: {
      kind: 'PiConcreteMaterializedKBundle0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'MaterializedKBundleEnvelope',
          digest: linkage.materializedKBundleDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteKBundleProofInventory',
          digest: linkage.proofInventoryDigest,
        },
      ],
    },

    ...overrides,
  };
}

export function makeConcreteKBundleProofInventory0(materializedKBundleEnvelope) {
  const k0Nodes = Array.isArray(materializedKBundleEnvelope?.K0?.nodes)
    ? materializedKBundleEnvelope.K0.nodes
    : [];

  const k0NodeIds = k0Nodes
    .map((node) => node?.id)
    .filter((id) => typeof id === 'string')
    .sort();

  const k0NodeIdSet = new Set(k0NodeIds);

  const conformanceRules = k0Nodes
    .map((node) => node?.RuleName ?? node?.ruleName ?? node?.rule)
    .filter((rule) => typeof rule === 'string')
    .sort();

  const missingKernelRules = KERNEL_RULES0.filter((rule) => !conformanceRules.includes(rule));

  const sigmaEntries = Array.isArray(materializedKBundleEnvelope?.PSigma?.theorems)
    ? materializedKBundleEnvelope.PSigma.theorems
    : [];

  const sigmaProofRefs = [];
  const unresolvedSigmaProofRefs = [];

  for (const theorem of sigmaEntries) {
    const theoremId = theorem?.id ?? theorem?.theorem ?? theorem?.name ?? null;
    const refs = Array.isArray(theorem?.proofRefs) ? theorem.proofRefs : [];

    for (const ref of refs) {
      sigmaProofRefs.push({
        theoremId,
        ref,
        resolved: k0NodeIdSet.has(ref),
      });

      if (!k0NodeIdSet.has(ref)) {
        unresolvedSigmaProofRefs.push({
          theoremId,
          ref,
        });
      }
    }
  }

  const sigmaTheoremIds = sigmaEntries
    .map((entry) => String(entry?.id ?? entry?.theorem ?? entry?.name ?? ''))
    .filter((entry) => entry.length > 0)
    .sort();

  const missingSigmaTheorems = SIGMA_REQUIRED_THEOREMS0.filter((required) => (
    !sigmaEntries.some((entry) => sigmaEntryMatches0(entry, required))
  ));

  const sigmaEntriesWithoutProofRefs = sigmaEntries
    .filter((entry) => !Array.isArray(entry?.proofRefs) || entry.proofRefs.length === 0)
    .map((entry) => entry?.id ?? entry?.theorem ?? entry?.name ?? null);

  const reflectionEntries = Array.isArray(materializedKBundleEnvelope?.ReflectionRegistry?.reflections)
    ? materializedKBundleEnvelope.ReflectionRegistry.reflections
    : [];

  const reflectionProofRefs = [];
  const unresolvedReflectionProofRefs = [];

  for (const reflection of reflectionEntries) {
    const checker = reflection?.checker ?? null;
    const refs = Array.isArray(reflection?.proofRefs) ? reflection.proofRefs : [];

    for (const ref of refs) {
      reflectionProofRefs.push({
        checker,
        ref,
        resolved: k0NodeIdSet.has(ref),
      });

      if (!k0NodeIdSet.has(ref)) {
        unresolvedReflectionProofRefs.push({
          checker,
          ref,
        });
      }
    }
  }

  const reflectionCheckers = reflectionEntries
    .map((entry) => entry?.checker)
    .filter((entry) => typeof entry === 'string')
    .sort();

  const missingReflectionCheckers = REFLECTION_REQUIRED_CHECKERS0.filter((checker) => (
    !reflectionCheckers.includes(checker)
  ));

  const reflectionsWithoutProofRefs = reflectionEntries
    .filter((entry) => !Array.isArray(entry?.proofRefs) || entry.proofRefs.length === 0)
    .map((entry) => entry?.checker ?? null);

  const opaqueHit = firstOpaqueProofMarker0(materializedKBundleEnvelope, ['MaterializedKBundleEnvelope']);
  const executableMinHit = firstForbiddenExecutableSymbol0(materializedKBundleEnvelope, ['MaterializedKBundleEnvelope']);

  return {
    kind: 'ConcreteKBundleProofInventory0',
    version: CHECKER_VERSION,

    kernelRuleCount: KERNEL_RULES0.length,
    conformanceNodeCount: k0Nodes.length,
    conformanceNodeIds: k0NodeIds,
    conformanceRules,
    missingKernelRules,
    kernelRuleCoverageComplete: missingKernelRules.length === 0,

    sigmaTheoremCount: sigmaEntries.length,
    sigmaTheoremIds,
    requiredSigmaTheorems: [...SIGMA_REQUIRED_THEOREMS0],
    missingSigmaTheorems,
    sigmaCoverageComplete: missingSigmaTheorems.length === 0,
    sigmaProofRefs,
    sigmaEntriesWithoutProofRefs,
    unresolvedSigmaProofRefs,
    sigmaProofRefsResolve: unresolvedSigmaProofRefs.length === 0 && sigmaEntriesWithoutProofRefs.length === 0,

    reflectionCount: reflectionEntries.length,
    reflectionCheckers,
    requiredReflectionCheckers: [...REFLECTION_REQUIRED_CHECKERS0],
    missingReflectionCheckers,
    reflectionCoverageComplete: missingReflectionCheckers.length === 0,
    reflectionProofRefs,
    reflectionsWithoutProofRefs,
    unresolvedReflectionProofRefs,
    reflectionProofRefsResolve: unresolvedReflectionProofRefs.length === 0 && reflectionsWithoutProofRefs.length === 0,

    noOpaqueProofRefs: opaqueHit === null,
    opaqueProofHit: opaqueHit,
    noExecutableMinSymbols: executableMinHit === null,
    executableMinHit,
  };
}

export async function CheckConcreteMaterializedKBundle0(
  input,
  config = makeConcreteMaterializedKBundleConfig0(),
) {
  const checker = 'CheckConcreteMaterializedKBundle0';
  const ledger = [];
  const cfg = makeConcreteMaterializedKBundleConfig0(config);
  const envelope = normalizeInput0(input);

  const cfgCheck = validateConfig0(cfg);

  ledger.push({
    phase: 'config',
    status: cfgCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(cfgCheck.nf ?? cfgCheck.witness ?? null),
  });

  if (!cfgCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: cfgCheck.path,
      witness: cfgCheck.witness,
      ledger,
    });
  }

  const shape = validateShape0(envelope);

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

  if (cfg.checkMaterializedKBundle === true) {
    const record = await CheckMaterializedKBundle0(
      envelope.MaterializedKBundleEnvelope,
      cfg.materializedKBundleConfig ?? {},
    );
    const result = recordToValidation0(record, ['MaterializedKBundleEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedKBundle0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.MaterializedKBundle`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkKBundle === true) {
    const record = await CheckKBundle0(envelope.MaterializedKBundleEnvelope);
    const result = recordToValidation0(record, ['MaterializedKBundleEnvelope']);

    ledger.push({
      phase: 'CheckKBundle0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.KBundle`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const recomputedInventory = makeConcreteKBundleProofInventory0(envelope.MaterializedKBundleEnvelope);

  if (cfg.checkProofInventory === true) {
    const proofInventory = validateProofInventory0(envelope.ProofInventory, recomputedInventory);

    ledger.push({
      phase: 'proofInventory',
      status: proofInventory.ok ? 'pass' : 'fail',
      digest: digestCanonical0(proofInventory.nf ?? proofInventory.witness ?? null),
    });

    if (!proofInventory.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.proofInventory`,
        path: proofInventory.path,
        witness: proofInventory.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope);

    ledger.push({
      phase: 'jsonMaterialized',
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
  }

  const markerInventory = collectFixtureMarkers0(envelope, ['ConcreteMaterializedKBundle0']);

  ledger.push({
    phase: 'fixtureMarkerInventory',
    status: 'pass',
    digest: digestCanonical0(markerInventory),
  });

  if (cfg.rejectFixtureMarkers === true) {
    const markers = validateNoForbiddenFixtureMarkers0(markerInventory, cfg);

    ledger.push({
      phase: 'fixtureMarkers',
      status: markers.ok ? 'pass' : 'fail',
      digest: digestCanonical0(markers.nf ?? markers.witness ?? null),
    });

    if (!markers.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.fixtureMarkers`,
        path: markers.path,
        witness: markers.witness,
        ledger,
      });
    }
  }

  if (cfg.checkLinkage === true) {
    const linkage = validateLinkage0(envelope, recomputedInventory);

    ledger.push({
      phase: 'linkage',
      status: linkage.ok ? 'pass' : 'fail',
      digest: digestCanonical0(linkage.nf ?? linkage.witness ?? null),
    });

    if (!linkage.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.linkage`,
        path: linkage.path,
        witness: linkage.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'ConcreteMaterializedKBundle0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,

    materializedKBundleDigest: digestCanonical0(envelope.MaterializedKBundleEnvelope),
    bootDigest: digestCanonical0(envelope.Boot0),
    kimplDigest: digestCanonical0(envelope.KImpl),
    k0Digest: digestCanonical0(envelope.K0),
    sigmaDigest: digestCanonical0(envelope.PSigma),
    reflectionDigest: digestCanonical0(envelope.ReflectionRegistry),
    proofInventoryDigest: digestCanonical0(recomputedInventory),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),

    kernelRuleCount: recomputedInventory.kernelRuleCount,
    conformanceNodeCount: recomputedInventory.conformanceNodeCount,
    kernelRuleCoverageComplete: recomputedInventory.kernelRuleCoverageComplete,

    sigmaTheoremCount: recomputedInventory.sigmaTheoremCount,
    sigmaCoverageComplete: recomputedInventory.sigmaCoverageComplete,
    sigmaProofRefsResolve: recomputedInventory.sigmaProofRefsResolve,

    reflectionCount: recomputedInventory.reflectionCount,
    reflectionCoverageComplete: recomputedInventory.reflectionCoverageComplete,
    reflectionProofRefsResolve: recomputedInventory.reflectionProofRefsResolve,

    noOpaqueProofRefs: recomputedInventory.noOpaqueProofRefs,
    noExecutableMinSymbols: recomputedInventory.noExecutableMinSymbols,

    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
    allowSyntheticScaffoldMarker: cfg.allowSyntheticScaffoldMarker,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeConcreteMaterializedKBundleFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedKBundleFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteMaterializedKBundle0(options);
  const checked = await CheckConcreteMaterializedKBundle0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedKBundle0.json');
  const materializedKBundlePath = path.join(outDir, 'MaterializedKBundle0.json');
  const proofInventoryPath = path.join(outDir, 'ConcreteKBundleProofInventory0.json');
  const kimplPath = path.join(outDir, 'KImpl0.json');
  const k0Path = path.join(outDir, 'K0.json');
  const sigmaPath = path.join(outDir, 'SigmaRegistry0.json');
  const reflectionPath = path.join(outDir, 'ReflectionRegistry0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedKBundle0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(materializedKBundlePath, envelope.MaterializedKBundleEnvelope);
  await writeJsonFile0(proofInventoryPath, envelope.ProofInventory);
  await writeJsonFile0(kimplPath, envelope.KImpl);
  await writeJsonFile0(k0Path, envelope.K0);
  await writeJsonFile0(sigmaPath, envelope.PSigma);
  await writeJsonFile0(reflectionPath, envelope.ReflectionRegistry);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      materializedKBundlePath,
      proofInventoryPath,
      kimplPath,
      k0Path,
      sigmaPath,
      reflectionPath,
      checkPath,
    },
  };
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'MaterializedKBundle0') {
    const proofInventory = makeConcreteKBundleProofInventory0(input);

    return {
      kind: 'ConcreteMaterializedKBundle0',
      version: CHECKER_VERSION,
      MaterializedKBundleEnvelope: input,
      Boot0: input.Boot0,
      KImpl: input.KImpl,
      K0: input.K0,
      PSigma: input.PSigma,
      ReflectionRegistry: input.ReflectionRegistry,
      ProofInventory: proofInventory,
      Linkage: {
        kind: 'ConcreteMaterializedKBundleLinkage0',
        version: CHECKER_VERSION,
        materializedKBundleDigest: digestCanonical0(input),
        bootDigest: digestCanonical0(input.Boot0),
        kimplDigest: digestCanonical0(input.KImpl),
        k0Digest: digestCanonical0(input.K0),
        sigmaDigest: digestCanonical0(input.PSigma),
        reflectionDigest: digestCanonical0(input.ReflectionRegistry),
        proofInventoryDigest: digestCanonical0(proofInventory),
        kernelRuleCount: proofInventory.kernelRuleCount,
        conformanceNodeCount: proofInventory.conformanceNodeCount,
        sigmaTheoremCount: proofInventory.sigmaTheoremCount,
        reflectionCount: proofInventory.reflectionCount,
      },
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedKBundleConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedKBundleConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedKBundleConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedKBundleConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkMaterializedKBundle',
    'checkKBundle',
    'checkProofInventory',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedKBundleConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.materializedKBundleConfig)) {
    return validationReject0(['materializedKBundleConfig'], 'materializedKBundleConfig must be an object', {
      actual: typeof config.materializedKBundleConfig,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedKBundleConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedKBundle0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedKBundle0') {
    return validationReject0(['kind'], 'ConcreteMaterializedKBundle0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  for (const field of [
    'MaterializedKBundleEnvelope',
    'Boot0',
    'KImpl',
    'K0',
    'PSigma',
    'ReflectionRegistry',
    'ProofInventory',
  ]) {
    if (!isPlainObject(envelope[field])) {
      return validationReject0([field], `ConcreteMaterializedKBundle0 must include ${field}`, {
        actual: typeof envelope[field],
      });
    }
  }

  if (envelope.MaterializedKBundleEnvelope.KImpl !== envelope.KImpl) {
    const expected = digestCanonical0(envelope.MaterializedKBundleEnvelope.KImpl);
    const actual = digestCanonical0(envelope.KImpl);

    if (!sameDigestHex0(actual, expected)) {
      return validationReject0(['KImpl'], 'top-level KImpl must match inner MaterializedKBundleEnvelope.KImpl', {
        expected,
        actual,
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedKBundleShape0NF',
  });
}

function validateProofInventory0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['ProofInventory'], 'ConcreteKBundleProofInventory0 must match recomputed proof inventory', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
    });
  }

  const requiredTrue = [
    'kernelRuleCoverageComplete',
    'sigmaCoverageComplete',
    'sigmaProofRefsResolve',
    'reflectionCoverageComplete',
    'reflectionProofRefsResolve',
    'noOpaqueProofRefs',
    'noExecutableMinSymbols',
  ];

  for (const field of requiredTrue) {
    if (expected[field] !== true) {
      return validationReject0(['ProofInventory', field], `ConcreteKBundleProofInventory0 must certify ${field}`, {
        actual: expected[field],
        missingKernelRules: expected.missingKernelRules,
        missingSigmaTheorems: expected.missingSigmaTheorems,
        sigmaEntriesWithoutProofRefs: expected.sigmaEntriesWithoutProofRefs,
        unresolvedSigmaProofRefs: expected.unresolvedSigmaProofRefs,
        missingReflectionCheckers: expected.missingReflectionCheckers,
        reflectionsWithoutProofRefs: expected.reflectionsWithoutProofRefs,
        unresolvedReflectionProofRefs: expected.unresolvedReflectionProofRefs,
        opaqueProofHit: expected.opaqueProofHit,
        executableMinHit: expected.executableMinHit,
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteKBundleProofInventory0NF',
    proofInventoryDigest: digestCanonical0(expected),
    kernelRuleCount: expected.kernelRuleCount,
    conformanceNodeCount: expected.conformanceNodeCount,
    sigmaTheoremCount: expected.sigmaTheoremCount,
    reflectionCount: expected.reflectionCount,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ConcreteMaterializedKBundle0'], 'ConcreteMaterializedKBundle0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ConcreteMaterializedKBundle0'], 'ConcreteMaterializedKBundle0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedKBundleJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope, proofInventory) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteMaterializedKBundleLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedKBundle0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = {
    materializedKBundleDigest: digestCanonical0(envelope.MaterializedKBundleEnvelope),
    bootDigest: digestCanonical0(envelope.Boot0),
    kimplDigest: digestCanonical0(envelope.KImpl),
    k0Digest: digestCanonical0(envelope.K0),
    sigmaDigest: digestCanonical0(envelope.PSigma),
    reflectionDigest: digestCanonical0(envelope.ReflectionRegistry),
    proofInventoryDigest: digestCanonical0(proofInventory),
  };

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  for (const [field, expectedValue] of Object.entries({
    kernelRuleCount: proofInventory.kernelRuleCount,
    conformanceNodeCount: proofInventory.conformanceNodeCount,
    sigmaTheoremCount: proofInventory.sigmaTheoremCount,
    reflectionCount: proofInventory.reflectionCount,
  })) {
    if (envelope.Linkage[field] !== expectedValue) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedValue,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedKBundleLinkage0NF',
    present: true,
    ...expected,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteMaterializedKBundleFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === 'synthetic').length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== 'synthetic').length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== 'synthetic' ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete materialized KBundle contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedKBundleNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function scanFixtureMarkers0(value, pathNow, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of CONCRETE_K_FORBIDDEN_MARKERS0) {
      if (lower.includes(marker)) {
        hits.push({
          path: pathNow,
          marker,
          value,
        });
      }
    }

    return;
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      scanFixtureMarkers0(value[index], [...pathNow, index], hits);
    }

    return;
  }

  if (!isPlainObject(value)) {
    return;
  }

  for (const key of Object.keys(value)) {
    scanFixtureMarkers0(value[key], [...pathNow, key], hits);
  }
}

function sigmaEntryMatches0(entry, required) {
  const haystack = [
    entry?.id,
    entry?.theorem,
    entry?.name,
  ].filter((value) => typeof value === 'string');

  return haystack.some((value) => value === required || value.endsWith(`.${required}`));
}

function firstOpaqueProofMarker0(value, pathNow) {
  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of OPAQUE_PROOF_MARKERS0) {
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

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = firstOpaqueProofMarker0(value[index], [...pathNow, index]);

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
    const hit = firstOpaqueProofMarker0(value[key], [...pathNow, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function firstForbiddenExecutableSymbol0(value, pathNow) {
  if (value === null || value === undefined) {
    return null;
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return null;
  }

  if (typeof value === 'string') {
    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = firstForbiddenExecutableSymbol0(value[index], [...pathNow, index]);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const [key, child] of Object.entries(value)) {
    if (EXECUTABLE_KEYS0.has(key)) {
      const hit = firstForbiddenSymbolInExecutableValue0(child, [...pathNow, key]);

      if (hit !== null) {
        return hit;
      }
    }

    const childHit = firstForbiddenExecutableSymbol0(child, [...pathNow, key]);

    if (childHit !== null) {
      return childHit;
    }
  }

  return null;
}

function firstForbiddenSymbolInExecutableValue0(value, pathNow) {
  if (value === null || value === undefined) {
    return null;
  }

  if (typeof value === 'string') {
    for (const symbol of FORBIDDEN_EXECUTABLE_SYMBOLS0) {
      if (value.includes(symbol)) {
        return {
          path: pathNow,
          symbol,
          value,
        };
      }
    }

    return null;
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = firstForbiddenSymbolInExecutableValue0(value[index], [...pathNow, index]);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const [key, child] of Object.entries(value)) {
    const hit = firstForbiddenSymbolInExecutableValue0(child, [...pathNow, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

function sameDigestHex0(actual, expected) {
  return (
    isPlainObject(actual) &&
    isPlainObject(expected) &&
    typeof actual.hex === 'string' &&
    typeof expected.hex === 'string' &&
    actual.hex === expected.hex &&
    (
      actual.alg === undefined ||
      expected.alg === undefined ||
      actual.alg === expected.alg
    )
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
