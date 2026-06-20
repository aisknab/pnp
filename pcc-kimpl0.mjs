/**
 * Reviewer orientation (non-normative).
 *
 * Purpose: validate the repository's small proof-kernel description, primitive
 * rule table, conformance suite, Sigma theorem schemas, reflection mappings, and
 * their aggregate KBundle.
 * Inputs: untrusted kernel, proof-node, schema-registry, reflection-registry, and
 * bundle records.
 * Outputs: phase-ledgered accept/reject records and canonical normal-form summaries.
 * Invariants enforced: required primitive-rule coverage, typed and acyclic proof
 * nodes, bounded side conditions/imports, no opaque proof blobs, no executable
 * minimization symbols, required Sigma entries, and required reflection entries.
 * Assumptions not checked: local mathematical soundness of each primitive rule,
 * adequacy of a Sigma theorem, or correctness of mapping a checker predicate to a
 * mathematical theorem. Those are part of the independent trusted-base audit.
 * Failure modes: malformed tables, missing rules, bad premises, cycles, bounds,
 * forbidden executable content, or mismatched registry entries return named rejects.
 * Naming: `KImpl` is the versioned PCC-K implementation record; `Sigma` denotes
 * schema-level theorem instances, not a JavaScript sum operation.
 */

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;

// Primitive proof-rule identifiers accepted by the version-zero kernel schema.
// This table is an implementation interface, not a proof that the rules are sound;
// each rule still requires an independent local-soundness audit.
export const KERNEL_RULES0 = Object.freeze([
  'Eq',
  'Subst',
  'Record',
  'DAGInd',
  'LedgerInd',
  'OblTopoInd',
  'TraceInd',
  'FiniteExhaust',
  'DPInd',
  'Hall',
  'RankInd',
  'MinCounterexample',
  'IntArith',
  'Transport',
  'TruthVec',
  'FiniteRel',
]);

export const SIGMA_REQUIRED_THEOREMS0 = Object.freeze([
  'V53',
  'V54',
]);

export const REFLECTION_REQUIRED_CHECKERS0 = Object.freeze([
  'CheckVerifierFrag0',
  'CheckBoot0',
  'CheckBootBatch0',
  'CheckBootAudit0',
  'CheckKImpl0',
]);

const KIMPL_REQUIRED_FIELDS0 = Object.freeze([
  'IfaceHash',
  'SchedHash',
  'Sorts',
  'Constructors',
  'TermGrammar',
  'FormulaGrammar',
  'JudgmentGrammar',
  'RuleTable',
  'SideLang',
  'ProofDAGChecker',
  'SigmaChecker',
  'ReflectionChecker',
  'InstanceChecker',
  'BoundsK',
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

export function makeKernelRuleTable0() {
  return KERNEL_RULES0.map((name, index) => Object.freeze({
    kind: 'KernelPrimitiveRule0',
    version: CHECKER_VERSION,
    name,
    index,
    primitive: true,
    modeSafe: true,
    premiseSorts: [],
    conclusionSort: 'Judgment',
    sideConditionSort: 'SideCond',
  }));
}

export function makeKernelProofNode0({
  id,
  RuleName,
  Mode = 'Full',
  Context = {},
  Premises = [],
  Conclusion,
  Payload = {},
  SideConds = [],
  Imports = [],
  Discharges = [],
  BoundsRef = {
    tag: 'BoundsRef0',
    id: 'K.bounds.synthetic',
  },
}) {
  if (!isNonEmptyString(id)) {
    throw new TypeError('makeKernelProofNode0 requires a non-empty id');
  }

  if (!isNonEmptyString(RuleName)) {
    throw new TypeError('makeKernelProofNode0 requires a non-empty RuleName');
  }

  const node = {
    kind: 'KProofNode0',
    version: CHECKER_VERSION,
    id,
    RuleName,
    Mode,
    Context,
    Premises,
    Conclusion: Conclusion ?? {
      tag: 'Judgment0',
      rule: RuleName,
      id,
    },
    Payload,
    SideConds,
    Imports,
    Discharges,
    BoundsRef,
  };

  return Object.freeze({
    ...node,
    Digest: digestCanonical0(node),
  });
}

export function makeKernelConformanceSuite0() {
  return {
    kind: 'KConformance0',
    version: CHECKER_VERSION,
    suiteId: 'K0.synthetic.primitive-conformance',
    nodes: KERNEL_RULES0.map((ruleName) => makeKernelProofNode0({
      id: `conf.${ruleName}`,
      RuleName: ruleName,
      Conclusion: {
        tag: 'PrimitiveConformanceJudgment0',
        rule: ruleName,
      },
    })),
  };
}

export function makeSigmaRegistry0() {
  return {
    kind: 'SigmaRegistry0',
    version: CHECKER_VERSION,
    theorems: [
      {
        kind: 'SigmaTheorem0',
        id: 'Sigma.V53',
        theorem: 'V53.ConstantCutHypergraphRigidity',
        conclusion: {
          tag: 'HypergraphRigidityConclusion0',
          statement: 'constant-cut nonnegative hypergraph rigidity',
        },
        proofRefs: [],
        modeSafe: true,
      },
      {
        kind: 'SigmaTheorem0',
        id: 'Sigma.V54',
        theorem: 'V54.ConsumerAntichainNormalForm',
        conclusion: {
          tag: 'ConsumerAntichainConclusion0',
          statement: 'monotone consumer antichain normal form',
        },
        proofRefs: [],
        modeSafe: true,
      },
    ],
  };
}

export function makeReflectionRegistry0() {
  return {
    kind: 'ReflectionRegistry0',
    version: CHECKER_VERSION,
    reflections: REFLECTION_REQUIRED_CHECKERS0.map((checker) => ({
      kind: 'Reflection0',
      checker,
      theorem: `${checker}.Soundness`,
      publicConclusion: {
        tag: 'CheckerSoundnessConclusion0',
        checker,
      },
      modeSafe: true,
    })),
  };
}

export function makeSyntheticKImpl0(overrides = {}) {
  return {
    kind: 'KImpl0',
    version: CHECKER_VERSION,
    IfaceHash: {
      alg: 'SHA256',
      hex: '7c923cae83c49a867df1a6a9e1b6367ef0deeae87fc836996f0e01ef1593f130',
    },
    SchedHash: {
      alg: 'SHA256',
      hex: '5b5be0411b2ac555e237b4d6470bab10a7e2f52ef0c7c344e261da638b0648c6',
    },
    Sorts: {
      Term: 'Term',
      Formula: 'Formula',
      Judgment: 'Judgment',
      SideCond: 'SideCond',
      ProofNode: 'ProofNode',
    },
    Constructors: {
      Var: 'Var',
      App: 'App',
      Eq: 'Eq',
      Judgment: 'Judgment',
      ProofNode: 'ProofNode',
    },
    TermGrammar: {
      kind: 'TermGrammar0',
      constructors: ['Var', 'App', 'Tuple', 'Record'],
    },
    FormulaGrammar: {
      kind: 'FormulaGrammar0',
      constructors: ['Eq', 'And', 'Implies', 'ForallFinite'],
    },
    JudgmentGrammar: {
      kind: 'JudgmentGrammar0',
      constructors: ['Derives', 'Accepts', 'Rejects', 'Bounds'],
    },
    RuleTable: makeKernelRuleTable0(),
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
      ],
    },
    ProofDAGChecker: {
      kind: 'ProofDAGChecker0',
      total: true,
      deterministic: true,
      acyclic: true,
    },
    SigmaChecker: {
      kind: 'SigmaChecker0',
      total: true,
      deterministic: true,
    },
    ReflectionChecker: {
      kind: 'ReflectionChecker0',
      total: true,
      deterministic: true,
    },
    InstanceChecker: {
      kind: 'InstanceChecker0',
      total: true,
      deterministic: true,
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
      note: 'synthetic proof-kernel implementation witness',
    },
    ...overrides,
  };
}

/**
 * Validates the kernel implementation descriptor and optional primitive proof DAG.
 * Input: KImpl0 record with grammars, rule table, checker descriptors, bounds, and PiK.
 * Output: accepted KImpl normal form or phase-specific reject record.
 * Enforces: required rule table, descriptor flags, bounded proof shape, no opaque proof,
 * no hidden executable minimization, and typed/acyclic optional proof nodes.
 * Does not check: mathematical soundness of the primitive rules or adequacy of the
 * represented logic.
 * Failure modes: shape/rule/descriptor/bound/no-min/opaque/DAG rejection.
 */
export async function CheckKImpl0(kimpl) {
  const checker = 'CheckKImpl0';
  const ledger = [];

  const shape = validateKImplShape0(kimpl);

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

  const ruleTable = validateKernelRuleTable0(kimpl.RuleTable);

  ledger.push({
    phase: 'RuleTable',
    status: ruleTable.ok ? 'pass' : 'fail',
    digest: digestCanonical0(ruleTable.nf ?? ruleTable.witness ?? null),
  });

  if (!ruleTable.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.RuleTable`,
      path: ruleTable.path,
      witness: ruleTable.witness,
      ledger,
    });
  }

  const checkerDescriptors = validateKernelCheckerDescriptors0(kimpl);

  ledger.push({
    phase: 'checkerDescriptors',
    status: checkerDescriptors.ok ? 'pass' : 'fail',
    digest: digestCanonical0(checkerDescriptors.nf ?? checkerDescriptors.witness ?? null),
  });

  if (!checkerDescriptors.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.checkerDescriptors`,
      path: checkerDescriptors.path,
      witness: checkerDescriptors.witness,
      ledger,
    });
  }

  const bounds = validateBoundsK0(kimpl.BoundsK);

  ledger.push({
    phase: 'BoundsK',
    status: bounds.ok ? 'pass' : 'fail',
    digest: digestCanonical0(bounds.nf ?? bounds.witness ?? null),
  });

  if (!bounds.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.BoundsK`,
      path: bounds.path,
      witness: bounds.witness,
      ledger,
    });
  }

  const noOpaque = validateNoOpaqueProof0(kimpl, ['KImpl']);

  ledger.push({
    phase: 'noOpaqueProof',
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

  const noHiddenMin = validateNoHiddenExecutableMin0(kimpl, ['KImpl']);

  ledger.push({
    phase: 'noHiddenMin',
    status: noHiddenMin.ok ? 'pass' : 'fail',
    digest: digestCanonical0(noHiddenMin.nf ?? noHiddenMin.witness ?? null),
  });

  if (!noHiddenMin.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.noHiddenMin`,
      path: noHiddenMin.path,
      witness: noHiddenMin.witness,
      ledger,
    });
  }

  const proofDAG = validateOptionalKernelProofDAG0(kimpl, ruleTable.ruleMap);

  ledger.push({
    phase: 'ProofDAG',
    status: proofDAG.ok ? 'pass' : 'fail',
    digest: digestCanonical0(proofDAG.nf ?? proofDAG.witness ?? null),
  });

  if (!proofDAG.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.ProofDAG`,
      path: proofDAG.path,
      witness: proofDAG.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'KImpl0NF',
    checker,
    version: CHECKER_VERSION,
    ifaceHashDigest: digestCanonical0(kimpl.IfaceHash),
    schedHashDigest: digestCanonical0(kimpl.SchedHash),
    sortCount: Object.keys(kimpl.Sorts).length,
    constructorCount: Object.keys(kimpl.Constructors).length,
    primitiveRuleCount: KERNEL_RULES0.length,
    ruleCount: ruleTable.nf.ruleCount,
    proofNodeCount: proofDAG.nf.nodeCount,
    bounds: bounds.nf,
    piKDigest: digestCanonical0(getPiK0(kimpl)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckConformance0(kimpl, suite) {
  const checker = 'CheckConformance0';
  const ledger = [];

  const kimplResult = await CheckKImpl0(kimpl);

  ledger.push({
    phase: 'CheckKImpl0',
    status: isRejectRecord0(kimplResult) ? 'fail' : 'pass',
    digest: kimplResult.Digest ?? kimplResult.digest,
  });

  if (isRejectRecord0(kimplResult)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.KImpl`,
      path: ['KImpl'],
      witness: {
        reason: 'CheckKImpl0 rejected',
        inner: compactReject0(kimplResult),
      },
      ledger,
    });
  }

  const effectiveSuite = suite ?? kimpl.K0 ?? kimpl.Conformance0 ?? kimpl.ConformanceSuite;
  const nodes = getConformanceNodes0(effectiveSuite);

  if (!Array.isArray(nodes)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: ['nodes'],
      witness: {
        reason: 'conformance suite must provide a nodes array',
      },
      ledger,
    });
  }

  const ruleTable = validateKernelRuleTable0(kimpl.RuleTable);
  const nodeCheck = validateKernelProofNodeSequence0(nodes, ruleTable.ruleMap, {
    pathBase: ['nodes'],
  });

  ledger.push({
    phase: 'nodes',
    status: nodeCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(nodeCheck.nf ?? nodeCheck.witness ?? null),
  });

  if (!nodeCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.nodes`,
      path: nodeCheck.path,
      witness: nodeCheck.witness,
      ledger,
    });
  }

  const coveredRules = new Set(nodes.map((node) => String(node.RuleName ?? node.ruleName ?? node.rule)));

  for (const ruleName of KERNEL_RULES0) {
    if (!coveredRules.has(ruleName)) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.coverage`,
        path: ['coverage', ruleName],
        witness: {
          reason: 'conformance suite is missing a primitive rule',
          rule: ruleName,
        },
        ledger,
      });
    }
  }

  const nf = {
    kind: 'KConformance0NF',
    checker,
    version: CHECKER_VERSION,
    suiteId: effectiveSuite?.suiteId ?? effectiveSuite?.id ?? 'K0',
    primitiveRuleCount: KERNEL_RULES0.length,
    nodeCount: nodes.length,
    coveredRules: KERNEL_RULES0,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckSigmaRegistry0(registry) {
  const checker = 'CheckSigmaRegistry0';
  const ledger = [];

  if (!isPlainObject(registry)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: [],
      witness: {
        reason: 'Sigma registry must be an object',
        actual: typeof registry,
      },
      ledger,
    });
  }

  if (registry.kind !== undefined && registry.kind !== 'SigmaRegistry0') {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: ['kind'],
      witness: {
        reason: 'Sigma registry kind must be SigmaRegistry0 when present',
        actual: registry.kind,
      },
      ledger,
    });
  }

  const entries = getSigmaEntries0(registry);

  if (!Array.isArray(entries)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: ['theorems'],
      witness: {
        reason: 'Sigma registry must provide a theorem array',
      },
      ledger,
    });
  }

  const seen = new Set();

  for (let index = 0; index < entries.length; index += 1) {
    const entry = entries[index];

    if (!isPlainObject(entry)) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.entry.${String(index).padStart(4, '0')}`,
        path: ['theorems', index],
        witness: {
          reason: 'Sigma theorem entry must be an object',
        },
        ledger,
      });
    }

    const id = entry.id ?? entry.theorem ?? entry.name;

    if (!isNonEmptyString(id)) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.entry.${String(index).padStart(4, '0')}`,
        path: ['theorems', index, 'id'],
        witness: {
          reason: 'Sigma theorem entry must have a non-empty id, theorem, or name',
        },
        ledger,
      });
    }

    if (seen.has(id)) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.entry.${String(index).padStart(4, '0')}`,
        path: ['theorems', index, 'id'],
        witness: {
          reason: 'Sigma theorem ids must be unique',
          id,
        },
        ledger,
      });
    }

    seen.add(id);

    if (entry.conclusion === undefined && entry.Conclusion === undefined) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.entry.${String(index).padStart(4, '0')}`,
        path: ['theorems', index, 'conclusion'],
        witness: {
          reason: 'Sigma theorem must have a conclusion',
          id,
        },
        ledger,
      });
    }

    const opaque = validateNoOpaqueProof0(entry, ['theorems', index]);

    if (!opaque.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.opaqueProof`,
        path: opaque.path,
        witness: opaque.witness,
        ledger,
      });
    }

    const noHidden = validateNoHiddenExecutableMin0(entry, ['theorems', index]);

    if (!noHidden.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.noHiddenMin`,
        path: noHidden.path,
        witness: noHidden.witness,
        ledger,
      });
    }

    ledger.push({
      phase: 'sigmaEntry',
      index,
      id,
      status: 'pass',
      digest: digestCanonical0(entry),
    });
  }

  for (const required of SIGMA_REQUIRED_THEOREMS0) {
    if (!entries.some((entry) => sigmaEntryMatches0(entry, required))) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.coverage`,
        path: ['coverage', required],
        witness: {
          reason: 'Sigma registry is missing a required theorem',
          theorem: required,
        },
        ledger,
      });
    }
  }

  const nf = {
    kind: 'SigmaRegistry0NF',
    checker,
    version: CHECKER_VERSION,
    theoremCount: entries.length,
    requiredTheorems: SIGMA_REQUIRED_THEOREMS0,
    theoremIds: entries.map((entry) => String(entry.id ?? entry.theorem ?? entry.name)).sort(),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

/**
 * Checks the shape, coverage, and internal references of reflection entries.
 * Input: registry mapping checker identifiers to reflected theorem conclusions.
 * Output: accepted registry summary or first malformed/missing/mismatched entry reject.
 * Enforces: required checker coverage, unique IDs, typed proof references, and the
 * repository's declared reflection metadata.
 * Does not check: that the checker predicate is actually equivalent to the reflected
 * mathematical theorem; that comparison is an independent review obligation.
 * Failure modes: malformed registry/entry, duplicate or missing checker, bad proof ref,
 * forbidden executable content, or opaque proof data.
 */
export async function CheckReflectionRegistry0(registry) {
  const checker = 'CheckReflectionRegistry0';
  const ledger = [];

  if (!isPlainObject(registry)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: [],
      witness: {
        reason: 'Reflection registry must be an object',
        actual: typeof registry,
      },
      ledger,
    });
  }

  if (registry.kind !== undefined && registry.kind !== 'ReflectionRegistry0') {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: ['kind'],
      witness: {
        reason: 'Reflection registry kind must be ReflectionRegistry0 when present',
        actual: registry.kind,
      },
      ledger,
    });
  }

  const entries = getReflectionEntries0(registry);

  if (!Array.isArray(entries)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: ['reflections'],
      witness: {
        reason: 'Reflection registry must provide a reflections array',
      },
      ledger,
    });
  }

  const seen = new Set();

  for (let index = 0; index < entries.length; index += 1) {
    const entry = entries[index];

    if (!isPlainObject(entry)) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.entry.${String(index).padStart(4, '0')}`,
        path: ['reflections', index],
        witness: {
          reason: 'Reflection entry must be an object',
        },
        ledger,
      });
    }

    if (!isNonEmptyString(entry.checker)) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.entry.${String(index).padStart(4, '0')}`,
        path: ['reflections', index, 'checker'],
        witness: {
          reason: 'Reflection entry must name a checker',
        },
        ledger,
      });
    }

    if (seen.has(entry.checker)) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.entry.${String(index).padStart(4, '0')}`,
        path: ['reflections', index, 'checker'],
        witness: {
          reason: 'Reflection checker names must be unique',
          checker: entry.checker,
        },
        ledger,
      });
    }

    seen.add(entry.checker);

    if (entry.publicConclusion === undefined && entry.Conclusion === undefined && entry.theorem === undefined) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.entry.${String(index).padStart(4, '0')}`,
        path: ['reflections', index, 'publicConclusion'],
        witness: {
          reason: 'Reflection entry must expose a public theorem conclusion',
          checker: entry.checker,
        },
        ledger,
      });
    }

    const opaque = validateNoOpaqueProof0(entry, ['reflections', index]);

    if (!opaque.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.opaqueProof`,
        path: opaque.path,
        witness: opaque.witness,
        ledger,
      });
    }

    const noHidden = validateNoHiddenExecutableMin0(entry, ['reflections', index]);

    if (!noHidden.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.noHiddenMin`,
        path: noHidden.path,
        witness: noHidden.witness,
        ledger,
      });
    }

    ledger.push({
      phase: 'reflectionEntry',
      index,
      checker: entry.checker,
      status: 'pass',
      digest: digestCanonical0(entry),
    });
  }

  for (const required of REFLECTION_REQUIRED_CHECKERS0) {
    if (!seen.has(required)) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.coverage`,
        path: ['coverage', required],
        witness: {
          reason: 'Reflection registry is missing a required checker reflection',
          checker: required,
        },
        ledger,
      });
    }
  }

  const nf = {
    kind: 'ReflectionRegistry0NF',
    checker,
    version: CHECKER_VERSION,
    reflectionCount: entries.length,
    requiredCheckers: REFLECTION_REQUIRED_CHECKERS0,
    checkers: entries.map((entry) => entry.checker).sort(),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

/**
 * Runs the aggregate kernel, conformance, Sigma, and reflection checks.
 * Input: KBundle0 containing KImpl, conformance suite, Sigma registry, reflection
 * registry, and bundle linkage/proof records.
 * Output: an accepted bundle normal form with child digests or wrapped child rejection.
 * Enforces: all four kernel surfaces accept and agree with the bundle linkage.
 * Does not check: independent local soundness of rules/schemas/reflections.
 * Failure modes: malformed bundle, any child checker reject, linkage mismatch,
 * hidden-minimization occurrence, or opaque proof material.
 */
export async function CheckKBundle0(bundle) {
  const checker = 'CheckKBundle0';
  const ledger = [];

  if (!isPlainObject(bundle)) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: [],
      witness: {
        reason: 'K bundle must be an object',
        actual: typeof bundle,
      },
      ledger,
    });
  }

  const kimpl = bundle.KImpl ?? bundle.kimpl;
  const conformance = bundle.K0 ?? bundle.Conformance0 ?? bundle.ConformanceSuite;
  const sigma = bundle.PSigma ?? bundle.SigmaRegistry ?? bundle.sigmaRegistry ?? bundle['PΣ'];
  const reflections = bundle.ReflectionRegistry ?? bundle.reflectionRegistry ?? bundle.PRefl ?? bundle['Pref l'];

  const phases = [
    ['CheckKImpl0', await CheckKImpl0(kimpl)],
    ['CheckConformance0', await CheckConformance0(kimpl, conformance)],
    ['CheckSigmaRegistry0', await CheckSigmaRegistry0(sigma)],
    ['CheckReflectionRegistry0', await CheckReflectionRegistry0(reflections)],
  ];

  for (const [phase, result] of phases) {
    ledger.push({
      phase,
      status: isRejectRecord0(result) ? 'fail' : 'pass',
      digest: result.Digest ?? result.digest,
    });

    if (isRejectRecord0(result)) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.${phase}`,
        path: [phase],
        witness: {
          reason: `${phase} rejected`,
          inner: compactReject0(result),
        },
        ledger,
      });
    }
  }

  const nf = {
    kind: 'KBundle0NF',
    checker,
    version: CHECKER_VERSION,
    kimplDigest: phases[0][1].Digest,
    conformanceDigest: phases[1][1].Digest,
    sigmaDigest: phases[2][1].Digest,
    reflectionDigest: phases[3][1].Digest,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateKImplShape0(kimpl) {
  if (!isPlainObject(kimpl)) {
    return validationReject0([], 'KImpl0 must be an object', {
      actual: typeof kimpl,
    });
  }

  if (kimpl.kind !== undefined && kimpl.kind !== 'KImpl0') {
    return validationReject0(['kind'], 'KImpl0 kind must be KImpl0 when present', {
      actual: kimpl.kind,
    });
  }

  if (kimpl.version !== undefined && kimpl.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `KImpl0 version must be ${CHECKER_VERSION} when present`, {
      actual: kimpl.version,
    });
  }

  for (const field of KIMPL_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(kimpl, field)) {
      return validationReject0([field], 'KImpl0 is missing a required field', {
        field,
      });
    }
  }

  for (const field of [
    'Sorts',
    'Constructors',
    'TermGrammar',
    'FormulaGrammar',
    'JudgmentGrammar',
    'SideLang',
    'ProofDAGChecker',
    'SigmaChecker',
    'ReflectionChecker',
    'InstanceChecker',
    'BoundsK',
  ]) {
    if (!isPlainObject(kimpl[field])) {
      return validationReject0([field], `${field} must be an object`, {
        actual: typeof kimpl[field],
      });
    }
  }

  if (getPiK0(kimpl) === undefined) {
    return validationReject0(['PiK'], 'KImpl0 is missing PiK or ΠK', null);
  }

  return validationAccept0({
    kind: 'KImpl0ShapeNF',
  });
}

function validateKernelRuleTable0(ruleTable) {
  const normalized = normalizeRuleTable0(ruleTable);

  if (!normalized.ok) {
    return normalized;
  }

  const seen = new Set();
  const ruleMap = new Map();

  for (let index = 0; index < normalized.rules.length; index += 1) {
    const rule = normalized.rules[index];
    const name = getRuleName0(rule);

    if (!isNonEmptyString(name)) {
      return validationReject0(['RuleTable', index], 'kernel rule must have a non-empty name', {
        rule,
      });
    }

    if (seen.has(name)) {
      return validationReject0(['RuleTable', index, 'name'], 'kernel rule names must be unique', {
        name,
      });
    }

    seen.add(name);
    ruleMap.set(name, rule);

    if (isPlainObject(rule) && rule.modeSafe === false) {
      return validationReject0(['RuleTable', index, 'modeSafe'], 'kernel primitive rule must be mode-safe', {
        name,
      });
    }

    const opaque = findOpaqueProof0(rule, ['RuleTable', index]);

    if (opaque !== null) {
      return validationReject0(opaque.path, 'opaque proof material is not allowed in the kernel rule table', opaque);
    }
  }

  for (const required of KERNEL_RULES0) {
    if (!seen.has(required)) {
      return validationReject0(['RuleTable', required], 'kernel rule table is missing a primitive rule', {
        rule: required,
      });
    }
  }

  return {
    ok: true,
    ruleMap,
    nf: {
      kind: 'KernelRuleTable0NF',
      ruleCount: normalized.rules.length,
      primitiveRuleCount: KERNEL_RULES0.length,
      rules: Array.from(seen).sort(),
    },
  };
}

function normalizeRuleTable0(ruleTable) {
  if (Array.isArray(ruleTable)) {
    return validationAccept0({
      kind: 'KernelRuleTableShapeNF',
      form: 'array',
    }, {
      rules: ruleTable,
    });
  }

  if (isPlainObject(ruleTable)) {
    const rules = Object.entries(ruleTable).map(([name, value]) => {
      if (isPlainObject(value)) {
        return {
          ...value,
          name: value.name ?? value.RuleName ?? name,
        };
      }

      return {
        kind: 'KernelPrimitiveRule0',
        name,
        value,
      };
    });

    return validationAccept0({
      kind: 'KernelRuleTableShapeNF',
      form: 'object',
    }, {
      rules,
    });
  }

  return validationReject0(['RuleTable'], 'kernel rule table must be an array or object', {
    actual: typeof ruleTable,
  });
}

function validateKernelCheckerDescriptors0(kimpl) {
  for (const field of [
    'ProofDAGChecker',
    'SigmaChecker',
    'ReflectionChecker',
    'InstanceChecker',
  ]) {
    const descriptor = kimpl[field];

    if (descriptor.total === false) {
      return validationReject0([field, 'total'], 'kernel checker descriptor must be total', {
        field,
      });
    }

    if (descriptor.deterministic === false) {
      return validationReject0([field, 'deterministic'], 'kernel checker descriptor must be deterministic', {
        field,
      });
    }
  }

  return validationAccept0({
    kind: 'KernelCheckerDescriptors0NF',
    checkers: [
      'ProofDAGChecker',
      'SigmaChecker',
      'ReflectionChecker',
      'InstanceChecker',
    ],
  });
}

function validateBoundsK0(bounds) {
  for (const field of [
    'nodeLimit',
    'premiseLimit',
    'sideConditionLimit',
    'importLimit',
  ]) {
    if (!Number.isInteger(bounds[field]) || bounds[field] <= 0) {
      return validationReject0(['BoundsK', field], 'BoundsK numeric limit must be a positive integer', {
        field,
        actual: bounds[field],
      });
    }
  }

  if (
    bounds.polynomialExponent !== undefined &&
    (!Number.isInteger(bounds.polynomialExponent) || bounds.polynomialExponent <= 0)
  ) {
    return validationReject0(['BoundsK', 'polynomialExponent'], 'BoundsK polynomialExponent must be positive when present', {
      actual: bounds.polynomialExponent,
    });
  }

  return validationAccept0({
    kind: 'BoundsK0NF',
    nodeLimit: bounds.nodeLimit,
    premiseLimit: bounds.premiseLimit,
    sideConditionLimit: bounds.sideConditionLimit,
    importLimit: bounds.importLimit,
    polynomialExponent: bounds.polynomialExponent ?? null,
  });
}

function validateNoOpaqueProof0(value, path) {
  const opaque = findOpaqueProof0(value, path);

  if (opaque !== null) {
    return validationReject0(opaque.path, 'opaque proof material is not allowed', opaque);
  }

  return validationAccept0({
    kind: 'NoOpaqueProof0NF',
  });
}

function validateNoHiddenExecutableMin0(value, path) {
  const hit = findForbiddenExecutableUse0(value, path, false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'NoHiddenExecutableMin0NF',
  });
}

function validateOptionalKernelProofDAG0(kimpl, ruleMap) {
  const nodes = kimpl.ProofDAG ?? kimpl.proofDAG ?? kimpl.proofNodes ?? kimpl.ProofNodes;

  if (nodes === undefined) {
    return validationAccept0({
      kind: 'KernelProofDAG0NF',
      nodeCount: 0,
      ids: [],
    });
  }

  return validateKernelProofNodeSequence0(nodes, ruleMap, {
    pathBase: ['ProofDAG'],
  });
}

function validateKernelProofNodeSequence0(nodes, ruleMap, {
  pathBase,
} = {}) {
  if (!Array.isArray(nodes)) {
    return validationReject0(pathBase ?? ['nodes'], 'kernel proof nodes must be an array', {
      actual: typeof nodes,
    });
  }

  const acceptedIds = new Set();
  const nodeIds = [];

  for (let index = 0; index < nodes.length; index += 1) {
    const result = validateKernelProofNode0(nodes[index], ruleMap, acceptedIds, [
      ...(pathBase ?? ['nodes']),
      index,
    ]);

    if (!result.ok) {
      return result;
    }

    acceptedIds.add(result.nodeId);
    nodeIds.push(result.nodeId);
  }

  return validationAccept0({
    kind: 'KernelProofDAG0NF',
    nodeCount: nodes.length,
    ids: nodeIds,
  });
}

function validateKernelProofNode0(node, ruleMap, acceptedIds, path) {
  if (!isPlainObject(node)) {
    return validationReject0(path, 'kernel proof node must be an object', {
      actual: typeof node,
    });
  }

  const id = node.id ?? node.ID;

  if (!isNonEmptyString(id)) {
    return validationReject0([...path, 'id'], 'kernel proof node must have a non-empty id', {
      actual: id,
    });
  }

  if (acceptedIds.has(id)) {
    return validationReject0([...path, 'id'], 'kernel proof node ids must be unique', {
      id,
    });
  }

  const ruleName = node.RuleName ?? node.ruleName ?? node.rule;

  if (!isNonEmptyString(ruleName)) {
    return validationReject0([...path, 'RuleName'], 'kernel proof node must name a rule', {
      actual: ruleName,
    });
  }

  if (!ruleMap.has(ruleName)) {
    return validationReject0([...path, 'RuleName'], 'kernel proof node references an unknown rule', {
      id,
      ruleName,
    });
  }

  const mode = node.Mode ?? node.mode ?? 'Full';

  if (!isNonEmptyString(mode)) {
    return validationReject0([...path, 'Mode'], 'kernel proof node mode must be a non-empty string', {
      id,
      mode,
    });
  }

  const premises = node.Premises ?? node.premises ?? [];

  if (!Array.isArray(premises)) {
    return validationReject0([...path, 'Premises'], 'kernel proof node Premises must be an array', {
      id,
    });
  }

  for (let premiseIndex = 0; premiseIndex < premises.length; premiseIndex += 1) {
    const premiseId = normalizeProofRefId0(premises[premiseIndex]);

    if (!isNonEmptyString(premiseId)) {
      return validationReject0([...path, 'Premises', premiseIndex], 'proof premise must resolve to a non-empty id', {
        id,
        premise: premises[premiseIndex],
      });
    }

    if (!acceptedIds.has(premiseId)) {
      return validationReject0([...path, 'Premises', premiseIndex], 'proof premise must reference an earlier node', {
        id,
        premiseId,
      });
    }
  }

  for (const field of ['SideConds', 'Imports', 'Discharges']) {
    const value = node[field] ?? node[field[0].toLowerCase() + field.slice(1)] ?? [];

    if (!Array.isArray(value)) {
      return validationReject0([...path, field], `${field} must be an array`, {
        id,
      });
    }
  }

  if (node.Conclusion === undefined && node.conclusion === undefined) {
    return validationReject0([...path, 'Conclusion'], 'kernel proof node must have a conclusion', {
      id,
    });
  }

  const opaque = findOpaqueProof0(node, path);

  if (opaque !== null) {
    return validationReject0(opaque.path, 'opaque proof material is not allowed in a kernel proof node', {
      id,
      opaque,
    });
  }

  const noHidden = findForbiddenExecutableUse0(node, path, false);

  if (noHidden !== null) {
    return validationReject0(noHidden.path, 'forbidden minimization symbol appears in executable proof-node position', {
      id,
      noHidden,
    });
  }

  const payload = node.Payload ?? node.payload ?? {};

  if (
    String(mode).trim().toLowerCase() === 'quot' &&
    isPlainObject(payload) &&
    payload.constructiveFullReplacement === true
  ) {
    return validationReject0([...path, 'Payload'], 'quotient proof node cannot construct a full replacement', {
      id,
      mode,
    });
  }

  const displayedDigest = node.Digest ?? node.digest;

  if (displayedDigest !== undefined) {
    const expectedDigest = digestCanonical0(proofNodeDigestMaterial0(node));

    if (!sameDigest0(displayedDigest, expectedDigest)) {
      return validationReject0([...path, 'Digest'], 'kernel proof node digest mismatch', {
        id,
        expectedDigest,
        displayedDigest,
      });
    }
  }

  return {
    ok: true,
    nodeId: id,
    nf: {
      kind: 'KernelProofNode0NF',
      id,
      ruleName,
      mode,
      premiseCount: premises.length,
    },
  };
}

function getConformanceNodes0(suite) {
  if (Array.isArray(suite)) {
    return suite;
  }

  if (!isPlainObject(suite)) {
    return null;
  }

  return suite.nodes ?? suite.Nodes ?? suite.proofNodes ?? suite.ProofNodes;
}

function getSigmaEntries0(registry) {
  return registry.theorems ?? registry.Theorems ?? registry.entries ?? registry.Entries ?? registry.Sigma;
}

function getReflectionEntries0(registry) {
  return registry.reflections ?? registry.Reflections ?? registry.entries ?? registry.Entries;
}

function sigmaEntryMatches0(entry, required) {
  const haystack = [
    entry.id,
    entry.name,
    entry.theorem,
    entry.Theorem,
  ]
    .filter((value) => value !== undefined && value !== null)
    .map((value) => String(value))
    .join(' ');

  return haystack.includes(required);
}

function normalizeProofRefId0(value) {
  if (typeof value === 'string') {
    return value;
  }

  if (isPlainObject(value)) {
    return value.id ?? value.ref ?? value.nodeId ?? value.NodeID ?? value.node;
  }

  return null;
}

function proofNodeDigestMaterial0(node) {
  const out = {};

  for (const key of Object.keys(node).sort()) {
    if (key !== 'Digest' && key !== 'digest') {
      out[key] = node[key];
    }
  }

  return out;
}

function sameDigest0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.alg === b.alg &&
    a.hex === b.hex
  );
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
    if (/opaque|proofblob|trustedblob|blob|assumeproof/i.test(key)) {
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
    if (inExecutablePosition && isForbiddenExecutableSymbol0(value)) {
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

function isForbiddenExecutableSymbol0(value) {
  return FORBIDDEN_EXECUTABLE_SYMBOLS0.some((symbol) => symbol === value);
}

function getRuleName0(rule) {
  if (typeof rule === 'string') {
    return rule;
  }

  if (isPlainObject(rule)) {
    return rule.name ?? rule.RuleName ?? rule.id;
  }

  return null;
}

function getPiK0(kimpl) {
  return kimpl.PiK ?? kimpl['ΠK'] ?? kimpl.piK;
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

function validationAccept0(nf, extra = {}) {
  return {
    ok: true,
    nf,
    ...extra,
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