import { createHash } from 'node:crypto';

const VERSION = 0;
const MAX_NODES = 100_000;
const MAX_TERM_DEPTH = 256;

export const SEMANTIC_KERNEL_REQUIRED_RULES0 = Object.freeze([
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

export const SEMANTIC_KERNEL_SUPPORTED_RULES0 = Object.freeze(['Eq']);
export const SEMANTIC_EQ_OPERATIONS0 = Object.freeze(['refl', 'symm', 'trans', 'cong']);

export function makeSemanticVar0(name, sort = 'Term') {
  requireText0(name, 'makeSemanticVar0 name');
  requireText0(sort, 'makeSemanticVar0 sort');
  return Object.freeze({ kind: 'SemanticVar0', name, sort });
}

export function makeSemanticConst0(name, sort = 'Term') {
  requireText0(name, 'makeSemanticConst0 name');
  requireText0(sort, 'makeSemanticConst0 sort');
  return Object.freeze({ kind: 'SemanticConst0', name, sort });
}

export function makeSemanticApp0(symbol, args, sort = 'Term') {
  requireText0(symbol, 'makeSemanticApp0 symbol');
  requireText0(sort, 'makeSemanticApp0 sort');
  if (!Array.isArray(args)) throw new TypeError('makeSemanticApp0 args must be an array');
  return Object.freeze({ kind: 'SemanticApp0', symbol, args: Object.freeze([...args]), sort });
}

export function makeSemanticEqJudgment0(left, right) {
  return Object.freeze({ kind: 'SemanticEqJudgment0', left, right });
}

export function makeSemanticProofNode0({
  id,
  RuleName = 'Eq',
  Mode = 'Full',
  Premises = [],
  Conclusion,
  Payload = {},
} = {}) {
  requireText0(id, 'makeSemanticProofNode0 id');
  requireText0(RuleName, 'makeSemanticProofNode0 RuleName');
  if (!Array.isArray(Premises)) throw new TypeError('makeSemanticProofNode0 Premises must be an array');
  if (!plain0(Payload)) throw new TypeError('makeSemanticProofNode0 Payload must be an object');
  return Object.freeze({
    kind: 'SemanticProofNode0',
    version: VERSION,
    id,
    RuleName,
    Mode,
    Premises: Object.freeze([...Premises]),
    Conclusion,
    Payload: Object.freeze({ ...Payload }),
  });
}

export function makeSemanticProofDAG0(nodes = []) {
  if (!Array.isArray(nodes)) throw new TypeError('makeSemanticProofDAG0 nodes must be an array');
  return Object.freeze({ kind: 'SemanticProofDAG0', version: VERSION, nodes: Object.freeze([...nodes]) });
}

/**
 * Release blocker tied to the handlers implemented in this module. Callers
 * cannot override the supported-rule set with assertion-shaped metadata.
 */
export function CheckSemanticKernelReadiness0() {
  const checker = 'CheckSemanticKernelReadiness0';
  const missingRules = SEMANTIC_KERNEL_REQUIRED_RULES0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES0.includes(rule),
  );
  const nf = {
    kind: 'SemanticKernelReadiness0NF',
    checker,
    version: VERSION,
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES0],
    missingRules,
    semanticRuleCoverageComplete: missingRules.length === 0,
    failClosedUnsupportedRules: true,
  };
  const ledger = [entry0('semanticRuleCoverage', missingRules.length === 0, nf)];

  if (missingRules.length !== 0) {
    return reject0(
      checker,
      `${checker}.coverage`,
      ['missingRules'],
      'semantic kernel is not ready for final-theorem use',
      { missingRules },
      ledger,
    );
  }
  return accept0(checker, nf, ledger);
}

/**
 * Fail-closed semantic checker for the first PCC-K rule family. Acceptance
 * means each conclusion follows from earlier conclusions by an implemented Eq
 * operation. It does not assert soundness of the remaining primitive rules.
 */
export function CheckSemanticKernelProof0(input) {
  const checker = 'CheckSemanticKernelProof0';
  const ledger = [];
  const dag = normalizeDAG0(input);
  ledger.push(entry0('input', dag.ok, dag.nf ?? dag.witness));

  if (!dag.ok) return rejectFrom0(checker, `${checker}.input`, dag, ledger);
  if (dag.nodes.length > MAX_NODES) {
    return reject0(checker, `${checker}.bounds`, ['nodes'], 'semantic proof DAG exceeds maxNodes', {
      maxNodes: MAX_NODES,
      actual: dag.nodes.length,
    }, ledger);
  }

  const accepted = new Map();
  const ids = [];

  for (let index = 0; index < dag.nodes.length; index += 1) {
    const path = ['nodes', index];
    const phase = String(index).padStart(4, '0');
    const shape = validateNode0(dag.nodes[index], path);
    ledger.push(entry0(`node.${phase}.shape`, shape.ok, shape.nf ?? shape.witness));
    if (!shape.ok) return rejectFrom0(checker, `${checker}.node.${phase}.shape`, shape, ledger);

    const node = shape.node;
    if (accepted.has(node.id)) {
      return reject0(checker, `${checker}.node.${phase}.id`, [...path, 'id'],
        'semantic proof node ids must be unique', { id: node.id }, ledger);
    }

    const premises = [];
    for (let p = 0; p < node.Premises.length; p += 1) {
      const premiseId = node.Premises[p];
      const premise = accepted.get(premiseId);
      if (premise === undefined) {
        return reject0(
          checker,
          `${checker}.node.${phase}.premise`,
          [...path, 'Premises', p],
          'semantic proof premise must reference an earlier accepted node',
          { nodeId: node.id, premiseId },
          ledger,
        );
      }
      premises.push(premise);
    }

    const semantic = checkEq0(node, premises, path);
    ledger.push(entry0(`node.${phase}.semantic`, semantic.ok, semantic.nf ?? semantic.witness));
    if (!semantic.ok) return rejectFrom0(checker, `${checker}.node.${phase}.semantic`, semantic, ledger);

    accepted.set(node.id, Object.freeze({
      id: node.id,
      RuleName: node.RuleName,
      Conclusion: node.Conclusion,
      operation: semantic.nf.operation,
      digest: digest0(node),
    }));
    ids.push(node.id);
  }

  const missingRequiredRules = SEMANTIC_KERNEL_REQUIRED_RULES0.filter(
    (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES0.includes(rule),
  );
  return accept0(checker, {
    kind: 'SemanticKernelProof0NF',
    checker,
    version: VERSION,
    semanticRuleChecking: true,
    failClosedUnsupportedRules: true,
    requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES0],
    supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES0],
    missingRequiredRules,
    semanticRuleCoverageComplete: missingRequiredRules.length === 0,
    supportedEqOperations: [...SEMANTIC_EQ_OPERATIONS0],
    nodeCount: ids.length,
    acceptedNodeIds: ids,
    conclusionDigests: ids.map((id) => ({ id, digest: digest0(accepted.get(id).Conclusion) })),
  }, ledger);
}

function normalizeDAG0(input) {
  if (Array.isArray(input)) return { ok: true, nodes: input, nf: { form: 'array', nodeCount: input.length } };
  if (!plain0(input)) return bad0([], 'semantic proof input must be an array or object', { actual: typeof input });
  if (input.kind !== undefined && input.kind !== 'SemanticProofDAG0') {
    return bad0(['kind'], 'semantic proof DAG kind must be SemanticProofDAG0 when present', { actual: input.kind });
  }
  if (input.version !== undefined && input.version !== VERSION) {
    return bad0(['version'], `semantic proof DAG version must be ${VERSION} when present`, { actual: input.version });
  }
  const nodes = input.nodes ?? input.ProofDAG ?? input.proofDAG;
  if (!Array.isArray(nodes)) return bad0(['nodes'], 'semantic proof DAG must provide a nodes array', { actual: typeof nodes });
  return { ok: true, nodes, nf: { form: 'object', nodeCount: nodes.length } };
}

function validateNode0(node, path) {
  if (!plain0(node)) return bad0(path, 'semantic proof node must be an object', { actual: typeof node });
  if (node.kind !== 'SemanticProofNode0') {
    return bad0([...path, 'kind'], 'semantic proof node kind must be SemanticProofNode0', { actual: node.kind });
  }
  if (node.version !== undefined && node.version !== VERSION) {
    return bad0([...path, 'version'], `semantic proof node version must be ${VERSION}`, { actual: node.version });
  }
  if (!text0(node.id)) return bad0([...path, 'id'], 'semantic proof node id must be a non-empty string', { actual: node.id });
  if (!text0(node.RuleName)) return bad0([...path, 'RuleName'], 'semantic proof node must name a rule', { actual: node.RuleName });
  if (!SEMANTIC_KERNEL_SUPPORTED_RULES0.includes(node.RuleName)) {
    return bad0([...path, 'RuleName'], 'semantic kernel rejects unsupported rule', {
      ruleName: node.RuleName,
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES0],
    });
  }
  const Mode = node.Mode ?? 'Full';
  if (Mode !== 'Full') return bad0([...path, 'Mode'], 'phase-one semantic kernel accepts Full mode only', { actual: Mode });
  if (!Array.isArray(node.Premises)) {
    return bad0([...path, 'Premises'], 'semantic proof node Premises must be an array', { actual: typeof node.Premises });
  }
  const seen = new Set();
  for (let index = 0; index < node.Premises.length; index += 1) {
    const id = node.Premises[index];
    if (!text0(id)) return bad0([...path, 'Premises', index], 'semantic proof premise id must be a non-empty string', { actual: id });
    if (seen.has(id)) return bad0([...path, 'Premises', index], 'semantic proof node cannot repeat a premise id', { premiseId: id });
    seen.add(id);
  }
  if (!plain0(node.Payload)) return bad0([...path, 'Payload'], 'semantic proof node Payload must be an object', { actual: typeof node.Payload });
  const conclusion = validateEq0(node.Conclusion, [...path, 'Conclusion']);
  if (!conclusion.ok) return conclusion;
  return {
    ok: true,
    node: { ...node, Mode },
    nf: { id: node.id, RuleName: node.RuleName, Mode, premiseCount: node.Premises.length, conclusionSort: conclusion.sort },
  };
}

function validateEq0(judgment, path) {
  if (!plain0(judgment)) return bad0(path, 'semantic equality conclusion must be an object', { actual: typeof judgment });
  if (judgment.kind !== 'SemanticEqJudgment0') {
    return bad0([...path, 'kind'], 'semantic equality conclusion kind must be SemanticEqJudgment0', { actual: judgment.kind });
  }
  const left = validateTerm0(judgment.left, [...path, 'left'], 0);
  if (!left.ok) return left;
  const right = validateTerm0(judgment.right, [...path, 'right'], 0);
  if (!right.ok) return right;
  if (left.sort !== right.sort) {
    return bad0(path, 'semantic equality terms must have the same sort', { leftSort: left.sort, rightSort: right.sort });
  }
  return { ok: true, sort: left.sort, nf: { sort: left.sort } };
}

function validateTerm0(term, path, depth) {
  if (depth > MAX_TERM_DEPTH) return bad0(path, 'semantic term exceeds maxTermDepth', { maxTermDepth: MAX_TERM_DEPTH });
  if (!plain0(term)) return bad0(path, 'semantic term must be an object', { actual: typeof term });

  if (term.kind === 'SemanticVar0' || term.kind === 'SemanticConst0') {
    if (!text0(term.name)) return bad0([...path, 'name'], 'semantic variable/constant name must be non-empty', { actual: term.name });
    if (!text0(term.sort)) return bad0([...path, 'sort'], 'semantic variable/constant sort must be non-empty', { actual: term.sort });
    return { ok: true, sort: term.sort, nf: { kind: term.kind, sort: term.sort } };
  }

  if (term.kind === 'SemanticApp0') {
    if (!text0(term.symbol)) return bad0([...path, 'symbol'], 'semantic application symbol must be non-empty', { actual: term.symbol });
    if (!text0(term.sort)) return bad0([...path, 'sort'], 'semantic application result sort must be non-empty', { actual: term.sort });
    if (!Array.isArray(term.args)) return bad0([...path, 'args'], 'semantic application args must be an array', { actual: typeof term.args });
    for (let index = 0; index < term.args.length; index += 1) {
      const arg = validateTerm0(term.args[index], [...path, 'args', index], depth + 1);
      if (!arg.ok) return arg;
    }
    return { ok: true, sort: term.sort, nf: { kind: term.kind, sort: term.sort, arity: term.args.length } };
  }

  return bad0([...path, 'kind'], 'unsupported semantic term kind', {
    actual: term.kind,
    supportedKinds: ['SemanticVar0', 'SemanticConst0', 'SemanticApp0'],
  });
}

function checkEq0(node, premises, path) {
  const op = node.Payload.op;
  if (!SEMANTIC_EQ_OPERATIONS0.includes(op)) {
    return bad0([...path, 'Payload', 'op'], 'Eq rule operation is unsupported', {
      actual: op,
      supportedOperations: [...SEMANTIC_EQ_OPERATIONS0],
    });
  }
  const c = node.Conclusion;

  if (op === 'refl') {
    const count = count0(node, premises, 0, path);
    if (!count.ok) return count;
    if (!same0(c.left, c.right)) {
      return bad0([...path, 'Conclusion'], 'Eq.refl conclusion must have identical left and right terms', { left: c.left, right: c.right });
    }
    return goodRule0(op, 0);
  }

  if (op === 'symm') {
    const count = count0(node, premises, 1, path);
    if (!count.ok) return count;
    const p = premises[0].Conclusion;
    if (!same0(c.left, p.right) || !same0(c.right, p.left)) {
      return bad0([...path, 'Conclusion'], 'Eq.symm conclusion must reverse its premise equality', { premise: p, conclusion: c });
    }
    return goodRule0(op, 1);
  }

  if (op === 'trans') {
    const count = count0(node, premises, 2, path);
    if (!count.ok) return count;
    const a = premises[0].Conclusion;
    const b = premises[1].Conclusion;
    if (!same0(a.right, b.left)) {
      return bad0([...path, 'Premises'], 'Eq.trans premise middle terms must be identical', { firstRight: a.right, secondLeft: b.left });
    }
    if (!same0(c.left, a.left) || !same0(c.right, b.right)) {
      return bad0([...path, 'Conclusion'], 'Eq.trans conclusion must join the outer premise terms', { first: a, second: b, conclusion: c });
    }
    return goodRule0(op, 2);
  }

  if (c.left.kind !== 'SemanticApp0' || c.right.kind !== 'SemanticApp0') {
    return bad0([...path, 'Conclusion'], 'Eq.cong conclusion must compare two applications', {
      leftKind: c.left.kind,
      rightKind: c.right.kind,
    });
  }
  if (c.left.symbol !== c.right.symbol || c.left.sort !== c.right.sort || c.left.args.length !== c.right.args.length) {
    return bad0([...path, 'Conclusion'], 'Eq.cong applications must have the same symbol, result sort, and arity', {
      left: c.left,
      right: c.right,
    });
  }
  const count = count0(node, premises, c.left.args.length, path);
  if (!count.ok) return count;
  for (let index = 0; index < c.left.args.length; index += 1) {
    const p = premises[index].Conclusion;
    if (!same0(p.left, c.left.args[index]) || !same0(p.right, c.right.args[index])) {
      return bad0([...path, 'Premises', index], 'Eq.cong premise must prove the corresponding argument equality', {
        premise: p,
        leftArg: c.left.args[index],
        rightArg: c.right.args[index],
      });
    }
  }
  return { ok: true, nf: { kind: 'SemanticEqRule0NF', operation: op, premiseCount: premises.length, symbol: c.left.symbol, arity: c.left.args.length } };
}

function count0(node, premises, expected, path) {
  if (premises.length !== expected) {
    return bad0([...path, 'Premises'], `Eq.${node.Payload.op} requires exactly ${expected} premise(s)`, {
      expected,
      actual: premises.length,
    });
  }
  return { ok: true, nf: { expected } };
}

function goodRule0(operation, premiseCount) {
  return { ok: true, nf: { kind: 'SemanticEqRule0NF', operation, premiseCount } };
}

function bad0(path, reason, details = {}) {
  return { ok: false, path, witness: { reason, ...details } };
}

function rejectFrom0(checker, coord, result, ledger) {
  return reject0(checker, coord, result.path, result.witness.reason, omitReason0(result.witness), ledger);
}

function reject0(checker, coord, path, reason, details, ledger) {
  const witness = { reason, ...details };
  const nf = { kind: `${checker}RejectNF`, checker, version: VERSION, coord, path, witness, ledger };
  const digest = digest0(nf);
  return {
    tag: 'reject', kind: 'reject', checker, version: VERSION,
    Coord: coord, Path: path, Witness: witness, Digest: digest, Ledger: ledger,
    coord, path, witness, digest, ledger,
  };
}

function accept0(checker, nf, ledger) {
  const digest = digest0(nf);
  return {
    tag: 'accept', kind: 'accept', checker, version: VERSION,
    NF: nf, Digest: digest, Ledger: ledger,
    nf, digest, ledger,
  };
}

function entry0(phase, ok, material) {
  return { phase, status: ok ? 'pass' : 'fail', digest: digest0(material ?? null) };
}

function digest0(value) {
  return { alg: 'SHA256', hex: createHash('sha256').update(stable0(value)).digest('hex') };
}

function stable0(value) {
  return JSON.stringify(canon0(value, new Set()));
}

function canon0(value, seen) {
  if (value === null || typeof value === 'boolean' || typeof value === 'string') return value;
  if (typeof value === 'number') {
    if (!Number.isFinite(value)) throw new TypeError('canonical semantic-kernel JSON rejects non-finite numbers');
    return Object.is(value, -0) ? 0 : value;
  }
  if (Array.isArray(value)) {
    if (seen.has(value)) throw new TypeError('canonical semantic-kernel JSON rejects cycles');
    seen.add(value);
    const out = value.map((entry) => canon0(entry, seen));
    seen.delete(value);
    return out;
  }
  if (plain0(value)) {
    if (seen.has(value)) throw new TypeError('canonical semantic-kernel JSON rejects cycles');
    seen.add(value);
    const out = {};
    for (const key of Object.keys(value).sort()) {
      if (value[key] === undefined) throw new TypeError(`canonical semantic-kernel JSON rejects undefined at ${key}`);
      out[key] = canon0(value[key], seen);
    }
    seen.delete(value);
    return out;
  }
  throw new TypeError(`canonical semantic-kernel JSON rejects ${typeof value}`);
}

function same0(left, right) {
  return stable0(left) === stable0(right);
}

function omitReason0(witness) {
  const { reason: _reason, ...details } = witness;
  return details;
}

function plain0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

function text0(value) {
  return typeof value === 'string' && value.trim().length > 0;
}

function requireText0(value, label) {
  if (!text0(value)) throw new TypeError(`${label} must be a non-empty string`);
}
