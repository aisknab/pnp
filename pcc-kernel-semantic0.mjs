import { createHash } from 'node:crypto';

const VERSION = 0;
const MAX_NODES = 100_000;
const MAX_TERM_DEPTH = 256;
const MAX_FORMULA_DEPTH = 256;

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

export const SEMANTIC_EQ_OPERATIONS0 = Object.freeze([
  'refl',
  'symm',
  'trans',
  'cong',
]);

export const SEMANTIC_SUBST_OPERATIONS0 = Object.freeze(['instantiate']);

const RULE_HANDLERS0 = Object.freeze({
  Eq: checkEq0,
  Subst: checkSubstRule0,
});

export const SEMANTIC_KERNEL_SUPPORTED_RULES0 = Object.freeze(
  Object.keys(RULE_HANDLERS0),
);

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
  if (!Array.isArray(args)) {
    throw new TypeError('makeSemanticApp0 args must be an array');
  }
  return Object.freeze({
    kind: 'SemanticApp0',
    symbol,
    args: Object.freeze([...args]),
    sort,
  });
}

export function makeSemanticEqJudgment0(left, right) {
  return Object.freeze({ kind: 'SemanticEqJudgment0', left, right });
}

export function makeSemanticPred0(symbol, args = []) {
  requireText0(symbol, 'makeSemanticPred0 symbol');
  if (!Array.isArray(args)) {
    throw new TypeError('makeSemanticPred0 args must be an array');
  }
  return Object.freeze({
    kind: 'SemanticPred0',
    symbol,
    args: Object.freeze([...args]),
  });
}

export function makeSemanticEqFormula0(left, right) {
  return Object.freeze({ kind: 'SemanticEqFormula0', left, right });
}

export function makeSemanticAndFormula0(items = []) {
  if (!Array.isArray(items)) {
    throw new TypeError('makeSemanticAndFormula0 items must be an array');
  }
  return Object.freeze({
    kind: 'SemanticAndFormula0',
    items: Object.freeze([...items]),
  });
}

export function makeSemanticImpliesFormula0(antecedent, consequent) {
  return Object.freeze({
    kind: 'SemanticImpliesFormula0',
    antecedent,
    consequent,
  });
}

export function makeSemanticForallFinite0(variable, domain, body) {
  if (!Array.isArray(domain)) {
    throw new TypeError('makeSemanticForallFinite0 domain must be an array');
  }
  return Object.freeze({
    kind: 'SemanticForallFinite0',
    variable,
    domain: Object.freeze([...domain]),
    body,
  });
}

export function makeSemanticFormulaJudgment0(formula) {
  return Object.freeze({ kind: 'SemanticFormulaJudgment0', formula });
}

export function makeSemanticSubstitution0({
  source,
  variable,
  replacement,
  result,
} = {}) {
  return Object.freeze({
    kind: 'SemanticSubstitution0',
    version: VERSION,
    source,
    variable,
    replacement,
    result,
  });
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
  if (!Array.isArray(Premises)) {
    throw new TypeError('makeSemanticProofNode0 Premises must be an array');
  }
  if (!plain0(Payload)) {
    throw new TypeError('makeSemanticProofNode0 Payload must be an object');
  }
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
  if (!Array.isArray(nodes)) {
    throw new TypeError('makeSemanticProofDAG0 nodes must be an array');
  }
  return Object.freeze({
    kind: 'SemanticProofDAG0',
    version: VERSION,
    nodes: Object.freeze([...nodes]),
  });
}

/**
 * Capture-avoiding, sort-preserving substitution on semantic terms.
 */
export function substituteSemanticTerm0(term, variable, replacement) {
  const checked = validateSubstitutionInputs0(variable, replacement, ['substitution']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  const termCheck = validateTerm0(term, ['term'], 0);
  if (!termCheck.ok) throw new TypeError(termCheck.witness.reason);
  return substituteTerm0(term, variable, replacement);
}

/**
 * Capture-avoiding substitution on formulas. Bound variables are renamed
 * deterministically when a replacement term would otherwise become captured.
 */
export function substituteSemanticFormula0(formula, variable, replacement) {
  const checked = validateSubstitutionInputs0(variable, replacement, ['substitution']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  const formulaCheck = validateFormula0(formula, ['formula'], 0);
  if (!formulaCheck.ok) throw new TypeError(formulaCheck.witness.reason);
  return substituteFormulaDetailed0(formula, variable, replacement).value;
}

export function substituteSemanticJudgment0(judgment, variable, replacement) {
  const checked = validateSubstitutionInputs0(variable, replacement, ['substitution']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  const judgmentCheck = validateJudgment0(judgment, ['judgment']);
  if (!judgmentCheck.ok) throw new TypeError(judgmentCheck.witness.reason);
  return substituteJudgmentDetailed0(judgment, variable, replacement).value;
}

/**
 * Standalone checker for a substitution certificate. This validates the exact
 * syntactic transformation; it does not assert that the source judgment has
 * been proved. The Subst proof rule applies this transformation only to an
 * earlier accepted proof node.
 */
export function CheckSemanticSubstitution0(input) {
  const checker = 'CheckSemanticSubstitution0';
  const ledger = [];
  const checked = validateSubstitutionRecord0(input, []);
  ledger.push(entry0('substitution', checked.ok, checked.nf ?? checked.witness));

  if (!checked.ok) {
    return rejectFrom0(checker, `${checker}.substitution`, checked, ledger);
  }

  return accept0(checker, {
    kind: 'SemanticSubstitution0NF',
    checker,
    version: VERSION,
    sourceKind: checked.source.kind,
    resultKind: checked.result.kind,
    variable: checked.variable,
    replacementSort: checked.replacement.sort,
    captureAvoiding: true,
    alphaRenameCount: checked.alphaRenamings.length,
    alphaRenamings: checked.alphaRenamings,
    resultDigest: digest0(checked.result),
  }, ledger);
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
 * Fail-closed semantic checker. Acceptance means every node follows from
 * earlier accepted nodes by a rule handler implemented in this module. It does
 * not assert soundness of primitive rules that remain absent from RULE_HANDLERS0.
 */
export function CheckSemanticKernelProof0(input) {
  const checker = 'CheckSemanticKernelProof0';
  const ledger = [];
  const dag = normalizeDAG0(input);
  ledger.push(entry0('input', dag.ok, dag.nf ?? dag.witness));

  if (!dag.ok) return rejectFrom0(checker, `${checker}.input`, dag, ledger);
  if (dag.nodes.length > MAX_NODES) {
    return reject0(
      checker,
      `${checker}.bounds`,
      ['nodes'],
      'semantic proof DAG exceeds maxNodes',
      { maxNodes: MAX_NODES, actual: dag.nodes.length },
      ledger,
    );
  }

  const accepted = new Map();
  const ids = [];

  for (let index = 0; index < dag.nodes.length; index += 1) {
    const path = ['nodes', index];
    const phase = String(index).padStart(4, '0');
    const shape = validateNode0(dag.nodes[index], path);
    ledger.push(entry0(`node.${phase}.shape`, shape.ok, shape.nf ?? shape.witness));
    if (!shape.ok) {
      return rejectFrom0(checker, `${checker}.node.${phase}.shape`, shape, ledger);
    }

    const node = shape.node;
    if (accepted.has(node.id)) {
      return reject0(
        checker,
        `${checker}.node.${phase}.id`,
        [...path, 'id'],
        'semantic proof node ids must be unique',
        { id: node.id },
        ledger,
      );
    }

    const premises = [];
    for (let premiseIndex = 0; premiseIndex < node.Premises.length; premiseIndex += 1) {
      const premiseId = node.Premises[premiseIndex];
      const premise = accepted.get(premiseId);
      if (premise === undefined) {
        return reject0(
          checker,
          `${checker}.node.${phase}.premise`,
          [...path, 'Premises', premiseIndex],
          'semantic proof premise must reference an earlier accepted node',
          { nodeId: node.id, premiseId },
          ledger,
        );
      }
      premises.push(premise);
    }

    const handler = RULE_HANDLERS0[node.RuleName];
    const semantic = handler(node, premises, path);
    ledger.push(entry0(`node.${phase}.semantic`, semantic.ok, semantic.nf ?? semantic.witness));
    if (!semantic.ok) {
      return rejectFrom0(checker, `${checker}.node.${phase}.semantic`, semantic, ledger);
    }

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
    supportedSubstOperations: [...SEMANTIC_SUBST_OPERATIONS0],
    nodeCount: ids.length,
    acceptedNodeIds: ids,
    conclusionDigests: ids.map((id) => ({
      id,
      digest: digest0(accepted.get(id).Conclusion),
    })),
  }, ledger);
}

function normalizeDAG0(input) {
  if (Array.isArray(input)) {
    return { ok: true, nodes: input, nf: { form: 'array', nodeCount: input.length } };
  }
  if (!plain0(input)) {
    return bad0([], 'semantic proof input must be an array or object', {
      actual: typeof input,
    });
  }
  if (input.kind !== undefined && input.kind !== 'SemanticProofDAG0') {
    return bad0(
      ['kind'],
      'semantic proof DAG kind must be SemanticProofDAG0 when present',
      { actual: input.kind },
    );
  }
  if (input.version !== undefined && input.version !== VERSION) {
    return bad0(
      ['version'],
      `semantic proof DAG version must be ${VERSION} when present`,
      { actual: input.version },
    );
  }
  const nodes = input.nodes ?? input.ProofDAG ?? input.proofDAG;
  if (!Array.isArray(nodes)) {
    return bad0(['nodes'], 'semantic proof DAG must provide a nodes array', {
      actual: typeof nodes,
    });
  }
  return { ok: true, nodes, nf: { form: 'object', nodeCount: nodes.length } };
}

function validateNode0(node, path) {
  if (!plain0(node)) {
    return bad0(path, 'semantic proof node must be an object', {
      actual: typeof node,
    });
  }
  if (node.kind !== 'SemanticProofNode0') {
    return bad0(
      [...path, 'kind'],
      'semantic proof node kind must be SemanticProofNode0',
      { actual: node.kind },
    );
  }
  if (node.version !== undefined && node.version !== VERSION) {
    return bad0(
      [...path, 'version'],
      `semantic proof node version must be ${VERSION}`,
      { actual: node.version },
    );
  }
  if (!text0(node.id)) {
    return bad0([...path, 'id'], 'semantic proof node id must be a non-empty string', {
      actual: node.id,
    });
  }
  if (!text0(node.RuleName)) {
    return bad0([...path, 'RuleName'], 'semantic proof node must name a rule', {
      actual: node.RuleName,
    });
  }
  if (!Object.prototype.hasOwnProperty.call(RULE_HANDLERS0, node.RuleName)) {
    return bad0([...path, 'RuleName'], 'semantic kernel rejects unsupported rule', {
      ruleName: node.RuleName,
      supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES0],
    });
  }
  const Mode = node.Mode ?? 'Full';
  if (Mode !== 'Full') {
    return bad0(
      [...path, 'Mode'],
      'phase-two semantic kernel accepts Full mode only',
      { actual: Mode },
    );
  }
  if (!Array.isArray(node.Premises)) {
    return bad0(
      [...path, 'Premises'],
      'semantic proof node Premises must be an array',
      { actual: typeof node.Premises },
    );
  }
  const seen = new Set();
  for (let index = 0; index < node.Premises.length; index += 1) {
    const id = node.Premises[index];
    if (!text0(id)) {
      return bad0(
        [...path, 'Premises', index],
        'semantic proof premise id must be a non-empty string',
        { actual: id },
      );
    }
    if (seen.has(id)) {
      return bad0(
        [...path, 'Premises', index],
        'semantic proof node cannot repeat a premise id',
        { premiseId: id },
      );
    }
    seen.add(id);
  }
  if (!plain0(node.Payload)) {
    return bad0([...path, 'Payload'], 'semantic proof node Payload must be an object', {
      actual: typeof node.Payload,
    });
  }
  const conclusion = validateJudgment0(node.Conclusion, [...path, 'Conclusion']);
  if (!conclusion.ok) return conclusion;
  return {
    ok: true,
    node: { ...node, Mode },
    nf: {
      id: node.id,
      RuleName: node.RuleName,
      Mode,
      premiseCount: node.Premises.length,
      conclusionKind: node.Conclusion.kind,
      conclusionSort: conclusion.sort ?? null,
    },
  };
}

function validateJudgment0(judgment, path) {
  if (!plain0(judgment)) {
    return bad0(path, 'semantic judgment must be an object', {
      actual: typeof judgment,
    });
  }
  if (judgment.kind === 'SemanticEqJudgment0') {
    return validateEq0(judgment, path);
  }
  if (judgment.kind === 'SemanticFormulaJudgment0') {
    const formula = validateFormula0(judgment.formula, [...path, 'formula'], 0);
    if (!formula.ok) return formula;
    return {
      ok: true,
      nf: { kind: 'SemanticFormulaJudgment0NF', formulaKind: judgment.formula.kind },
    };
  }
  return bad0([...path, 'kind'], 'unsupported semantic judgment kind', {
    actual: judgment.kind,
    supportedKinds: ['SemanticEqJudgment0', 'SemanticFormulaJudgment0'],
  });
}

function validateEq0(judgment, path) {
  if (!plain0(judgment)) {
    return bad0(path, 'semantic equality conclusion must be an object', {
      actual: typeof judgment,
    });
  }
  if (judgment.kind !== 'SemanticEqJudgment0') {
    return bad0(
      [...path, 'kind'],
      'semantic equality conclusion kind must be SemanticEqJudgment0',
      { actual: judgment.kind },
    );
  }
  const left = validateTerm0(judgment.left, [...path, 'left'], 0);
  if (!left.ok) return left;
  const right = validateTerm0(judgment.right, [...path, 'right'], 0);
  if (!right.ok) return right;
  if (left.sort !== right.sort) {
    return bad0(path, 'semantic equality terms must have the same sort', {
      leftSort: left.sort,
      rightSort: right.sort,
    });
  }
  return { ok: true, sort: left.sort, nf: { sort: left.sort } };
}

function validateTerm0(term, path, depth) {
  if (depth > MAX_TERM_DEPTH) {
    return bad0(path, 'semantic term exceeds maxTermDepth', {
      maxTermDepth: MAX_TERM_DEPTH,
    });
  }
  if (!plain0(term)) {
    return bad0(path, 'semantic term must be an object', { actual: typeof term });
  }

  if (term.kind === 'SemanticVar0' || term.kind === 'SemanticConst0') {
    if (!text0(term.name)) {
      return bad0(
        [...path, 'name'],
        'semantic variable/constant name must be non-empty',
        { actual: term.name },
      );
    }
    if (!text0(term.sort)) {
      return bad0(
        [...path, 'sort'],
        'semantic variable/constant sort must be non-empty',
        { actual: term.sort },
      );
    }
    return { ok: true, sort: term.sort, nf: { kind: term.kind, sort: term.sort } };
  }

  if (term.kind === 'SemanticApp0') {
    if (!text0(term.symbol)) {
      return bad0(
        [...path, 'symbol'],
        'semantic application symbol must be non-empty',
        { actual: term.symbol },
      );
    }
    if (!text0(term.sort)) {
      return bad0(
        [...path, 'sort'],
        'semantic application result sort must be non-empty',
        { actual: term.sort },
      );
    }
    if (!Array.isArray(term.args)) {
      return bad0(
        [...path, 'args'],
        'semantic application args must be an array',
        { actual: typeof term.args },
      );
    }
    for (let index = 0; index < term.args.length; index += 1) {
      const arg = validateTerm0(term.args[index], [...path, 'args', index], depth + 1);
      if (!arg.ok) return arg;
    }
    return {
      ok: true,
      sort: term.sort,
      nf: { kind: term.kind, sort: term.sort, arity: term.args.length },
    };
  }

  return bad0([...path, 'kind'], 'unsupported semantic term kind', {
    actual: term.kind,
    supportedKinds: ['SemanticVar0', 'SemanticConst0', 'SemanticApp0'],
  });
}

function validateFormula0(formula, path, depth) {
  if (depth > MAX_FORMULA_DEPTH) {
    return bad0(path, 'semantic formula exceeds maxFormulaDepth', {
      maxFormulaDepth: MAX_FORMULA_DEPTH,
    });
  }
  if (!plain0(formula)) {
    return bad0(path, 'semantic formula must be an object', {
      actual: typeof formula,
    });
  }

  if (formula.kind === 'SemanticPred0') {
    if (!text0(formula.symbol)) {
      return bad0([...path, 'symbol'], 'semantic predicate symbol must be non-empty', {
        actual: formula.symbol,
      });
    }
    if (!Array.isArray(formula.args)) {
      return bad0([...path, 'args'], 'semantic predicate args must be an array', {
        actual: typeof formula.args,
      });
    }
    for (let index = 0; index < formula.args.length; index += 1) {
      const arg = validateTerm0(formula.args[index], [...path, 'args', index], 0);
      if (!arg.ok) return arg;
    }
    return { ok: true, nf: { kind: formula.kind, arity: formula.args.length } };
  }

  if (formula.kind === 'SemanticEqFormula0') {
    const left = validateTerm0(formula.left, [...path, 'left'], 0);
    if (!left.ok) return left;
    const right = validateTerm0(formula.right, [...path, 'right'], 0);
    if (!right.ok) return right;
    if (left.sort !== right.sort) {
      return bad0(path, 'semantic equality formula terms must have the same sort', {
        leftSort: left.sort,
        rightSort: right.sort,
      });
    }
    return { ok: true, nf: { kind: formula.kind, sort: left.sort } };
  }

  if (formula.kind === 'SemanticAndFormula0') {
    if (!Array.isArray(formula.items)) {
      return bad0([...path, 'items'], 'semantic conjunction items must be an array', {
        actual: typeof formula.items,
      });
    }
    for (let index = 0; index < formula.items.length; index += 1) {
      const item = validateFormula0(formula.items[index], [...path, 'items', index], depth + 1);
      if (!item.ok) return item;
    }
    return { ok: true, nf: { kind: formula.kind, itemCount: formula.items.length } };
  }

  if (formula.kind === 'SemanticImpliesFormula0') {
    const antecedent = validateFormula0(
      formula.antecedent,
      [...path, 'antecedent'],
      depth + 1,
    );
    if (!antecedent.ok) return antecedent;
    const consequent = validateFormula0(
      formula.consequent,
      [...path, 'consequent'],
      depth + 1,
    );
    if (!consequent.ok) return consequent;
    return { ok: true, nf: { kind: formula.kind } };
  }

  if (formula.kind === 'SemanticForallFinite0') {
    const variable = validateVariable0(formula.variable, [...path, 'variable']);
    if (!variable.ok) return variable;
    if (!Array.isArray(formula.domain)) {
      return bad0([...path, 'domain'], 'finite quantifier domain must be an array', {
        actual: typeof formula.domain,
      });
    }
    for (let index = 0; index < formula.domain.length; index += 1) {
      const entry = validateTerm0(formula.domain[index], [...path, 'domain', index], 0);
      if (!entry.ok) return entry;
      if (entry.sort !== formula.variable.sort) {
        return bad0(
          [...path, 'domain', index],
          'finite quantifier domain entry must match the bound-variable sort',
          {
            variableSort: formula.variable.sort,
            entrySort: entry.sort,
          },
        );
      }
    }
    const body = validateFormula0(formula.body, [...path, 'body'], depth + 1);
    if (!body.ok) return body;
    return {
      ok: true,
      nf: {
        kind: formula.kind,
        variable: formula.variable,
        domainSize: formula.domain.length,
      },
    };
  }

  return bad0([...path, 'kind'], 'unsupported semantic formula kind', {
    actual: formula.kind,
    supportedKinds: [
      'SemanticPred0',
      'SemanticEqFormula0',
      'SemanticAndFormula0',
      'SemanticImpliesFormula0',
      'SemanticForallFinite0',
    ],
  });
}

function checkEq0(node, premises, path) {
  if (node.Conclusion.kind !== 'SemanticEqJudgment0') {
    return bad0(
      [...path, 'Conclusion', 'kind'],
      'Eq rule requires a SemanticEqJudgment0 conclusion',
      { actual: node.Conclusion.kind },
    );
  }
  for (let index = 0; index < premises.length; index += 1) {
    if (premises[index].Conclusion.kind !== 'SemanticEqJudgment0') {
      return bad0(
        [...path, 'Premises', index],
        'Eq rule premises must be semantic equality judgments',
        { actual: premises[index].Conclusion.kind },
      );
    }
  }

  const op = node.Payload.op;
  if (!SEMANTIC_EQ_OPERATIONS0.includes(op)) {
    return bad0([...path, 'Payload', 'op'], 'Eq rule operation is unsupported', {
      actual: op,
      supportedOperations: [...SEMANTIC_EQ_OPERATIONS0],
    });
  }
  const conclusion = node.Conclusion;

  if (op === 'refl') {
    const count = premiseCount0('Eq', op, premises, 0, path);
    if (!count.ok) return count;
    if (!same0(conclusion.left, conclusion.right)) {
      return bad0(
        [...path, 'Conclusion'],
        'Eq.refl conclusion must have identical left and right terms',
        { left: conclusion.left, right: conclusion.right },
      );
    }
    return goodRule0('Eq', op, 0);
  }

  if (op === 'symm') {
    const count = premiseCount0('Eq', op, premises, 1, path);
    if (!count.ok) return count;
    const premise = premises[0].Conclusion;
    if (!same0(conclusion.left, premise.right) || !same0(conclusion.right, premise.left)) {
      return bad0(
        [...path, 'Conclusion'],
        'Eq.symm conclusion must reverse its premise equality',
        { premise, conclusion },
      );
    }
    return goodRule0('Eq', op, 1);
  }

  if (op === 'trans') {
    const count = premiseCount0('Eq', op, premises, 2, path);
    if (!count.ok) return count;
    const first = premises[0].Conclusion;
    const second = premises[1].Conclusion;
    if (!same0(first.right, second.left)) {
      return bad0(
        [...path, 'Premises'],
        'Eq.trans premise middle terms must be identical',
        { firstRight: first.right, secondLeft: second.left },
      );
    }
    if (!same0(conclusion.left, first.left) || !same0(conclusion.right, second.right)) {
      return bad0(
        [...path, 'Conclusion'],
        'Eq.trans conclusion must join the outer premise terms',
        { first, second, conclusion },
      );
    }
    return goodRule0('Eq', op, 2);
  }

  if (conclusion.left.kind !== 'SemanticApp0' || conclusion.right.kind !== 'SemanticApp0') {
    return bad0(
      [...path, 'Conclusion'],
      'Eq.cong conclusion must compare two applications',
      {
        leftKind: conclusion.left.kind,
        rightKind: conclusion.right.kind,
      },
    );
  }
  if (
    conclusion.left.symbol !== conclusion.right.symbol
    || conclusion.left.sort !== conclusion.right.sort
    || conclusion.left.args.length !== conclusion.right.args.length
  ) {
    return bad0(
      [...path, 'Conclusion'],
      'Eq.cong applications must have the same symbol, result sort, and arity',
      { left: conclusion.left, right: conclusion.right },
    );
  }
  const count = premiseCount0(
    'Eq',
    op,
    premises,
    conclusion.left.args.length,
    path,
  );
  if (!count.ok) return count;
  for (let index = 0; index < conclusion.left.args.length; index += 1) {
    const premise = premises[index].Conclusion;
    if (
      !same0(premise.left, conclusion.left.args[index])
      || !same0(premise.right, conclusion.right.args[index])
    ) {
      return bad0(
        [...path, 'Premises', index],
        'Eq.cong premise must prove the corresponding argument equality',
        {
          premise,
          leftArg: conclusion.left.args[index],
          rightArg: conclusion.right.args[index],
        },
      );
    }
  }
  return {
    ok: true,
    nf: {
      kind: 'SemanticEqRule0NF',
      ruleName: 'Eq',
      operation: op,
      premiseCount: premises.length,
      symbol: conclusion.left.symbol,
      arity: conclusion.left.args.length,
    },
  };
}

function checkSubstRule0(node, premises, path) {
  const op = node.Payload.op;
  if (!SEMANTIC_SUBST_OPERATIONS0.includes(op)) {
    return bad0(
      [...path, 'Payload', 'op'],
      'Subst rule operation is unsupported',
      { actual: op, supportedOperations: [...SEMANTIC_SUBST_OPERATIONS0] },
    );
  }
  const count = premiseCount0('Subst', op, premises, 1, path);
  if (!count.ok) return count;

  const checked = validateSubstitutionRecord0({
    kind: 'SemanticSubstitution0',
    version: VERSION,
    source: premises[0].Conclusion,
    variable: node.Payload.variable,
    replacement: node.Payload.replacement,
    result: node.Conclusion,
  }, path);
  if (!checked.ok) return checked;

  return {
    ok: true,
    nf: {
      kind: 'SemanticSubstRule0NF',
      ruleName: 'Subst',
      operation: op,
      premiseCount: 1,
      sourceKind: checked.source.kind,
      resultKind: checked.result.kind,
      variable: checked.variable,
      replacementSort: checked.replacement.sort,
      captureAvoiding: true,
      alphaRenameCount: checked.alphaRenamings.length,
      alphaRenamings: checked.alphaRenamings,
    },
  };
}

function validateSubstitutionRecord0(input, path) {
  if (!plain0(input)) {
    return bad0(path, 'semantic substitution record must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== undefined && input.kind !== 'SemanticSubstitution0') {
    return bad0(
      [...path, 'kind'],
      'semantic substitution kind must be SemanticSubstitution0 when present',
      { actual: input.kind },
    );
  }
  if (input.version !== undefined && input.version !== VERSION) {
    return bad0(
      [...path, 'version'],
      `semantic substitution version must be ${VERSION} when present`,
      { actual: input.version },
    );
  }

  const source = validateJudgment0(input.source, [...path, 'source']);
  if (!source.ok) return source;
  const result = validateJudgment0(input.result, [...path, 'result']);
  if (!result.ok) return result;
  const inputs = validateSubstitutionInputs0(
    input.variable,
    input.replacement,
    path,
  );
  if (!inputs.ok) return inputs;

  const transformed = substituteJudgmentDetailed0(
    input.source,
    input.variable,
    input.replacement,
  );
  if (!same0(transformed.value, input.result)) {
    return bad0(
      [...path, 'result'],
      'semantic substitution result does not equal capture-avoiding substitution',
      {
        expected: transformed.value,
        actual: input.result,
        alphaRenamings: transformed.alphaRenamings,
      },
    );
  }

  return {
    ok: true,
    source: input.source,
    result: input.result,
    variable: input.variable,
    replacement: input.replacement,
    alphaRenamings: transformed.alphaRenamings,
    nf: {
      sourceKind: input.source.kind,
      resultKind: input.result.kind,
      variable: input.variable,
      replacementSort: input.replacement.sort,
      captureAvoiding: true,
      alphaRenameCount: transformed.alphaRenamings.length,
    },
  };
}

function validateSubstitutionInputs0(variable, replacement, path) {
  const variableCheck = validateVariable0(variable, [...path, 'variable']);
  if (!variableCheck.ok) return variableCheck;
  const replacementCheck = validateTerm0(replacement, [...path, 'replacement'], 0);
  if (!replacementCheck.ok) return replacementCheck;
  if (replacementCheck.sort !== variable.sort) {
    return bad0(
      [...path, 'replacement'],
      'semantic substitution replacement sort must match the variable sort',
      {
        variableSort: variable.sort,
        replacementSort: replacementCheck.sort,
      },
    );
  }
  return { ok: true, nf: { variable, replacementSort: replacementCheck.sort } };
}

function validateVariable0(variable, path) {
  const checked = validateTerm0(variable, path, 0);
  if (!checked.ok) return checked;
  if (variable.kind !== 'SemanticVar0') {
    return bad0(path, 'semantic substitution variable must be a SemanticVar0', {
      actual: variable.kind,
    });
  }
  return { ok: true, sort: variable.sort, nf: { variable } };
}

function substituteJudgmentDetailed0(judgment, variable, replacement) {
  if (judgment.kind === 'SemanticEqJudgment0') {
    return {
      value: makeSemanticEqJudgment0(
        substituteTerm0(judgment.left, variable, replacement),
        substituteTerm0(judgment.right, variable, replacement),
      ),
      alphaRenamings: [],
    };
  }
  if (judgment.kind === 'SemanticFormulaJudgment0') {
    const transformed = substituteFormulaDetailed0(
      judgment.formula,
      variable,
      replacement,
    );
    return {
      value: makeSemanticFormulaJudgment0(transformed.value),
      alphaRenamings: transformed.alphaRenamings,
    };
  }
  throw new TypeError(`unsupported semantic judgment kind ${String(judgment.kind)}`);
}

function substituteTerm0(term, variable, replacement) {
  if (term.kind === 'SemanticVar0') {
    return sameVariable0(term, variable) ? replacement : term;
  }
  if (term.kind === 'SemanticConst0') return term;
  if (term.kind === 'SemanticApp0') {
    return makeSemanticApp0(
      term.symbol,
      term.args.map((arg) => substituteTerm0(arg, variable, replacement)),
      term.sort,
    );
  }
  throw new TypeError(`unsupported semantic term kind ${String(term.kind)}`);
}

function substituteFormulaDetailed0(formula, variable, replacement) {
  const state = { alphaRenamings: [] };
  const value = substituteFormulaWithState0(formula, variable, replacement, state);
  return { value, alphaRenamings: state.alphaRenamings };
}

function substituteFormulaWithState0(formula, variable, replacement, state) {
  if (formula.kind === 'SemanticPred0') {
    return makeSemanticPred0(
      formula.symbol,
      formula.args.map((arg) => substituteTerm0(arg, variable, replacement)),
    );
  }
  if (formula.kind === 'SemanticEqFormula0') {
    return makeSemanticEqFormula0(
      substituteTerm0(formula.left, variable, replacement),
      substituteTerm0(formula.right, variable, replacement),
    );
  }
  if (formula.kind === 'SemanticAndFormula0') {
    return makeSemanticAndFormula0(
      formula.items.map((item) => (
        substituteFormulaWithState0(item, variable, replacement, state)
      )),
    );
  }
  if (formula.kind === 'SemanticImpliesFormula0') {
    return makeSemanticImpliesFormula0(
      substituteFormulaWithState0(
        formula.antecedent,
        variable,
        replacement,
        state,
      ),
      substituteFormulaWithState0(
        formula.consequent,
        variable,
        replacement,
        state,
      ),
    );
  }
  if (formula.kind === 'SemanticForallFinite0') {
    const substitutedDomain = formula.domain.map((entry) => (
      substituteTerm0(entry, variable, replacement)
    ));

    if (sameVariable0(formula.variable, variable)) {
      return makeSemanticForallFinite0(
        formula.variable,
        substitutedDomain,
        formula.body,
      );
    }

    let binder = formula.variable;
    let body = formula.body;
    const replacementFree = freeTermVariableKeys0(replacement);
    if (replacementFree.has(variableKey0(binder))) {
      const usedNames = collectAllVariableNames0(
        formula,
        replacement,
        variable,
      );
      const fresh = makeSemanticVar0(
        freshVariableName0(binder.name, usedNames),
        binder.sort,
      );
      body = renameBoundOccurrencesFormula0(body, binder, fresh);
      state.alphaRenamings.push(Object.freeze({ from: binder, to: fresh }));
      binder = fresh;
    }

    return makeSemanticForallFinite0(
      binder,
      substitutedDomain,
      substituteFormulaWithState0(body, variable, replacement, state),
    );
  }
  throw new TypeError(`unsupported semantic formula kind ${String(formula.kind)}`);
}

function renameBoundOccurrencesFormula0(formula, from, to) {
  if (formula.kind === 'SemanticPred0') {
    return makeSemanticPred0(
      formula.symbol,
      formula.args.map((arg) => renameVariableInTerm0(arg, from, to)),
    );
  }
  if (formula.kind === 'SemanticEqFormula0') {
    return makeSemanticEqFormula0(
      renameVariableInTerm0(formula.left, from, to),
      renameVariableInTerm0(formula.right, from, to),
    );
  }
  if (formula.kind === 'SemanticAndFormula0') {
    return makeSemanticAndFormula0(
      formula.items.map((item) => renameBoundOccurrencesFormula0(item, from, to)),
    );
  }
  if (formula.kind === 'SemanticImpliesFormula0') {
    return makeSemanticImpliesFormula0(
      renameBoundOccurrencesFormula0(formula.antecedent, from, to),
      renameBoundOccurrencesFormula0(formula.consequent, from, to),
    );
  }
  if (formula.kind === 'SemanticForallFinite0') {
    const domain = formula.domain.map((entry) => renameVariableInTerm0(entry, from, to));
    if (sameVariable0(formula.variable, from)) {
      return makeSemanticForallFinite0(formula.variable, domain, formula.body);
    }
    return makeSemanticForallFinite0(
      formula.variable,
      domain,
      renameBoundOccurrencesFormula0(formula.body, from, to),
    );
  }
  throw new TypeError(`unsupported semantic formula kind ${String(formula.kind)}`);
}

function renameVariableInTerm0(term, from, to) {
  if (term.kind === 'SemanticVar0') {
    return sameVariable0(term, from) ? to : term;
  }
  if (term.kind === 'SemanticConst0') return term;
  if (term.kind === 'SemanticApp0') {
    return makeSemanticApp0(
      term.symbol,
      term.args.map((arg) => renameVariableInTerm0(arg, from, to)),
      term.sort,
    );
  }
  throw new TypeError(`unsupported semantic term kind ${String(term.kind)}`);
}

function freeTermVariableKeys0(term, out = new Set()) {
  if (term.kind === 'SemanticVar0') {
    out.add(variableKey0(term));
    return out;
  }
  if (term.kind === 'SemanticConst0') return out;
  if (term.kind === 'SemanticApp0') {
    for (const arg of term.args) freeTermVariableKeys0(arg, out);
    return out;
  }
  throw new TypeError(`unsupported semantic term kind ${String(term.kind)}`);
}

function collectAllVariableNames0(formula, replacement, variable) {
  const names = new Set([variable.name]);
  collectFormulaVariableNames0(formula, names);
  collectTermVariableNames0(replacement, names);
  return names;
}

function collectFormulaVariableNames0(formula, out) {
  if (formula.kind === 'SemanticPred0') {
    for (const arg of formula.args) collectTermVariableNames0(arg, out);
    return out;
  }
  if (formula.kind === 'SemanticEqFormula0') {
    collectTermVariableNames0(formula.left, out);
    collectTermVariableNames0(formula.right, out);
    return out;
  }
  if (formula.kind === 'SemanticAndFormula0') {
    for (const item of formula.items) collectFormulaVariableNames0(item, out);
    return out;
  }
  if (formula.kind === 'SemanticImpliesFormula0') {
    collectFormulaVariableNames0(formula.antecedent, out);
    collectFormulaVariableNames0(formula.consequent, out);
    return out;
  }
  if (formula.kind === 'SemanticForallFinite0') {
    out.add(formula.variable.name);
    for (const entry of formula.domain) collectTermVariableNames0(entry, out);
    collectFormulaVariableNames0(formula.body, out);
    return out;
  }
  throw new TypeError(`unsupported semantic formula kind ${String(formula.kind)}`);
}

function collectTermVariableNames0(term, out) {
  if (term.kind === 'SemanticVar0') {
    out.add(term.name);
    return out;
  }
  if (term.kind === 'SemanticConst0') return out;
  if (term.kind === 'SemanticApp0') {
    for (const arg of term.args) collectTermVariableNames0(arg, out);
    return out;
  }
  throw new TypeError(`unsupported semantic term kind ${String(term.kind)}`);
}

function freshVariableName0(base, usedNames) {
  for (let index = 0; index < Number.MAX_SAFE_INTEGER; index += 1) {
    const candidate = `${base}$${index}`;
    if (!usedNames.has(candidate)) return candidate;
  }
  throw new RangeError('unable to allocate a fresh semantic variable name');
}

function sameVariable0(left, right) {
  return left.name === right.name && left.sort === right.sort;
}

function variableKey0(variable) {
  return `${variable.sort}\u0000${variable.name}`;
}

function premiseCount0(ruleName, operation, premises, expected, path) {
  if (premises.length !== expected) {
    return bad0(
      [...path, 'Premises'],
      `${ruleName}.${operation} requires exactly ${expected} premise(s)`,
      { expected, actual: premises.length },
    );
  }
  return { ok: true, nf: { expected } };
}

function goodRule0(ruleName, operation, premiseCount) {
  return {
    ok: true,
    nf: {
      kind: `Semantic${ruleName}Rule0NF`,
      ruleName,
      operation,
      premiseCount,
    },
  };
}

function bad0(path, reason, details = {}) {
  return { ok: false, path, witness: { reason, ...details } };
}

function rejectFrom0(checker, coord, result, ledger) {
  return reject0(
    checker,
    coord,
    result.path,
    result.witness.reason,
    omitReason0(result.witness),
    ledger,
  );
}

function reject0(checker, coord, path, reason, details, ledger) {
  const witness = { reason, ...details };
  const nf = {
    kind: `${checker}RejectNF`,
    checker,
    version: VERSION,
    coord,
    path,
    witness,
    ledger,
  };
  const digest = digest0(nf);
  return {
    tag: 'reject',
    kind: 'reject',
    checker,
    version: VERSION,
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

function accept0(checker, nf, ledger) {
  const digest = digest0(nf);
  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: VERSION,
    NF: nf,
    Digest: digest,
    Ledger: ledger,
    nf,
    digest,
    ledger,
  };
}

function entry0(phase, ok, material) {
  return {
    phase,
    status: ok ? 'pass' : 'fail',
    digest: digest0(material ?? null),
  };
}

function digest0(value) {
  return {
    alg: 'SHA256',
    hex: createHash('sha256').update(stable0(value)).digest('hex'),
  };
}

function stable0(value) {
  return JSON.stringify(canon0(value, new Set()));
}

function canon0(value, seen) {
  if (value === null || typeof value === 'boolean' || typeof value === 'string') {
    return value;
  }
  if (typeof value === 'number') {
    if (!Number.isFinite(value)) {
      throw new TypeError('canonical semantic-kernel JSON rejects non-finite numbers');
    }
    return Object.is(value, -0) ? 0 : value;
  }
  if (Array.isArray(value)) {
    if (seen.has(value)) {
      throw new TypeError('canonical semantic-kernel JSON rejects cycles');
    }
    seen.add(value);
    const out = value.map((entry) => canon0(entry, seen));
    seen.delete(value);
    return out;
  }
  if (plain0(value)) {
    if (seen.has(value)) {
      throw new TypeError('canonical semantic-kernel JSON rejects cycles');
    }
    seen.add(value);
    const out = {};
    for (const key of Object.keys(value).sort()) {
      if (value[key] === undefined) {
        throw new TypeError(
          `canonical semantic-kernel JSON rejects undefined at ${key}`,
        );
      }
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
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

function text0(value) {
  return typeof value === 'string' && value.trim().length > 0;
}

function requireText0(value, label) {
  if (!text0(value)) {
    throw new TypeError(`${label} must be a non-empty string`);
  }
}
