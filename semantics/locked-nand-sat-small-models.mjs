import {
  evaluateNANDWord0,
  flattenedTruthTable0,
  makeBoundarySource0,
  makeConstSource0,
  makeGateSource0,
  makeNANDWord0,
  sizeOfNANDWord0,
  validateNANDWord0,
} from './nand-direct-wire-reference.mjs';

import {
  enumerateNANDWords0,
} from './nand-small-models.mjs';

const COORDINATE0 = 'PNP-LOCKED-NAND-SAT-SMALL-MODELS-2026-06-27-01';
const EXPECTED_BLOCKERS0 = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];

export function enumerateCNFUniverse0({ maxVariables = 2 } = {}) {
  const formulas = [];
  for (let variableCount = 1; variableCount <= maxVariables; variableCount += 1) {
    const variables = Array.from({ length: variableCount }, (_, index) => `x${index}`);
    for (const variable of variables) {
      formulas.push({ id: `unit-${variable}`, variables, clauses: [[{ variable, negated: false }]], expectedSat: true });
      formulas.push({ id: `unit-not-${variable}`, variables, clauses: [[{ variable, negated: true }]], expectedSat: true });
      formulas.push({ id: `contradiction-${variable}`, variables, clauses: [[{ variable, negated: false }], [{ variable, negated: true }]], expectedSat: false });
    }
  }
  return formulas;
}

export function bruteForceCNFSAT0(formula) {
  const assignments = enumerateBooleanAssignments0(formula.variables);
  for (const assignment of assignments) {
    if (evaluateCNF0(formula, assignment) === 1) return { tag: 'accept', sat: true, witness: assignment };
  }
  return { tag: 'accept', sat: false, witness: null };
}

export function evaluateCNF0(formula, assignment) {
  if (!Array.isArray(formula.clauses) || formula.clauses.length === 0) return 1;
  for (const clause of formula.clauses) {
    let clauseValue = 0;
    for (const literal of clause) {
      const value = assignment[literal.variable];
      const litValue = literal.negated ? 1 - value : value;
      clauseValue = clauseValue || litValue;
    }
    if (clauseValue === 0) return 0;
  }
  return 1;
}

export function constructLockedNANDSATSeedWord0(formula) {
  const boundary = [...formula.variables, 'z'];
  const recognized = recognizeSeedFormula0(formula);
  if (recognized.tag === 'reject') return recognized;

  if (recognized.kind === 'contradiction') {
    return { tag: 'accept', word: makeNANDWord0({ boundary, gates: [], outputs: [makeConstSource0(0)] }), baselineMinimum: 0 };
  }

  const variableSource = makeBoundarySource0(recognized.variable);
  const zSource = makeBoundarySource0('z');
  if (recognized.negated) {
    return {
      tag: 'accept',
      word: makeNANDWord0({
        boundary,
        gates: [
          { id: 'not_lit', op: 'NAND', left: variableSource, right: variableSource },
          { id: 'z_nand_lit', op: 'NAND', left: zSource, right: makeGateSource0('not_lit') },
          { id: 'final', op: 'NAND', left: makeGateSource0('z_nand_lit'), right: makeGateSource0('z_nand_lit') },
        ],
        outputs: [makeGateSource0('final')],
      }),
      baselineMinimum: 0,
    };
  }

  return {
    tag: 'accept',
    word: makeNANDWord0({
      boundary,
      gates: [
        { id: 'z_nand_lit', op: 'NAND', left: zSource, right: variableSource },
        { id: 'final', op: 'NAND', left: makeGateSource0('z_nand_lit'), right: makeGateSource0('z_nand_lit') },
      ],
      outputs: [makeGateSource0('final')],
    }),
    baselineMinimum: 0,
  };
}

function recognizeSeedFormula0(formula) {
  if (!Array.isArray(formula.variables) || formula.variables.length === 0) return reject0('LockedNANDSAT.FormulaVariables', ['formula', 'variables'], 'formula variables must be non-empty');
  if (!Array.isArray(formula.clauses)) return reject0('LockedNANDSAT.FormulaClauses', ['formula', 'clauses'], 'formula clauses must be an array');

  if (formula.clauses.length === 1 && formula.clauses[0].length === 1) {
    const literal = formula.clauses[0][0];
    if (!formula.variables.includes(literal.variable)) return reject0('LockedNANDSAT.UnknownLiteralVariable', ['formula', 'clauses'], 'literal references unknown variable', { literal });
    return { tag: 'accept', kind: 'unit', variable: literal.variable, negated: literal.negated === true };
  }

  if (formula.clauses.length === 2 && formula.clauses.every((clause) => clause.length === 1)) {
    const [left] = formula.clauses[0];
    const [right] = formula.clauses[1];
    if (left.variable === right.variable && left.negated !== right.negated && formula.variables.includes(left.variable)) {
      return { tag: 'accept', kind: 'contradiction', variable: left.variable };
    }
  }

  return reject0('LockedNANDSAT.UnsupportedSeedFormula', ['formula', 'clauses'], 'seed locked-NAND SAT small-model audit currently supports only unit clauses and single-variable contradiction pairs', { formula });
}

export function expectedLockedOutputBits0(formula) {
  const boundary = [...formula.variables, 'z'];
  const assignments = enumerateBooleanAssignments0(boundary);
  return assignments.map((assignment) => assignment.z === 1 && evaluateCNF0(formula, assignment) === 1 ? 1 : 0);
}

export function exactMinimumForTruthBits0({ boundary, bits, maxGates }) {
  const words = enumerateNANDWords0({ boundary, maxGates });
  let minimum = Number.POSITIVE_INFINITY;
  let witness = null;
  for (const word of words) {
    const table = flattenedTruthTable0(word);
    if (table.tag === 'reject') return table;
    if (sameArray0(table.bits, bits)) {
      const size = sizeOfNANDWord0(word);
      if (size.tag === 'reject') return size;
      if (size.size < minimum) {
        minimum = size.size;
        witness = word;
      }
    }
  }
  if (minimum === Number.POSITIVE_INFINITY) return reject0('LockedNANDSAT.ExactMinimumNotFound', ['exactMinimum'], 'no NAND word inside the configured bound realizes the target truth table', { boundary, bits, maxGates });
  return { tag: 'accept', minimum, witness };
}

export function RunLockedNANDSATSmallModels0(config = {}) {
  try {
    const maxVariables = config.formulaUniverse?.maxVariables ?? config.maxVariables ?? 2;
    const maxExactSearchGates = config.thresholdModel?.maxExactSearchGates ?? config.maxExactSearchGates ?? 3;
    if (!Number.isInteger(maxVariables) || maxVariables < 1 || maxVariables > 2) return reject0('LockedNANDSAT.ConfigMaxVariables', ['formulaUniverse', 'maxVariables'], 'seed maxVariables must be 1 or 2', { maxVariables });
    if (!Number.isInteger(maxExactSearchGates) || maxExactSearchGates < 0 || maxExactSearchGates > 3) return reject0('LockedNANDSAT.ConfigMaxExactSearchGates', ['thresholdModel', 'maxExactSearchGates'], 'seed maxExactSearchGates must be between 0 and 3', { maxExactSearchGates });

    const formulas = enumerateCNFUniverse0({ maxVariables });
    const results = [];
    let satCount = 0;
    let unsatCount = 0;
    for (const formula of formulas) {
      const sat = bruteForceCNFSAT0(formula);
      if (sat.tag === 'reject') return sat;
      if (sat.sat !== formula.expectedSat) return reject0('LockedNANDSAT.ExpectedSATMismatch', ['formulas', formula.id], 'formula expectedSat metadata mismatch', { formula, actualSat: sat.sat });
      satCount += sat.sat ? 1 : 0;
      unsatCount += sat.sat ? 0 : 1;

      const construction = constructLockedNANDSATSeedWord0(formula);
      if (construction.tag === 'reject') return construction;
      const validation = validateNANDWord0(construction.word);
      if (validation.tag === 'reject') return reject0('LockedNANDSAT.ConstructedWordInvalid', ['formulas', formula.id], 'constructed locked NAND seed word failed validation', { validation, formula, word: construction.word });

      const expectedBits = expectedLockedOutputBits0(formula);
      const table = flattenedTruthTable0(construction.word);
      if (table.tag === 'reject') return table;
      if (!sameArray0(table.bits, expectedBits)) return reject0('LockedNANDSAT.TruthTableMismatch', ['formulas', formula.id], 'constructed locked NAND seed truth table mismatch', { formula, expectedBits, actualBits: table.bits });
      const nonzero = table.bits.some((bit) => bit === 1);
      if (nonzero !== sat.sat) return reject0('LockedNANDSAT.NonzeroIffSATFailed', ['formulas', formula.id], 'locked output nonzero predicate must agree with brute-force SAT', { formula, sat: sat.sat, bits: table.bits });

      const exact = exactMinimumForTruthBits0({ boundary: construction.word.boundary, bits: table.bits, maxGates: maxExactSearchGates });
      if (exact.tag === 'reject') return exact;
      const threshold = exact.minimum > construction.baselineMinimum;
      if (threshold !== sat.sat) return reject0('LockedNANDSAT.ThresholdMismatch', ['formulas', formula.id], 'small-model threshold predicate must agree with brute-force SAT', { formula, sat: sat.sat, minimum: exact.minimum, baselineMinimum: construction.baselineMinimum });
      if (!sat.sat && exact.minimum !== 0) return reject0('LockedNANDSAT.UnsatNotZeroMinimum', ['formulas', formula.id], 'unsatisfiable seed formulas must have zero final-output minimum', { formula, minimum: exact.minimum });
      if (sat.sat && exact.minimum <= 0) return reject0('LockedNANDSAT.SatNotPositiveMinimum', ['formulas', formula.id], 'satisfiable seed formulas must have positive final-output minimum', { formula, minimum: exact.minimum });

      results.push({ id: formula.id, variableCount: formula.variables.length, sat: sat.sat, minimum: exact.minimum, baselineMinimum: construction.baselineMinimum, threshold });
    }

    return {
      tag: 'accept',
      kind: 'accept',
      checker: 'RunLockedNANDSATSmallModels0',
      version: 0,
      coordinate: COORDINATE0,
      satSmallModelsReady: true,
      fullLockedNANDThresholdCoverageProved: false,
      formulaCount: formulas.length,
      satFormulaCount: satCount,
      unsatFormulaCount: unsatCount,
      maxVariables,
      maxExactSearchGates,
      thresholdModel: 'LockedFinalOutputNonconstantSeed0',
      results,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS0],
    };
  } catch (error) {
    return reject0('LockedNANDSAT.UnhandledException', [], 'locked NAND SAT small-model audit threw unexpectedly', normalizeError0(error));
  }
}

function enumerateBooleanAssignments0(variables) {
  const total = 2 ** variables.length;
  const assignments = [];
  for (let mask = 0; mask < total; mask += 1) {
    const assignment = {};
    for (let index = 0; index < variables.length; index += 1) {
      assignment[variables[index]] = (mask >> (variables.length - index - 1)) & 1;
    }
    assignments.push(assignment);
  }
  return assignments;
}

function reject0(coord, path, reason, witness = {}) {
  return {
    tag: 'reject',
    kind: 'reject',
    checker: 'RunLockedNANDSATSmallModels0',
    version: 0,
    coord,
    path,
    witness: { reason, ...witness },
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    remainingBlockers: [...EXPECTED_BLOCKERS0],
  };
}

function sameArray0(left, right) {
  return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]);
}

function normalizeError0(error) {
  return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null };
}
