const WORD_KIND = 'NANDDirectWireWord0';

export function nand0(left, right) {
  return left === 1 && right === 1 ? 0 : 1;
}

export function makeBoundarySource0(name) {
  return { kind: 'boundary', name };
}

export function makeConstSource0(value) {
  return { kind: 'const', value };
}

export function makeGateSource0(id) {
  return { kind: 'gate', id };
}

export function makeNANDWord0({ boundary, gates, outputs }) {
  return {
    kind: WORD_KIND,
    boundary,
    gates,
    outputs,
  };
}

export function validateNANDWord0(word) {
  if (!plain0(word)) return reject0('NANDWord.Shape', [], 'word must be an object');
  if (word.kind !== WORD_KIND) return reject0('NANDWord.Kind', ['kind'], 'word kind mismatch');
  if (!Array.isArray(word.boundary)) return reject0('NANDWord.BoundaryShape', ['boundary'], 'boundary must be an array');
  if (!Array.isArray(word.gates)) return reject0('NANDWord.GatesShape', ['gates'], 'gates must be an array');
  if (!Array.isArray(word.outputs) || word.outputs.length === 0) return reject0('NANDWord.OutputsShape', ['outputs'], 'outputs must be a non-empty array');

  const boundarySet = new Set();
  for (let index = 0; index < word.boundary.length; index += 1) {
    const name = word.boundary[index];
    if (!name0(name)) return reject0('NANDWord.BoundaryName', ['boundary', index], 'boundary name must be a non-empty string');
    if (boundarySet.has(name)) return reject0('NANDWord.BoundaryDuplicate', ['boundary', index], 'boundary names must be unique', { name });
    boundarySet.add(name);
  }

  const gateSet = new Set();
  for (let index = 0; index < word.gates.length; index += 1) {
    const gate = word.gates[index];
    const path = ['gates', index];
    if (!plain0(gate)) return reject0('NANDWord.GateShape', path, 'gate must be an object');
    if (!name0(gate.id)) return reject0('NANDWord.GateId', [...path, 'id'], 'gate id must be a non-empty string');
    if (boundarySet.has(gate.id)) return reject0('NANDWord.GateIdBoundaryCollision', [...path, 'id'], 'gate id cannot collide with boundary name', { id: gate.id });
    if (gateSet.has(gate.id)) return reject0('NANDWord.GateDuplicate', [...path, 'id'], 'gate ids must be unique', { id: gate.id });
    if (gate.op !== 'NAND') return reject0('NANDWord.GateOp', [...path, 'op'], 'gate op must be NAND');
    const left = validateSource0(gate.left, [...path, 'left'], boundarySet, gateSet);
    if (left.tag === 'reject') return left;
    const right = validateSource0(gate.right, [...path, 'right'], boundarySet, gateSet);
    if (right.tag === 'reject') return right;
    gateSet.add(gate.id);
  }

  for (let index = 0; index < word.outputs.length; index += 1) {
    const output = validateSource0(word.outputs[index], ['outputs', index], boundarySet, gateSet);
    if (output.tag === 'reject') return output;
  }

  return { tag: 'accept' };
}

function validateSource0(source, pathArray, boundarySet, gateSet) {
  if (!plain0(source)) return reject0('NANDWord.SourceShape', pathArray, 'source must be an object');
  if (source.kind === 'boundary') {
    if (!boundarySet.has(source.name)) return reject0('NANDWord.SourceBoundaryUnknown', [...pathArray, 'name'], 'boundary source references an unknown boundary', { name: source.name });
    return { tag: 'accept' };
  }
  if (source.kind === 'const') {
    if (source.value !== 0 && source.value !== 1) return reject0('NANDWord.SourceConstValue', [...pathArray, 'value'], 'constant source value must be 0 or 1', { value: source.value });
    return { tag: 'accept' };
  }
  if (source.kind === 'gate') {
    if (!gateSet.has(source.id)) return reject0('NANDWord.SourceGateNotEarlier', [...pathArray, 'id'], 'gate source must reference an earlier gate', { id: source.id });
    return { tag: 'accept' };
  }
  return reject0('NANDWord.SourceKind', [...pathArray, 'kind'], 'source kind must be boundary, const, or gate', { kind: source.kind });
}

export function evaluateNANDWord0(word, assignment) {
  const validation = validateNANDWord0(word);
  if (validation.tag === 'reject') return validation;
  if (!plain0(assignment)) return reject0('NANDEval.AssignmentShape', ['assignment'], 'assignment must be an object');

  const env = new Map();
  for (const name of word.boundary) {
    if (assignment[name] !== 0 && assignment[name] !== 1) return reject0('NANDEval.AssignmentValue', ['assignment', name], 'assignment value must be 0 or 1', { value: assignment[name] });
    env.set(name, assignment[name]);
  }

  for (const gate of word.gates) {
    const left = evalSource0(gate.left, env);
    const right = evalSource0(gate.right, env);
    env.set(gate.id, nand0(left, right));
  }

  return {
    tag: 'accept',
    outputs: word.outputs.map((source) => evalSource0(source, env)),
  };
}

function evalSource0(source, env) {
  if (source.kind === 'boundary') return env.get(source.name);
  if (source.kind === 'const') return source.value;
  return env.get(source.id);
}

export function enumerateAssignments0(boundary) {
  if (!Array.isArray(boundary)) return [];
  const total = 2 ** boundary.length;
  const out = [];
  for (let mask = 0; mask < total; mask += 1) {
    const assignment = {};
    for (let index = 0; index < boundary.length; index += 1) {
      const bit = (mask >> (boundary.length - index - 1)) & 1;
      assignment[boundary[index]] = bit;
    }
    out.push(assignment);
  }
  return out;
}

export function truthTable0(word) {
  const validation = validateNANDWord0(word);
  if (validation.tag === 'reject') return validation;
  const rows = [];
  for (const assignment of enumerateAssignments0(word.boundary)) {
    const evaluation = evaluateNANDWord0(word, assignment);
    if (evaluation.tag === 'reject') return evaluation;
    rows.push({ assignment, outputs: evaluation.outputs });
  }
  return { tag: 'accept', boundary: [...word.boundary], outputArity: word.outputs.length, rows };
}

export function flattenedTruthTable0(word) {
  const table = truthTable0(word);
  if (table.tag === 'reject') return table;
  return { tag: 'accept', bits: table.rows.flatMap((row) => row.outputs) };
}

export function sizeOfNANDWord0(word) {
  const validation = validateNANDWord0(word);
  if (validation.tag === 'reject') return validation;
  return { tag: 'accept', size: word.gates.length };
}

export function equivalentNANDWords0(left, right) {
  const leftValidation = validateNANDWord0(left);
  if (leftValidation.tag === 'reject') return leftValidation;
  const rightValidation = validateNANDWord0(right);
  if (rightValidation.tag === 'reject') return rightValidation;
  if (!sameArray0(left.boundary, right.boundary)) return reject0('NANDEquivalence.BoundaryMismatch', ['boundary'], 'equivalent words must have identical boundary tuples', { left: left.boundary, right: right.boundary });
  if (left.outputs.length !== right.outputs.length) return reject0('NANDEquivalence.OutputArityMismatch', ['outputs'], 'equivalent words must have the same output arity', { left: left.outputs.length, right: right.outputs.length });
  const leftBits = flattenedTruthTable0(left);
  if (leftBits.tag === 'reject') return leftBits;
  const rightBits = flattenedTruthTable0(right);
  if (rightBits.tag === 'reject') return rightBits;
  return { tag: 'accept', equivalent: sameArray0(leftBits.bits, rightBits.bits), leftBits: leftBits.bits, rightBits: rightBits.bits };
}

export function compatibleReplacement0(supportWord, replacementWord) {
  const eq = equivalentNANDWords0(supportWord, replacementWord);
  if (eq.tag === 'reject') return eq;
  if (!eq.equivalent) return reject0('NANDReplacement.NotEquivalent', ['replacement'], 'replacement word is not truth-table equivalent to the support word', { leftBits: eq.leftBits, rightBits: eq.rightBits });
  return { tag: 'accept', compatible: true };
}

function reject0(coord, pathArray, reason, witness = {}) {
  return { tag: 'reject', coord, path: pathArray, witness: { reason, ...witness } };
}

function plain0(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function name0(value) {
  return typeof value === 'string' && value.length > 0;
}

function sameArray0(left, right) {
  return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]);
}
