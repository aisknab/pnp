import {
  compatibleReplacement0,
  flattenedTruthTable0,
  makeBoundarySource0,
  makeConstSource0,
  makeGateSource0,
  makeNANDWord0,
  sizeOfNANDWord0,
  validateNANDWord0,
} from './nand-direct-wire-reference.mjs';

const DEFAULT_BOUNDARY_SIZES0 = [0, 1, 2];
const DEFAULT_MAX_GATES0 = 2;
const EXPECTED_BLOCKERS0 = ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance'];

export function RunNANDSmallModelAudit0(config = {}) {
  try {
    const cfg = normalizeConfig0(config);
    if (cfg.tag === 'reject') return cfg;

    const families = [];
    let wordCount = 0;
    let equivalenceReplacementChecks = 0;
    let nonEquivalenceRejectChecks = 0;
    let truthClassCount = 0;

    for (const boundarySize of cfg.boundarySizes) {
      const boundary = Array.from({ length: boundarySize }, (_, index) => `x${index}`);
      const words = enumerateNANDWords0({ boundary, maxGates: cfg.maxGates });
      if (words.length === 0) return reject0('NANDSmallModels.EmptyUniverse', ['boundarySizes', boundarySize], 'small-model universe must not be empty');
      wordCount += words.length;

      const classes = new Map();
      for (const word of words) {
        const validation = validateNANDWord0(word);
        if (validation.tag === 'reject') return reject0('NANDSmallModels.GeneratedInvalidWord', ['words'], 'generated word failed validation', { validation, word });
        const size = sizeOfNANDWord0(word);
        if (size.tag === 'reject') return reject0('NANDSmallModels.GeneratedSizeReject', ['words'], 'generated word size rejected', { size, word });
        if (size.size !== word.gates.length) return reject0('NANDSmallModels.SizeMismatch', ['words'], 'size must equal NAND gate count', { expected: word.gates.length, actual: size.size, word });
        const table = flattenedTruthTable0(word);
        if (table.tag === 'reject') return reject0('NANDSmallModels.TruthTableReject', ['words'], 'generated word truth table rejected', { table, word });
        const key = table.bits.join('');
        const bucket = classes.get(key) ?? { key, minSize: Number.POSITIVE_INFINITY, examples: [] };
        bucket.minSize = Math.min(bucket.minSize, size.size);
        bucket.examples.push({ word, size: size.size, bits: table.bits });
        classes.set(key, bucket);
      }

      for (const bucket of classes.values()) {
        for (const example of bucket.examples) {
          if (example.size < bucket.minSize) return reject0('NANDSmallModels.MinSizeInvariant', ['classes', bucket.key], 'example size below computed class minimum', { bucket, example });
        }
      }

      const replacementResult = checkReplacementPairs0(classes);
      if (replacementResult.tag === 'reject') return replacementResult;
      equivalenceReplacementChecks += replacementResult.equivalenceReplacementChecks;
      nonEquivalenceRejectChecks += replacementResult.nonEquivalenceRejectChecks;
      truthClassCount += classes.size;

      families.push({
        boundarySize,
        wordCount: words.length,
        truthClassCount: classes.size,
        minClassSizeHistogram: histogram0([...classes.values()].map((bucket) => bucket.minSize)),
      });
    }

    const badFutureGate = makeNANDWord0({
      boundary: ['x0'],
      gates: [{ id: 'g0', op: 'NAND', left: makeGateSource0('future'), right: makeBoundarySource0('x0') }],
      outputs: [makeGateSource0('g0')],
    });
    const badFutureGateValidation = validateNANDWord0(badFutureGate);
    if (badFutureGateValidation.tag !== 'reject') return reject0('NANDSmallModels.FutureGateAccepted', ['futureGate'], 'future gate references must reject');

    return {
      tag: 'accept',
      kind: 'accept',
      checker: 'RunNANDSmallModelAudit0',
      version: 0,
      coordinate: 'PNP-NAND-SMALL-MODELS-2026-06-27-01',
      smallModelsReady: true,
      fullSmallModelCoverageProved: false,
      boundarySizes: cfg.boundarySizes,
      maxGates: cfg.maxGates,
      outputArity: 1,
      wordCount,
      truthClassCount,
      equivalenceReplacementChecks,
      nonEquivalenceRejectChecks,
      futureGateRejectChecked: true,
      families,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      remainingBlockers: [...EXPECTED_BLOCKERS0],
    };
  } catch (error) {
    return reject0('NANDSmallModels.UnhandledException', [], 'small-model audit threw unexpectedly', normalizeError0(error));
  }
}

export function enumerateNANDWords0({ boundary, maxGates }) {
  const gateSequences = [[]];
  for (let gateCount = 1; gateCount <= maxGates; gateCount += 1) {
    enumerateGateSequences0({ boundary, gateCount, gates: [], out: gateSequences });
  }

  const words = [];
  for (const gates of gateSequences) {
    const sources = sourcesAfterGates0(boundary, gates.length);
    for (const output of sources) {
      words.push(makeNANDWord0({ boundary: [...boundary], gates: clone0(gates), outputs: [output] }));
    }
  }
  return words;
}

function enumerateGateSequences0({ boundary, gateCount, gates, out }) {
  if (gates.length === gateCount) {
    out.push(clone0(gates));
    return;
  }
  const index = gates.length;
  const sources = sourcesAfterGates0(boundary, index);
  for (let leftIndex = 0; leftIndex < sources.length; leftIndex += 1) {
    for (let rightIndex = leftIndex; rightIndex < sources.length; rightIndex += 1) {
      gates.push({ id: `g${index}`, op: 'NAND', left: sources[leftIndex], right: sources[rightIndex] });
      enumerateGateSequences0({ boundary, gateCount, gates, out });
      gates.pop();
    }
  }
}

function sourcesAfterGates0(boundary, gateCount) {
  return [
    ...boundary.map((name) => makeBoundarySource0(name)),
    makeConstSource0(0),
    makeConstSource0(1),
    ...Array.from({ length: gateCount }, (_, index) => makeGateSource0(`g${index}`)),
  ];
}

function checkReplacementPairs0(classes) {
  let equivalenceReplacementChecks = 0;
  let nonEquivalenceRejectChecks = 0;
  const buckets = [...classes.values()].sort((left, right) => left.key.localeCompare(right.key));
  for (const bucket of buckets) {
    if (bucket.examples.length >= 2) {
      const compatible = compatibleReplacement0(bucket.examples[0].word, bucket.examples[1].word);
      if (compatible.tag === 'reject') return reject0('NANDSmallModels.EquivalentReplacementRejected', ['classes', bucket.key], 'equivalent same-boundary words must be compatible replacements', { compatible });
      equivalenceReplacementChecks += 1;
    }
  }
  if (buckets.length >= 2) {
    const incompatible = compatibleReplacement0(buckets[0].examples[0].word, buckets[1].examples[0].word);
    if (incompatible.tag !== 'reject') return reject0('NANDSmallModels.NonEquivalentReplacementAccepted', ['classes'], 'non-equivalent same-boundary words must reject compatible replacement');
    nonEquivalenceRejectChecks += 1;
  }
  return { tag: 'accept', equivalenceReplacementChecks, nonEquivalenceRejectChecks };
}

function normalizeConfig0(config) {
  const boundarySizes = config.boundarySizes ?? DEFAULT_BOUNDARY_SIZES0;
  const maxGates = config.maxGates ?? DEFAULT_MAX_GATES0;
  if (!Array.isArray(boundarySizes) || boundarySizes.length === 0) return reject0('NANDSmallModels.ConfigBoundarySizes', ['boundarySizes'], 'boundarySizes must be a non-empty array');
  for (const value of boundarySizes) {
    if (!Number.isInteger(value) || value < 0 || value > 4) return reject0('NANDSmallModels.ConfigBoundarySize', ['boundarySizes'], 'boundary sizes must be integers between 0 and 4', { value });
  }
  if (!Number.isInteger(maxGates) || maxGates < 0 || maxGates > 3) return reject0('NANDSmallModels.ConfigMaxGates', ['maxGates'], 'maxGates must be an integer between 0 and 3 for the seed audit', { maxGates });
  return { tag: 'accept', boundarySizes, maxGates };
}

function histogram0(values) {
  const map = new Map();
  for (const value of values) map.set(value, (map.get(value) ?? 0) + 1);
  return Object.fromEntries([...map.entries()].sort((left, right) => left[0] - right[0]).map(([key, value]) => [String(key), value]));
}

function reject0(coord, path, reason, witness = {}) {
  return {
    tag: 'reject',
    kind: 'reject',
    checker: 'RunNANDSmallModelAudit0',
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

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

function normalizeError0(error) {
  return { name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code ?? null };
}
