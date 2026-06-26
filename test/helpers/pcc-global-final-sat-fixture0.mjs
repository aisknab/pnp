import {
  makeGlobalFinalSATSemanticInput0,
  makeGlobalFinalSATSemanticSuite0,
} from '../../pcc-global-final-sat-semantic0.mjs';

import {
  makeGlobalProofDAGFinalSATSuccessor0,
} from '../../pcc-global-proof-dag-final-sat-successor0.mjs';

import {
  makeFinalPrefixSurfaces0,
} from './pcc-global-final-prefix-fixture0.mjs';

export function makeFinalSATSurfaces0(options = {}) {
  const surfaces = makeFinalPrefixSurfaces0(options);
  return {
    ...surfaces,
    FinalSATSemanticDerivations: makeGlobalFinalSATSemanticSuite0({
      LegacyGlobalProofDAG: surfaces.LegacyGlobalProofDAG,
      PCCPack: surfaces.PCCPack,
    }),
  };
}

export function makeFinalSATSemanticInput0(options = {}) {
  const surfaces = makeFinalSATSurfaces0(options);
  return makeGlobalFinalSATSemanticInput0({
    ...surfaces,
    SemanticFinalSAT: surfaces.FinalSATSemanticDerivations,
  });
}

export function makeFinalSATSuccessorInput0({
  Purpose = 'development',
  ...options
} = {}) {
  const surfaces = makeFinalSATSurfaces0(options);
  return makeGlobalProofDAGFinalSATSuccessor0({
    ...surfaces,
    Purpose,
  });
}

export function withoutFinalSATDigest0(node, changes) {
  const out = { ...node, ...changes };
  delete out.Digest;
  delete out.digest;
  return out;
}
