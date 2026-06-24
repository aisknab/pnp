import {
  makeKBundleReflectionSuccessor0,
} from '../../pcc-kbundle-reflection-successor0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from '../../pcc-global-proof-dag0.mjs';

import {
  makeGlobalInfrastructureSemanticSuite0,
} from '../../pcc-global-infrastructure-semantic0.mjs';

import {
  makeSyntheticRowPack0,
} from '../../pcc-rows0.mjs';

import {
  makeSyntheticRowFamG0,
} from '../../pcc-gpack0.mjs';

import {
  makeGlobalRowSemanticSuite0,
} from '../../pcc-global-row-semantic0.mjs';

import {
  makeSyntheticLocalPackages0,
} from '../../pcc-local-packages0.mjs';

import {
  makeGlobalPackageSemanticSuite0,
} from '../../pcc-global-package-semantic0.mjs';

import {
  makeGlobalFinalPrefixPCCPack0,
  makeGlobalFinalPrefixSemanticInput0,
  makeGlobalFinalPrefixSemanticSuite0,
} from '../../pcc-global-final-prefix-semantic0.mjs';

import {
  makeGlobalProofDAGFinalPrefixSuccessor0,
} from '../../pcc-global-proof-dag-final-prefix-successor0.mjs';

import {
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticFiniteRelJudgment0,
  makeSemanticFiniteRelClaim0,
  makeSemanticFiniteRelDomain0,
  makeSemanticFiniteRelNode0,
  makeSemanticFiniteRelProgram0,
  makeSemanticFiniteRelSpec0,
  makeSemanticFiniteRelTuple0,
} from '../../pcc-kernel-finiterel-semantic0.mjs';

export function makeFinalPrefixFiniteRelProof0() {
  const domain = makeSemanticFiniteRelDomain0({
    index: 0,
    id: 'D',
    elements: ['a', 'b'],
  });
  const literal = makeSemanticFiniteRelNode0({
    index: 0,
    id: 'R',
    op: 'literal',
    domainIds: ['D', 'D'],
    tuples: [makeSemanticFiniteRelTuple0({ index: 0, values: ['a', 'b'] })],
  });
  const closure = makeSemanticFiniteRelNode0({
    index: 1,
    id: 'R.rtc',
    op: 'reflexive-transitive-closure',
    domainIds: ['D', 'D'],
    inputIds: ['R'],
  });
  const program = makeSemanticFiniteRelProgram0({
    programId: 'global.final.prefix.semantic.program',
    domains: [domain],
    nodes: [literal, closure],
    claims: [
      makeSemanticFiniteRelClaim0({
        index: 0,
        id: 'claim.R.in.rtc',
        claimKind: 'included',
        leftId: 'R',
        rightId: 'R.rtc',
      }),
      makeSemanticFiniteRelClaim0({
        index: 1,
        id: 'claim.rtc.closed',
        claimKind: 'reflexive-transitive-closed',
        leftId: 'R.rtc',
      }),
    ],
  });
  const spec = makeSemanticFiniteRelSpec0({
    evaluationId: 'global.final.prefix.semantic.eval',
    program,
  });
  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'finiterel.global.final.prefix.semantic',
      RuleName: 'FiniteRel',
      Conclusion: deriveSemanticFiniteRelJudgment0({ spec }),
      Payload: { op: 'verify', spec },
    }),
  ]);
}

export function makeFinalPrefixSurfaces0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
  LocalPackages = makeSyntheticLocalPackages0(),
  PCCPack = null,
} = {}) {
  const KBundle = makeKBundleReflectionSuccessor0({
    SemanticProofDAG: makeFinalPrefixFiniteRelProof0(),
  });
  const resolvedPack = PCCPack ?? makeGlobalFinalPrefixPCCPack0({
    LegacyGlobalProofDAG,
    RowPack,
    RowFamG,
    LocalPackages,
  });
  const InfrastructureSemanticDerivations =
    makeGlobalInfrastructureSemanticSuite0({ LegacyGlobalProofDAG });
  const RowSemanticDerivations = makeGlobalRowSemanticSuite0({
    LegacyGlobalProofDAG,
    RowPack,
    RowFamG,
  });
  const PackageSemanticDerivations = makeGlobalPackageSemanticSuite0({
    LegacyGlobalProofDAG,
    LocalPackages,
  });
  const FinalPrefixSemanticDerivations =
    makeGlobalFinalPrefixSemanticSuite0({
      LegacyGlobalProofDAG,
      PCCPack: resolvedPack,
    });
  return {
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    RowPack,
    RowFamG,
    RowSemanticDerivations,
    LocalPackages,
    PackageSemanticDerivations,
    PCCPack: resolvedPack,
    FinalPrefixSemanticDerivations,
  };
}

export function makeFinalPrefixSemanticInput0(options = {}) {
  const surfaces = makeFinalPrefixSurfaces0(options);
  return makeGlobalFinalPrefixSemanticInput0({
    ...surfaces,
    SemanticFinalPrefix: surfaces.FinalPrefixSemanticDerivations,
  });
}

export function makeFinalPrefixSuccessorInput0({
  Purpose = 'development',
  ...options
} = {}) {
  const surfaces = makeFinalPrefixSurfaces0(options);
  return makeGlobalProofDAGFinalPrefixSuccessor0({
    ...surfaces,
    Purpose,
  });
}

export function withoutFinalPrefixDigest0(node, changes) {
  const out = { ...node, ...changes };
  delete out.Digest;
  delete out.digest;
  return out;
}
