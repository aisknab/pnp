import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  LoadMaterializedPCCPackShellFile0,
} from './pcc-materialized-loader0.mjs';

import {
  CheckMaterializedArtefactDeps0,
  makeMaterializedArtefactDependencyShell0,
} from './pcc-materialized-artefact-deps0.mjs';

import {
  sha256Utf8DigestRecord0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_PROOF_REF_KINDS0 = Object.freeze([
  'KPrimitive',
  'SigmaInstance',
  'ReflectionInstance',
  'EarlierArtefactProof',
]);

export const MATERIALIZED_PROOF_REF_POLICY0 = Object.freeze({
  kind: 'MaterializedProofRefPolicy0',
  version: CHECKER_VERSION,
  allowedRefKinds: MATERIALIZED_PROOF_REF_KINDS0,
  earlierArtefactOnly: true,
  rejectsOpaqueProofMaterial: true,
  requiresDependencyCoverage: true,
});

export function makeMaterializedProofRef0({
  refKind,
  id,
  artefactName = null,
  rule = null,
  theorem = null,
  checker = null,
} = {}) {
  if (!MATERIALIZED_PROOF_REF_KINDS0.includes(refKind)) {
    throw new TypeError(`unknown proof ref kind: ${String(refKind)}`);
  }

  if (typeof id !== 'string' || id.length === 0) {
    throw new TypeError('makeMaterializedProofRef0 requires a non-empty id');
  }

  const ref = {
    kind: 'ProofRef0',
    version: CHECKER_VERSION,
    refKind,
    id,
  };

  if (artefactName !== null) {
    ref.artefactName = artefactName;
  }

  if (rule !== null) {
    ref.rule = rule;
  }

  if (theorem !== null) {
    ref.theorem = theorem;
  }

  if (checker !== null) {
    ref.checker = checker;
  }

  return ref;
}

export function makeMaterializedProofRefShell0(overrides = {}) {
  const shell = makeMaterializedArtefactDependencyShell0();
  const packObject = JSON.parse(shell.PackBytes);
  const artefactOrder = packObject.Manifest.artefactOrder;

  packObject.Manifest = {
    ...packObject.Manifest,
    proofRefPolicy: {
      ...MATERIALIZED_PROOF_REF_POLICY0,
    },
  };

  for (const artefactName of artefactOrder) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const deps = packObject.Manifest.artefactDependencies[artefactName] ?? [];

    packObject[artefactName] = {
      ...packObject[artefactName],
      proofRefs: [
        makeMaterializedProofRef0({
          refKind: 'KPrimitive',
          id: `K.${artefactName}.record`,
          rule: 'Record',
        }),
        makeMaterializedProofRef0({
          refKind: 'ReflectionInstance',
          id: `Reflection.${artefactName}.soundness`,
          checker: `Check${artefactName}0`,
        }),
        ...deps.map((dep) => makeMaterializedProofRef0({
          refKind: 'EarlierArtefactProof',
          id: `${artefactName}.depends.${dep}`,
          artefactName: dep,
        })),
      ],
    };
  }

  shell.PackBytes = stableStringify0(packObject);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  return {
    ...shell,
    ...overrides,
  };
}

export async function CheckMaterializedProofRefs0(shell, config = {}) {
  const checker = 'CheckMaterializedProofRefs0';
  const ledger = [];

  const depsRecord = await CheckMaterializedArtefactDeps0(shell, config.depsConfig ?? {});
  const deps = recordToValidation0(depsRecord, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedArtefactDeps0',
    status: deps.ok ? 'pass' : 'fail',
    digest: depsRecord.Digest ?? depsRecord.digest ?? digestCanonical0(depsRecord),
  });

  if (!deps.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.deps`,
      path: deps.path,
      witness: deps.witness,
      ledger,
    });
  }

  const manifest = depsRecord.Manifest;
  const packObject = depsRecord.PackObject;

  const policy = validateProofRefPolicy0(manifest);

  ledger.push({
    phase: 'proofRefPolicy',
    status: policy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
  });

  if (!policy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.proofRefPolicy`,
      path: policy.path,
      witness: policy.witness,
      ledger,
    });
  }

  const shape = validateProofRefLists0(packObject, manifest);

  ledger.push({
    phase: 'proofRefLists',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.proofRefLists`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const refs = validateProofRefs0(packObject, manifest);

  ledger.push({
    phase: 'proofRefs',
    status: refs.ok ? 'pass' : 'fail',
    digest: digestCanonical0(refs.nf ?? refs.witness ?? null),
  });

  if (!refs.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.proofRefs`,
      path: refs.path,
      witness: refs.witness,
      ledger,
    });
  }

  const dependencyCoverage = validateDependencyProofCoverage0(packObject, manifest);

  ledger.push({
    phase: 'dependencyProofCoverage',
    status: dependencyCoverage.ok ? 'pass' : 'fail',
    digest: digestCanonical0(dependencyCoverage.nf ?? dependencyCoverage.witness ?? null),
  });

  if (!dependencyCoverage.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.dependencyProofCoverage`,
      path: dependencyCoverage.path,
      witness: dependencyCoverage.witness,
      ledger,
    });
  }

  const noOpaque = validateNoOpaqueProofMaterial0(packObject, ['PackBytes']);

  ledger.push({
    phase: 'noOpaqueProofMaterial',
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

  const nf = {
    kind: 'MaterializedProofRefs0NF',
    checker,
    version: CHECKER_VERSION,
    artefactCount: manifest.artefactOrder.length,
    proofRefCount: proofRefCount0(packObject, manifest),
    allowedRefKinds: MATERIALIZED_PROOF_REF_KINDS0,
    proofRefDigest: digestCanonical0(proofRefSummary0(packObject, manifest)),
    manifestDigest: digestCanonical0(manifest),
    packDigest: shell.PackDigest,
  };

  return {
    ...makeAcceptRecord({
      checker,
      nf,
      ledger,
    }),
    Manifest: manifest,
    PackObject: packObject,
    manifest,
    packObject,
  };
}

export async function CheckMaterializedProofRefsFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedProofRefsFile0';
  const ledger = [];

  const loaded = await LoadMaterializedPCCPackShellFile0(filePath, config.loaderConfig ?? {});
  const loadResult = recordToValidation0(loaded, ['file']);

  ledger.push({
    phase: 'load',
    status: loadResult.ok ? 'pass' : 'fail',
    digest: loaded.Digest ?? loaded.digest ?? digestCanonical0(loaded),
  });

  if (!loadResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.load`,
      path: loadResult.path,
      witness: loadResult.witness,
      ledger,
    });
  }

  const checked = await CheckMaterializedProofRefs0(loaded.Shell, config);
  const checkResult = recordToValidation0(checked, ['Shell']);

  ledger.push({
    phase: 'CheckMaterializedProofRefs0',
    status: checkResult.ok ? 'pass' : 'fail',
    digest: checked.Digest ?? checked.digest ?? digestCanonical0(checked),
  });

  if (!checkResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.proofRefs`,
      path: checkResult.path,
      witness: checkResult.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedProofRefsFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: loaded.NF.filePath,
    byteLength: loaded.NF.byteLength,
    fileDigest: loaded.NF.fileDigest,
    proofRefsDigest: checked.Digest ?? checked.digest,
    proofRefCount: checked.NF.proofRefCount,
    artefactCount: checked.NF.artefactCount,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateProofRefPolicy0(manifest) {
  const policy = manifest.proofRefPolicy;

  if (!isPlainObject(policy)) {
    return validationReject0(['PackBytes', 'Manifest', 'proofRefPolicy'], 'Pack.Manifest proofRefPolicy must be an object', {
      actual: typeof policy,
    });
  }

  if (!Array.isArray(policy.allowedRefKinds)) {
    return validationReject0(['PackBytes', 'Manifest', 'proofRefPolicy', 'allowedRefKinds'], 'proofRefPolicy allowedRefKinds must be an array', {
      actual: typeof policy.allowedRefKinds,
    });
  }

  for (const refKind of MATERIALIZED_PROOF_REF_KINDS0) {
    if (!policy.allowedRefKinds.includes(refKind)) {
      return validationReject0(['PackBytes', 'Manifest', 'proofRefPolicy', 'allowedRefKinds', refKind], 'proofRefPolicy is missing an allowed proof ref kind', {
        refKind,
      });
    }
  }

  if (policy.earlierArtefactOnly !== true) {
    return validationReject0(['PackBytes', 'Manifest', 'proofRefPolicy', 'earlierArtefactOnly'], 'proofRefPolicy must require earlier artefact proof references', {
      actual: policy.earlierArtefactOnly,
    });
  }

  if (policy.rejectsOpaqueProofMaterial !== true) {
    return validationReject0(['PackBytes', 'Manifest', 'proofRefPolicy', 'rejectsOpaqueProofMaterial'], 'proofRefPolicy must reject opaque proof material', {
      actual: policy.rejectsOpaqueProofMaterial,
    });
  }

  if (policy.requiresDependencyCoverage !== true) {
    return validationReject0(['PackBytes', 'Manifest', 'proofRefPolicy', 'requiresDependencyCoverage'], 'proofRefPolicy must require dependency proof coverage', {
      actual: policy.requiresDependencyCoverage,
    });
  }

  return validationAccept0({
    kind: 'MaterializedProofRefPolicy0NF',
  });
}

function validateProofRefLists0(packObject, manifest) {
  for (const artefactName of manifest.artefactOrder) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const artefact = packObject[artefactName];

    if (!isPlainObject(artefact)) {
      return validationReject0(['PackBytes', artefactName], 'materialized artefact must be an object before proof ref checking', {
        artefactName,
        actual: typeof artefact,
      });
    }

    if (!Object.prototype.hasOwnProperty.call(artefact, 'proofRefs')) {
      return validationReject0(['PackBytes', artefactName, 'proofRefs'], 'materialized artefact must declare proofRefs', {
        artefactName,
      });
    }

    if (!Array.isArray(artefact.proofRefs)) {
      return validationReject0(['PackBytes', artefactName, 'proofRefs'], 'materialized artefact proofRefs must be an array', {
        artefactName,
        actual: typeof artefact.proofRefs,
      });
    }

    if (artefact.proofRefs.length === 0) {
      return validationReject0(['PackBytes', artefactName, 'proofRefs'], 'materialized artefact proofRefs must be non-empty', {
        artefactName,
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedProofRefLists0NF',
  });
}

function validateProofRefs0(packObject, manifest) {
  const orderIndex = new Map(manifest.artefactOrder.map((artefactName, index) => [artefactName, index]));
  const seenIds = new Set();

  for (const artefactName of manifest.artefactOrder) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const refs = packObject[artefactName].proofRefs;

    for (let index = 0; index < refs.length; index += 1) {
      const ref = refs[index];

      if (!isPlainObject(ref)) {
        return validationReject0(['PackBytes', artefactName, 'proofRefs', index], 'proofRef must be an object', {
          artefactName,
          actual: typeof ref,
        });
      }

      if (ref.kind !== 'ProofRef0') {
        return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'kind'], 'proofRef kind must be ProofRef0', {
          artefactName,
          actual: ref.kind,
        });
      }

      if (!MATERIALIZED_PROOF_REF_KINDS0.includes(ref.refKind)) {
        return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'refKind'], 'proofRef refKind is not allowed', {
          artefactName,
          actual: ref.refKind,
        });
      }

      if (typeof ref.id !== 'string' || ref.id.length === 0) {
        return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'id'], 'proofRef id must be a non-empty string', {
          artefactName,
          actual: ref.id,
        });
      }

      if (seenIds.has(ref.id)) {
        return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'id'], 'proofRef ids must be globally unique', {
          artefactName,
          id: ref.id,
        });
      }

      seenIds.add(ref.id);

      if (ref.refKind === 'EarlierArtefactProof') {
        const target = ref.artefactName ?? ref.targetArtefact ?? ref.target;

        if (target === 'AcceptRun' || target === 'AcceptRun0') {
          return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'artefactName'], 'EarlierArtefactProof must not target AcceptRun', {
            artefactName,
            target,
          });
        }

        if (typeof target !== 'string' || target.length === 0) {
          return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'artefactName'], 'EarlierArtefactProof must name a target artefact', {
            artefactName,
            actual: target,
          });
        }

        if (!orderIndex.has(target)) {
          return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'artefactName'], 'EarlierArtefactProof target is unknown', {
            artefactName,
            target,
          });
        }

        if (orderIndex.get(target) >= orderIndex.get(artefactName)) {
          return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'artefactName'], 'EarlierArtefactProof target must be an earlier artefact', {
            artefactName,
            target,
            artefactIndex: orderIndex.get(artefactName),
            targetIndex: orderIndex.get(target),
          });
        }
      }

      if (ref.refKind === 'KPrimitive' && (typeof ref.rule !== 'string' || ref.rule.length === 0)) {
        return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'rule'], 'KPrimitive proofRef must name a kernel rule', {
          artefactName,
          ref,
        });
      }

      if (ref.refKind === 'SigmaInstance' && (typeof ref.theorem !== 'string' || ref.theorem.length === 0)) {
        return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'theorem'], 'SigmaInstance proofRef must name a theorem', {
          artefactName,
          ref,
        });
      }

      if (ref.refKind === 'ReflectionInstance' && (typeof ref.checker !== 'string' || ref.checker.length === 0)) {
        return validationReject0(['PackBytes', artefactName, 'proofRefs', index, 'checker'], 'ReflectionInstance proofRef must name a checker', {
          artefactName,
          ref,
        });
      }
    }
  }

  return validationAccept0({
    kind: 'MaterializedProofRefsShape0NF',
    proofRefCount: seenIds.size,
  });
}

function validateDependencyProofCoverage0(packObject, manifest) {
  for (const artefactName of manifest.artefactOrder) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const deps = manifest.artefactDependencies[artefactName] ?? [];
    const refs = packObject[artefactName].proofRefs ?? [];

    for (const dep of deps) {
      const hasRef = refs.some((ref) => (
        isPlainObject(ref) &&
        ref.refKind === 'EarlierArtefactProof' &&
        (ref.artefactName ?? ref.targetArtefact ?? ref.target) === dep
      ));

      if (!hasRef) {
        return validationReject0(['PackBytes', artefactName, 'proofRefs'], 'materialized artefact proofRefs must cover every declared dependency', {
          artefactName,
          missingDependency: dep,
        });
      }
    }
  }

  return validationAccept0({
    kind: 'MaterializedDependencyProofCoverage0NF',
  });
}

function validateNoOpaqueProofMaterial0(value, path) {
  const hit = findOpaqueProofMaterial0(value, path);

  if (hit !== null) {
    return validationReject0(hit.path, 'materialized proof references reject opaque proof material', hit);
  }

  return validationAccept0({
    kind: 'MaterializedProofRefsNoOpaque0NF',
  });
}

function findOpaqueProofMaterial0(value, path = []) {
  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findOpaqueProofMaterial0(value[index], [...path, index]);

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
    if (isOpaqueProofMaterialKey0(key)) {
      return {
        key,
        path: [...path, key],
        value: value[key],
      };
    }

    const hit = findOpaqueProofMaterial0(value[key], [...path, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function isOpaqueProofMaterialKey0(key) {
  const normalized = String(key).replace(/[_\-\s]/g, '').toLowerCase();

  return (
    normalized === 'opaqueproof' ||
    normalized === 'opaqueproofblob' ||
    normalized === 'proofblob' ||
    normalized === 'trustedblob' ||
    normalized === 'trustedproofblob' ||
    normalized === 'assumeproof'
  );
}

function proofRefCount0(packObject, manifest) {
  let count = 0;

  for (const artefactName of manifest.artefactOrder) {
    if (artefactName === 'Core' || artefactName === 'Manifest') {
      continue;
    }

    const refs = packObject[artefactName]?.proofRefs;

    if (Array.isArray(refs)) {
      count += refs.length;
    }
  }

  return count;
}

function proofRefSummary0(packObject, manifest) {
  return manifest.artefactOrder.map((artefactName) => ({
    artefactName,
    proofRefs: Array.isArray(packObject[artefactName]?.proofRefs)
      ? packObject[artefactName].proofRefs.map((ref) => ({
          refKind: ref.refKind,
          id: ref.id,
          artefactName: ref.artefactName ?? null,
          rule: ref.rule ?? null,
          theorem: ref.theorem ?? null,
          checker: ref.checker ?? null,
        }))
      : [],
  }));
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