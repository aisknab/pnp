# M241 plan: support-independent physical ownership and exact materializer charges

This is a pre-implementation specification, not an earned result.
Preparation uses fully locally verified M240 commit
`03bc59376befee17399b9449f3e5ae0847f9997c`, tree
`3e441fe808fb4aa580c45b7b7e0d57876e64d7ae`.
M240 must pass its ordinary publication and exact-merge release gates before
M241 is published. Reanchor to that actual merge without changing the tested tree.

## Manuscript anchor and dependency edge

The pinned [manuscript](../../archive/legacy-v0/ARCHIVE.json), section 4,
requires computational charges to have a unique owner fixed in the ambient
circuit. Materializer weights are their actual NAND sizes. The disjoint
charge partition underlies ChargeSoundness and later HN/BWL cost accounting.
Section 2.2 gives the open-support extraction semantics.

M236 already accounts for every physical insertion, but its seed-dependent
introduction provenance is explicitly not the ambient ownership map. M240
proves forced minimum growth for independent NAND materializers, not general
ownership. This milestone supplies one missing physical partition kernel:
compute one ownership assignment before selecting a support, extract the
owned pieces as actual circuits, and prove their sizes sum exactly to the
selected physical support size.

This is not a replacement for the manuscript's admissibility requirements.
A deterministic owner is not automatically an admissible carrier, frontier,
or discharged obligation. Keep the existing nonunique-active-owner rejection
in the production transparency classifier unchanged.

## Unbounded construction

For arbitrary dimensions and arbitrary finite raw request data

```text
requests : Fin ownerCount -> List (Fin gates)
```

define `terminalPhysicalOwner requests gate : Option (Fin ownerCount)`
by selecting the first requesting owner in canonical finite-index order.
Return `none` for an unrequested gate; this is the fixed remainder bucket.
No seed, support, trace, numerical weight, ownership proof or coverage
certificate is an input to this assignment.

For each optional owner and arbitrary terminal records, retain precisely
the selected physical gates assigned to that owner. Map those indices back
to physical gate records and call the existing `extractTerminalSupport`.
The output is an actual open-boundary NAND candidate, not a weighted label.

## Exact theorem contracts

For every candidate, request family, record list and gate:

1. If the computed owner is `some owner`, that owner's raw request contains
   the gate. The result is `none` exactly when no request contains it.
2. Membership in an owner's selected piece is equivalent to membership in the
   whole selected support together with equality to the computed ambient owner.
   Consequently the pieces cover all selected gates, are pairwise disjoint,
   and retain the same owner under arbitrary support restriction.
3. The extracted piece's gate count is exactly the length of the physical
   gate list computed for that owner, with duplicates charged only once.
4. With `owners = none :: (allFin ownerCount).map some`:

```text
(owners.map (fun owner =>
  (terminalOwnedPhysicalMaterializer candidate requests records owner).gateCount)).sum
  = (extractTerminalSupport candidate records).gateCount
```

5. For every boundary valuation, each materializer has exactly the existing
   independent open-support semantics of its computed gate records. Under
   boundary values induced by the ambient candidate, each interface output
   equals that original gate's value.
6. The exact charge identity specializes to the candidate's complete physical
   gate set, with total equal to `gates`.

These must hold for all finite dimensions, all overlaps and all unrequested
gates. Do not replace them with fixed instances, a caller-supplied partition
certificate, arbitrary numerical weights, or a precondition that requests
are disjoint or exhaustive.

## Producer and expectation map

- New definitions and arbitrary-dimension theorem types: prepare Lean
  applications, axiom expectations and minimal positive/negative fixtures
  alongside implementation; build the exact dependency before importing it.
- Protect the existing extractor, executor, physical accounting and
  transparency classifier. No change may turn a canonical assignment into
  evidence of unique active admissible ownership.
- Update both reviewed-name producers, theorem fingerprints, the publication
  row, status fields and mutation lists, package-script contract and durable
  workflow assertions as one coherent interface.
- Derive generated counts, hashes, source closure and coordinates only after
  source stabilizes. Run sealed public-surface checks after the inventory,
  publication map and status agree, before the broad suite.
- Update current core documentation from the canonical progress ledger and
  preserve previous historical rows and exact source coordinates.
- Run cheap targeted checks, one deduplicated complete test union, the existing
  report reproduction once, normal PR/post-merge checks, and independent
  exact-object reproduction. Do not repeat unchanged core proof evidence at
  a publication-mirror boundary.

## Regression boundaries

Use universal theorem applications plus small bounded fixtures: zero owners,
zero gates, an empty support, overlapping and duplicate requests, uncovered
gates, metadata-only records, repeated/reordered selected records, and support
restrictions with stable ambient ownership. Include a cross-owner dependency
whose boundary values are induced by the whole circuit. Verify that selecting
an arbitrary owner does not discharge the old nonunique-active-owner test.

Runtime checks are regression evidence, never native proof authority.
Do not run exhaustive reference minima for a charge-partition theorem.

## Remaining obligations and progress

The request family is raw finite data, not the derived manuscript-wide
computational record universe. This milestone does not derive all profile
materializers, prove their admissibility, count proof-only metadata as gates,
justify HN assembly, prove forced full-profile minimum growth, discharge open
obligations, or produce the complete terminal family and global routes.
Polynomial construction/runtime bounds, unconditional SaturatePositive,
BCELReady, ZeroSlack, deterministic CNFSAT in P and the eligible root remain
open. A finite executable partition is not a polynomial-time PCCMin proof.

The reviewed M240 baseline is formal artefact coverage 216 of 218,
risk-weighted proof completion 40%, uncertainty 20% to 40%, and 0 of 5 global
gates closed. No fixed checkpoint changes state for this bounded physical
partition kernel. Add coverage only after all general theorem and release
gates pass; do not preselect a generated row count.

Publication decision: **defer PNPLabs**. This supplies an internal physical
ownership/cost dependency, not a complete admissible materializer route or a
change to the coherent published M231 bottom line.
