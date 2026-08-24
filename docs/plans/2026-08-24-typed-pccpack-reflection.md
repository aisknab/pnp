# M188 typed PCCPack generation and reflection

## Evidence-led selection

The active Lean bridge has only two project-specific axioms left:
`PNP.GeneratePCCPack` and `PNP.CheckPCCPackexp`.  Both occur in
`PNP.Bridge`, where `PCCPack` currently contains only a string identifier and
the accepted-package implication asks `CheckerTrustModel` to manufacture a
`PCCMinLoopCertificate` from the opaque checker equation.  The actual proof
burden is therefore obscured behind two global constants and one caller
reflection field.

M188 replaces that boundary with a universal typed interface.  A Lean
`PCCPack` will carry the exact `PCCMinLoopCertificate` consumed by the active
bridge.  `GeneratePCCPack` will be a transparent function from an explicit
loop certificate, and `CheckPCCPackexp` will be a transparent structural
identifier check.  The generated identifier is canonical, a generated pack
is accepted by computation, a mismatched identifier is rejected, and the
certificate projected from a generated pack is definitionally the supplied
certificate.  No certificate, minimizer, SAT-hardness proof, or final theorem
is manufactured by this change.

## Legacy anchor and unbounded abstraction

- Legacy anchor: the canonical manuscript's package generation, typed
  reflection, acceptance, and final bridge layers in Sections 18.3, 20.4,
  20.7, 20.9, 20.13, and 20.21.
- Closed edge: explicit proof-bearing `PCCMinLoopCertificate` -> canonical
  typed `PCCPack` -> structural checker verdict -> exact certificate
  projection used by the active residual-band bridge.
- Unbounded abstraction: every `PCCMinLoopCertificate`, including its complete
  concrete finite-pipeline residual-band decider and proof fields.  The result
  is not tied to a finite fixture, a supplied truth bit, or one materialized
  JavaScript package.

## Exact theorem target

Define transparent functions with the general types

```text
PNP.GeneratePCCPack : PNP.PCCMinLoopCertificate -> PNP.PCCPack
PNP.CheckPCCPackexp : PNP.PCCPack -> PNP.Verdict
```

and prove for every loop certificate:

```text
PNP.check_generated_pcc_pack_exp_accepts
PNP.generated_pcc_pack_loop_certificate_exact
PNP.typed_pccpack_reflection_checked_complete
```

The complete theorem must package canonical identifier generation, computed
acceptance, exact certificate projection, and rejection of every pack whose
identifier differs from the canonical generated identifier.  Refactor
`AcceptedGeneratedPackage` and `FinalReportAntecedent` so that existence of the
proof-bearing loop certificate is explicit, and remove the obsolete
`CheckerTrustModel.pccPackProducesPCCMinLoop` field.  The active bridge may then
use the projected certificate directly; `CheckerTrustModel` retains only the
separate concrete SAT-hardness premise.

## Claim boundary and downstream blockers

M188 does not construct a `PCCMinLoopCertificate`, prove the semantics named by
its string metadata, implement or verify the historical JavaScript serializer
or checker, derive terminal candidates or routing data, prove unconditional
ZeroSlack, define the complete PCCMin loop, establish encoded-size polynomial
bounds, produce a residual-band decider, prove concrete SAT hardness, put
CNFSAT in P, create `PNP.Main.p_eq_np`, open a global gate, or prove `P = NP`.
The final bridge remains conditional on existence of an explicit proof-bearing
loop certificate and on concrete SAT hardness.

This closes exactly the two fixed one-point checkpoints
`axiom-remove-generate-pccpack` and `axiom-remove-check-pccpackexp`.  The
compiled project-axiom inventory must fall from two to zero before either
checkpoint is credited.  The risk-weighted estimate may then move from 33 to
35 percent, while the 20--40 percent uncertainty range and all five open
global gates remain unchanged.  One formal-publication row is added, so
current coverage should move from 163/165 to 164/166.

## Required evidence

- focused Lean compilation and axiom transcripts for the transparent
  generator, structural checker, exact projection, complete M188 theorem,
  active bridge, and root import;
- regression of arbitrary loop certificates, canonical acceptance, mismatched
  identifier rejection, exact projection, the existential report antecedent,
  and the one-field checker trust boundary;
- hostile checks rejecting restoration of either project axiom, a string-only
  `PCCPack`, an always-accept checker without identifier comparison, a supplied
  checker-success Boolean, a recreated reflection field, a hidden default loop
  certificate, or widened ZeroSlack/PCCMin/runtime/final claims;
- compiled theorem-inventory and formal-status updates showing zero remaining
  project axioms, the absent eligible root, false publication gate, and all
  five global blockers still open;
- two fixed-checkpoint score transitions with exact compiled evidence and an
  unchanged uncertainty range; and
- complete core and PNPLabs publication, review, clean-merge reproduction,
  deployment, provenance, route, and service verification gates.

## Verification and deduplication

Run source-contract checks first.  Compile the changed Lean bridge and explicit
root once on the capped remote builder, then run the focused regression and
axiom audit.  After source stabilization, regenerate the inventory, status,
progress ledger, publication map, TeX, and PDF, and run the complete core suite
once.  PNPLabs consumes the exact merged core artifacts and performs its full
current-surface publication audit without rebuilding Lean already proved for
the same core tree.
