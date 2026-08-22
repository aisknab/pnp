# M183 checked finite SaturatePositive-to-BCEL-ready composition

## Evidence-led selection

The formal status still names `Formal.ZeroSlack` as a blocker. The existing
finite terminal reconstruction already computes a candidate-derived saturation
trace, routes the exact first unsafe closure, preserves positive full slack on
an all-safe trace, checks whole-support projection positivity, and computes a
minimum positive BCEL anchor nucleus. Those results remain nested, however: no
single checker exposes the exact successful path from the production finite
`SaturatePositive` classifier to its computed BCEL-ready nucleus.

M183 closes that bounded dependency edge. It does not add another fixed
instance or rerun an existing theorem under a new name: acceptance must
recompute the nested production classifier, and the output retains its exact
selection equality and all proof-bearing data needed by downstream BN3--BN6
work.

## Exact theorem target

For every finite direct-wire candidate, executable saturation model, and
proof-bearing candidate BCEL anchor problem with explicit initial positive full
slack, define one Boolean checker that accepts exactly when
`classifyTerminalFiniteSaturatePositive` returns its positive-projection branch
and the nested `TerminalBCELAnchorNucleusOutcome` is `ready`.

Prove
`PNP.DirectWire.terminal_finite_saturate_positive_bcel_ready_checked_complete`:
checker acceptance reconstructs a certificate containing the exact classifier
equality, safe closure trace, positive final slack, positive whole-support
defect, and computed BCEL nucleus. Project the at-least-two anchor bound, exact
proper-cut constant equation, and complete local BN2 conclusion from that
certificate.

## Claim boundary

The terminal candidate, model, anchor problem, and initial positive full-slack
premise remain explicit. A rejected local branch is not mapped to the complete
global route system. The theorem does not derive positivity from residual
slack, construct BN3--BN6 data or a grouped family, derive constant activation,
establish manuscript-wide `SaturatePositive` or `BCELReady`, prove ZeroSlack or
PCCMin, establish polynomial runtime, put SAT in P, remove a project axiom, or
prove `P = NP`.

## Required evidence

- root import and compiled theorem-inventory inclusion;
- a six-declaration axiom transcript excluding `Classical.choice`;
- generic regression of the accepted certificate and projected conclusions;
- hostile mutations rejecting nested-branch widening, fail-open fallback,
  caller success devices, detached results, assumptions, and overclaims;
- formal-status and publication-map rows with reviewed kernel fingerprints;
- reconstruction, bridge, pipeline, terminology, audit, README, and canonical
  report documentation; and
- durable CI and aggregate-verifier coverage.

## Verification and deduplication

Use lightweight source checks first. Compile and fully verify core PNP once on
the remote builder under the approved resource ceiling. Reuse identical-tree
proof evidence at the merge boundary. PNPLabs consumes the exact verified core
artifacts and audits their publication, browser, provenance, and deployment
binding; it must not execute Lean, Lake, Elan, or the core proof suite.
