# M174 terminal HResolve maximal H-disjoint family

## Evidence-led selection

The pinned manuscript's Section 8.2 `HResolve` theorem requires accepted
proper hereditary leaves to be assembled into a maximal H-disjoint family.
H-disjointness simultaneously covers support, frontier, origin, kernel,
obligation, prefix-tail, charge, and interface noninterference. The current
terminal HResolve milestones provide a complete finite candidate ledger and
computed exact-or-gain semantics, but explicitly leave H-disjoint family
assembly and blocker semantics open.

M174 closes that named assembly edge before attempting HN grammar, BWL, or
ParseOrExit. It is generic over arbitrary finite candidate families and every
coordinate type, rather than a fixed circuit, coordinate list, or family size.

## Target

For every duplicate-free finite family of hereditary footprints whose eight
coordinate domains have decidable equality:

1. define exact H-disjointness as simultaneous list disjointness in all eight
   manuscript domains;
2. reflect an executable Boolean to that exact proposition;
3. return the first exact interference domain when two candidates are not
   H-disjoint;
4. deterministically recurse through the complete supplied family, retaining
   a candidate exactly when it is H-disjoint from the already selected tail;
5. prove every selected candidate came from the governed family;
6. prove the selected family remains duplicate-free and pairwise H-disjoint;
   and
7. prove maximality: every governed candidate is selected or has a selected
   blocker with an exact support, frontier, origin, kernel, obligation,
   prefix-tail, charge, or interface interference route.

The named endpoint is
`PNP.DirectWire.terminal_hresolve_maximal_hdisjoint_family_complete`.

## Claim boundary

The governed footprints remain inputs. M174 does not derive accepted HN leaves
from a direct-wire candidate, formalize the pair/tripod/spine/non-flat grammar,
prove BWL exactness or ParseOrExit, establish leaf tightness, solve a leaf,
construct the full H0-H4 NoHereditary sidecar, connect blocker edges to HB
ranks, or prove polynomial encoding/runtime. It does not complete HResolve,
BudgetResolve, the ZeroSlack no-lower ledger, unconditional ZeroSlack, PCCMin,
concrete SAT, the root theorem, or project-axiom removal.

## Required evidence

- root import and compiled theorem-inventory inclusion;
- an explicit axiom transcript for every public declaration;
- regression fixtures covering pairwise selection and every named interference
  domain, including a governed candidate rejected by a selected blocker;
- hostile mutations for omitted domains, caller-supplied acceptance or
  maximality, non-maximal selection, assumptions, fixed family bounds, and
  claim widening;
- publication-map and formal-status rows with reviewed kernel fingerprints;
- current reconstruction, audit, pipeline, terminology, README, and canonical
  report documentation; and
- durable CI and aggregate-verifier coverage.

## Verification order

Run the focused source audit first. On the configured remote builder, compile
the new module and root import before the axiom transcript and regression.
Regenerate the compiled theorem inventory, publication payloads, and canonical
report only after the theorem surface stabilizes. Finish with the complete core
suite and one fresh exact-head reproduction. PNPLabs will consume the resulting
verified artifacts byte-for-byte and will not compile Lean.
