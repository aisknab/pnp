# Proof progress model

The project reports two independent measurements. They answer different
questions and must never be combined.

## Formal artefact coverage

Formal artefact coverage counts earned rows in the current formal publication
milestone ledger. At
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-29-206`, 182 of 184
current scoped rows are earned, or 98.9 percent of that evidence ledger.

This is not proof completion. Rows are not equal units of mathematical
difficulty, and the denominator can grow when a dependency is discovered or an
obligation is decomposed. New finite, local, conditional, or supplied-data
results can add valuable evidence without retiring a global proof obligation.

## Risk-weighted proof completion estimate

The version 0 model assigns 100 fixed points to load-bearing checkpoints:

| Track | Available | Earned at M206 |
| --- | ---: | ---: |
| Formal foundations and proof infrastructure | 15 | 13 |
| Concrete reductions and locked-NAND route | 20 | 15 |
| Unconditional residual core and ZeroSlack | 35 | 2 |
| Exact PCCMin algorithm, complexity and bounds | 20 | 1 |
| Root theorem and project-axiom elimination | 10 | 4 |
| **Total** | **100** | **35** |

The M206 risk-weighted proof completion estimate is therefore 35 percent, with
a current uncertainty range of 20 to 40 percent. This is a conservative estimate
of how much of the complete formal proof burden has been retired. It is not the
probability that `P = NP`, confidence that the proposed route is correct, or an
estimate of time remaining.

The exact checkpoint definitions, evidence, remaining limitations, gate states,
score-change record requirements, and baseline history are in the canonical
machine-readable ledger:

[`status/PROOF_PROGRESS.json`](../status/PROOF_PROGRESS.json)

The five current global gates are open: Concrete SAT, residual-band minimisation,
unconditional ZeroSlack, polynomial runtime and certificate bounds, and the root
theorem plus axiom audit. The compiled project-specific axiom inventory is empty,
`PNP.Main.p_eq_np` is absent, and the publication gate is false.

The immutable scoring baseline remains M184: 160 of 162 formal artefact rows,
30 risk-weighted points, a 20-to-40-percent uncertainty range, and zero of five
global gates closed. M185 added a finite activation-coherence diagnostic row,
so its coverage was 161 of 163. It did not close a fixed checkpoint or change
the 30-percent estimate. Both reviews are recorded separately
in the canonical ledger history. M186 then makes the report-facing SAT and
locked-NAND endpoints exact concrete finite-pipeline languages, consumes the
compiled all-bitstring reduction without caller trust, and removes
`PNP.LockedNANDThreshold` from the project-axiom inventory. Those compiled
changes close exactly `reductions-final-target-compatibility` and
`axiom-remove-locked-nand-threshold`, moving the score from 30 to 32 and current
coverage to 162 of 164. M187 then makes the residual-band endpoint a concrete
encoded exact-minimum threshold predicate, proves its arbitrary typed-candidate
semantics, replaces the supplied compatibility edge with an identity reduction,
and removes `PNP.ResidualBandExactMinimization` from project-specific proof
authority. That closes exactly `axiom-remove-residual-band-minimum`, moving the
score from 32 to 33 and current coverage to 163 of 165. The uncertainty range
remains 20 to 40 percent and all five global gates remain open. M188 then makes
the PCCPack generator and checker transparent typed definitions over an explicit
loop certificate, removing `PNP.GeneratePCCPack` and
`PNP.CheckPCCPackexp` from project-specific proof authority. Those two fixed
one-point checkpoints move the score from 33 to 35 and coverage to 164 of 166.
The certificate's existence, exactness construction, polynomial runtime,
deterministic SAT theorem, and root theorem remain open; no global gate closes
and the uncertainty range remains 20 to 40 percent. M189 then formalizes the
general proof-bearing total-oracle loop: its checked gain branches preserve
semantics and strictly lower slack, terminal branches carry exactness, recursion
is well-founded, and gain iterations are bounded by initial slack. Because the
total oracle remains an explicit supplied boundary and the regression fixture
uses exhaustive reference minimization, no fixed checkpoint closes. Coverage
becomes 165 of 167 while the score remains 35 percent, the uncertainty range
remains 20 to 40 percent, and all five gates remain open. M190 then composes the
manuscript's proof-bearing NormalizeOrGain and PCCOracle stages: semantic
normalization cannot increase gate count, subsequent oracle gains lift to
strict gains from the original implementation, and exact or ZeroSlack endpoints
transport back through normalization into the checked recursive loop. Because
the total normalizer and oracle remain explicit arguments and the regression
fixtures use exhaustive reference minimization, no fixed checkpoint closes.
Coverage becomes 166 of 168 while the score remains 35 percent, the uncertainty
range remains 20 to 40 percent, and all five gates remain open. M191 then
reconstructs the oracle's internal manuscript order: HResolve precedes
BudgetResolve, arbitrary finite selector rows are scanned at every canonical
rank, and ZeroSlack is reachable only through a complete typed-blocker ledger.
Because the component algorithms, selector data, blocker semantics, and final
ZeroSlack closure remain explicit supplied boundaries, no fixed checkpoint
closes. Coverage becomes 167 of 169 while the score remains 35 percent, the
uncertainty range remains 20 to 40 percent, and all five gates remain open.
M192 then replaces the arbitrary selector-row and proof-bearing realizer inputs
with a complete checked data-only Packet table and derives exact rows from the
canonical handle list plus supplied rank map. Because the family, rank map,
claim data, resolvers, blocker semantics, and ZeroSlack closure remain supplied,
no fixed checkpoint closes. Coverage becomes 168 of 170 while the score remains
35 percent, the uncertainty range remains 20 to 40 percent, and all five gates
remain open. M193 then removes the opaque complete-silence-to-ZeroSlack callback:
accepted rank-row silence is reflected into the executable selector-silence
checker, checked HB closure eliminates every faithful canonical handle, and an
explicit positive-slack-to-faithful-selector premise supplies the final
contradiction. Because that positive-slack bridge, terminal data, resolvers,
normalizer, and polynomial construction remain supplied or open, no fixed
checkpoint closes. Coverage becomes 169 of 171 while the score remains 35
percent, the uncertainty range remains 20 to 40 percent, and all five gates
remain open. No retrospective score was invented.

M194 then removes M193's arbitrary positive-slack-to-faithful-selector
callback. Positive slack now supplies only the earlier constant-activation
boundary; the existing general BN6 theorem constructs the positive Packet, and
the route-clear payload checker constructs a faithful selector in the
canonicalized table before the checked HB contradiction derives conditional
ZeroSlack. Because constant activation, terminal data, route-clear evidence,
resolvers, normalizer, and polynomial construction remain supplied or open, no
fixed checkpoint closes. Coverage becomes 170 of 172 while the score remains
35 percent, the uncertainty range remains 20 to 40 percent, and all five gates
remain open. No retrospective score was invented.

M195 then removes M194's opaque positive-slack-to-constant-activation callback
from the new endpoint. It binds a supplied Packet family to the same-candidate
checked BCEL nucleus and exhaustively classifies its carrier, cut value, and
every canonical nonempty proper-cut activation weight. The coherent branch
derives constant activation and conditional ZeroSlack; each failure remains a
typed mismatch route. Because the terminal problem, positive premise, checked
ready certificate, family, tables, ranks, route-clear and HB data, resolvers,
normalizer, and polynomial construction remain supplied or open, and the
mismatch routes are not gains or globally decreasing transitions, no fixed
checkpoint closes. Coverage becomes 171 of 173 while the score remains 35
percent, the uncertainty range remains 20 to 40 percent, and all five gates
remain open. No retrospective score was invented.

M196 then removes M195's independently supplied Packet carrier and cut value.
The BN6 family skeleton now takes its carrier, carrier uniqueness, cut value,
and cut-value positivity from the same checked BCEL nucleus. Carrier and
cut-value mismatch routes are impossible by construction; the new endpoint
retains only an exact proper-cut activation mismatch or conditional ZeroSlack.
Because the grouped cells, payloads, grouping proofs, tables, ranks,
route-clear and HB data, resolvers, normalizer, and polynomial construction
remain supplied or open, and the remaining activation mismatch is not a gain
or globally decreasing transition, no fixed checkpoint closes. Coverage
becomes 172 of 174 while the score remains 35 percent, the uncertainty range
remains 20 to 40 percent, and all five gates remain open. No retrospective
score was invented.

M197 then removes M196's supplied V54 consumer systems, singletonization
certificates, exact group-footprint-size proofs, and duplicate-free grouping
proof. Each supplied raw support is normalized inside the checked BCEL carrier,
its singleton consumer system is constructed, duplicate footprints are
coalesced, and every positive payload atom is preserved before the canonical
grouped family reuses M196. The raw supports and payload atoms are still
supplied rather than derived from BN3, BN4, BN5, PkgC, or every terminal input;
the remaining activation mismatch is not a gain or globally decreasing route;
and the inherited finite cut scan may be exponential. No fixed checkpoint or
global gate closes. Coverage becomes 173 of 175 while the score remains 35
percent, the uncertainty range remains 20 to 40 percent, and all five gates
remain open. No retrospective score was invented.

M198 then proves an arbitrary-finite conservation theorem at the BN4/BN6
activation edge. Collecting raw positive payload atoms by canonical normalized
footprint and coalescing duplicate footprints preserves the exact crossing-
mass sum on every cut. The checked PCCMin endpoint now expresses its surviving
BCEL obstruction directly as a mismatch between that raw positive-cell cut
ledger and the checked defect, rather than through an opaque grouped-family
activation total. The raw cells remain supplied rather than derived from every
terminal input; the constant-activation equation remains open; the mismatch is
not a gain or globally decreasing transition; and the inherited finite cut
scan may be exponential. No fixed checkpoint or global gate closes. Coverage
becomes 174 of 176 while the score remains 35 percent, the uncertainty range
remains 20 to 40 percent, and all five gates remain open. No retrospective
score was invented.

M199 then proves that a shape-specific sparse V53 basis is equivalent to the
complete proper-cut constant equation on every finite carrier of size at least
two. Its total classifier checks only the two-anchor full weight, three
singleton cuts, or four-plus full-span support and weight. At the checked PCC
boundary, an accepted basis derives constant activation and reuses the
Packet/BN6/BCEL/HB conditional ZeroSlack contradiction without calling M195's
powerset classifier; a rejection remains one typed structural obstruction.
Raw cells and the remaining terminal, table, rank, route, HB, and polynomial
construction data remain supplied; basis rejection is not a gain or global
rank decrease; and upstream construction may still enumerate subsets. No
fixed checkpoint or global gate closes. Coverage becomes 175 of 177 while the
score remains 35 percent, the uncertainty range remains 20 to 40 percent, and
all five gates remain open. No retrospective score was invented.

M200 replaces M199's structural-only rejection with the first exact
singleton-or-pair proper cut whose crossing weight misses the checked value.
Lean proves for every finite sparse positive V53 carrier of size at least two
that this duplicate-free, quadratic-size test family is equivalent to the
complete proper-cut constant equation. The checked adapter reflects a
mismatch into M198's direct raw activation ledger or reaches M199's
conditional ZeroSlack branch. Raw cells and terminal, table, rank, route, HB,
and complete encoded-input polynomial construction data remain supplied; the
local family-size bound is not complete PCCMin runtime, and the mismatch is
not a gain or global rank decrease. No fixed checkpoint or global gate closes.
Coverage becomes 176 of 178 while the score remains 35 percent, the
uncertainty range remains 20 to 40 percent, and all five gates remain open. No
retrospective score was invented.

M201 reconstructs the next PkgC-to-BN6 edge over arbitrary finite supplied
active V54 consumer systems. Its total classifier returns the first exact
same-key cancellation realization or proves every source singletonized; that
branch derives each raw BN6 positive-cell support from the consumer footprint,
derives support size at least two from activity, preserves payload order, and
conserves the exact activation weight on every cut. The terminal source
systems, active cuts, payload atoms, typed restorer, and upstream BN3--BN5
construction remain supplied; cancellation is not a global gain or rank
decrease, and no complete encoded-size polynomial construction is proved. No
fixed checkpoint or global gate closes. Coverage becomes 177 of 179 while the
score remains 35 percent, the uncertainty range remains 20 to 40 percent, and
all five gates remain open. No retrospective score was invented.

M202 composes M201's source-derived positive cells directly with M200's
checked sparse BN6/BCEL/Packet/HB route. Its total classifier retains the
exact source-member same-key cancellation, returns genuine conditional
ZeroSlack under supplied checked selector silence, or reflects one nonempty
proper singleton/pair activation mismatch through all-cut conservation to the
original PkgC source ledger. No independent raw BN6 ledger is accepted. The
terminal problem, checked ready certificate, source systems and cuts,
payloads, restorer, realizer table, claims, ranks, dependency table, checked
HB closure, route-clear result, and selector silence remain supplied;
cancellation or mismatch is not a gain or global rank decrease, and no
complete encoded-size polynomial construction is proved. No fixed checkpoint
or global gate closes. Coverage becomes 178 of 180 while the score remains 35
percent, the uncertainty range remains 20 to 40 percent, and all five gates
remain open. No retrospective score was invented.

M203 removes the caller-supplied remainder and permutation seam from M202's
PkgC cancellation branch. Constructive remove-first recursion computes an
order-independent, multiplicity-preserving ambient BN4 remainder with an exact
permutation and complete residual-ledger equality, or proves that no exact
remainder embedding exists. The candidate-bound BN4 kernel is constructed from
the same checked BCEL nucleus, while conditional ZeroSlack and the source
activation mismatch branches remain unchanged. The terminal source systems,
ambient ledger, payloads, restorer, downstream tables and selector silence
remain supplied; the remainder is not proved empty and neither extraction
failure nor cancellation reduction is a global gain or rank decrease. No fixed
checkpoint or global gate closes. Coverage becomes 179 of 181 while the score
remains 35 percent, the uncertainty range remains 20 to 40 percent, and all
five gates remain open. No retrospective score was invented.

M204 replaces the always-total supplied typed-restorer branch at this local
PkgC boundary with the arbitrary-finite restoration-coordinate classifier.
The incomplete-coverage branch retains an exact Hall deficit and forced Q
route. Complete coverage constructs balanced opposite-sign BN4 unit cells
for every canonical quotient coordinate, then computes an arbitrary-order
ambient remainder with exact residual-ledger reduction or proves no exact
embedding. The restoration universe and maps, consumer system and ambient
ledger remain supplied; equality-fibre coverage does not materialize
semantic full candidates, the Hall route is not a verified global gain, and
the computed remainder is not proved empty. No fixed checkpoint or global
gate closes. Coverage becomes 180 of 182 while the score remains 35 percent,
the uncertainty range remains 20 to 40 percent, and all five gates remain
open. No retrospective score was invented.

M205 lifts the M204 restoration-coverage result over the complete
arbitrary-finite active PkgC source ledger in canonical list order. Only the
all-source singletonized branch constructs the BN6 positive-cell ledger, with
exact length, payload order, and activation-weight conservation on every cut;
otherwise the first exact source-member Hall, ambient-reduction, or
no-embedding evidence is retained. The source cells and active cuts, payloads,
per-source restoration universes and maps, and ambient BN4 ledgers remain
supplied. The Hall route is not a verified global gain, the computed remainder
is not proved empty, and ambient incompatibility is not a complete global
route. No fixed checkpoint or global gate closes. Coverage becomes 181 of 183
while the score remains 35 percent, the uncertainty range remains 20 to 40
percent, and all five gates remain open. No retrospective score was invented.

M206 binds the complete M205 restoration-coverage ledger to one computed
BCEL nucleus and composes only its all-singletonized branch with the checked
sparse BN6/BCEL Packet/HB classifier. The first exact Hall, ambient-reduction,
or no-embedding outcome is preserved; the downstream branch yields conditional
ZeroSlack or reflects one proper singleton/pair activation mismatch to the
original enriched source ledger. The terminal problem, checked certificate,
source cells and cuts, restoration universes and maps, ambient ledgers, ranks,
claims, dependency table, checked HB closure, route-clear result, and selector
silence remain supplied. No obstruction is yet a verified global descent and
the computed remainder is not proved empty. No fixed checkpoint or global gate
closes. Coverage becomes 182 of 184 while the score remains 35 percent, the
uncertainty range remains 20 to 40 percent, and all five gates remain open. No
retrospective score was invented.

## Changing the score

A future score change must change the state of a fixed checkpoint and record its
old and new state, exact compiled evidence, source coordinate or commit,
load-bearing rationale, remaining track limitations, old and new totals, and an
uncertainty-range decision. The score can decrease when evidence is invalidated,
an assumption returns, hidden exponential work is found, or a new load-bearing
obligation appears.

The following do not automatically earn points: tests, documentation, theorem or
declaration counts, publication rows, fixed instances, schedule slots,
conditional sidecars, supplied-object theorems, regenerated reports, CI work,
refactors, and external review. Polynomial-runtime points require a theorem that
bounds the complete construction uniformly in encoded source-input size.

Validate the ledger against the formal reconstruction status and compiled
theorem inventory with:

```bash
npm run formal:progress
```

The validator checks the fixed 100-point model, recomputes earned points and
formal artefact coverage independently, verifies checkpoint evidence, and rejects
conflicting gate, axiom, root-theorem, or publication states.
