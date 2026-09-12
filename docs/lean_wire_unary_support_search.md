# Computed complete search for proper constant and unary R7 gains

M258 derives a complete support search from the computational carrier itself.
Neither a successful support nor a candidate family is supplied to the search.

Formal artefact coverage: 234 of 236 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

## Specification and scope

The route reconstructs the support-discovery edge of section 6.1's unary cut
realization and VerifyDW in the manuscript pinned by
[the immutable archive manifest](../archive/legacy-v0/ARCHIVE.json).
Package E requires a proper physical support, an equivalent complete local word
and strict physical saving. Sections 2 and 3 specify the incoming boundary and
completed frontier; sections 4 and 6.2 govern matched Pull/Expand accounting.

Input count, original gate count, ordinary output width, computational field
count and the support quantified by the completeness theorem are arbitrary.
The eligible supports have zero or one actual incoming boundary wire and a
nonempty original exterior. The complete frontier includes all computational
fields, not only ordinary outputs.

M257 already constructs and compiles the minimum complete zero/unary word for
any such support. M258 supplies the missing source-derived discovery step.
The production search does not enumerate all supports or all implementations.

## Source-derived candidate family

Choose either no boundary or a wire actually consumed by a gate.
There are at most two consumed wire occurrences per original gate. Repeated
occurrences may remain. Boundary-choice enumeration excludes unused declared
inputs; this statement is about the choices, not all downstream extraction work.

For each choice and an omitted original gate, scan the source in topological
order. Select precisely the gates that are neither the omitted gate nor the
chosen boundary gate, and whose sources are constants, already selected gates
or the chosen boundary. This maximal admissible selection has at most one actual
incoming boundary. The omitted gate makes it proper.

Add every canonical singleton gate support. With g original gates, the family
has at most (2*g+1)*g+g entries, each containing at most g gate records.
The list and every candidate are computed from the source; they are not
caller-supplied coverage certificates.

These are physical candidate-count and record-count bounds. Inherited
physical-port extraction and compilation retain their own execution costs.
No complete encoded-size polynomial runtime, output-size or certificate-size
theorem is claimed.

## Why the search is complete in this class

For any arbitrary proper zero/unary support, its boundary choice occurs among
the gate-consumed wires, and an omitted exterior gate exists. Induction over the
source program proves that the corresponding maximal selection contains every
selected gate of the original support.

If that support has at least two gates, the containing maximal candidate also
has at least two. Its complete zero/unary realization uses at most one shared
NOT, so the existing proper-gain checker succeeds.

If the support has one gate, the canonical singleton occurs in the family.
The inherited physical extraction congruence shows that repeated gate records
and non-gate records selecting the same gates preserve the boundary, complete
frontier, open function and gate count. The one-gate saving therefore transfers.
An empty support cannot have a strictly smaller realization.

The general theorem quantifies over every strictly smaller equivalent complete
local open realization of every eligible support. This comparison word and its
semantic agreement are premises of the mathematical completeness statement,
not inputs to the executable search.

## Actual returned gain and precise negative result

The carrier-only search runs the actual proper-gain checker on the computed
family. A successful result identifies an actual proper support and constructs
its expanded carrier. Every ordinary output and every full computational field
is preserved at every ambient valuation. The replacement and original exterior
are charged exactly once, and the total saving is strict.

For each original source-bound R5 identity, the result constructs an R7 witness
at the same field coordinate, with the actual expanded source and the complete
original field value. No rank, compiler-success result, agreement or full-value
certificate is supplied to the search.

A negative result excludes every strict gain on proper zero/unary supports.
It is not global minimality or unconditional ZeroSlack. The regression suite
includes a two-boundary duplicate with an explicit smaller ambient realization
for which this restricted search correctly returns no gain.

Whole-support saving is not a proper-support Package E certificate.
Preserving ordinary outputs without full computational fields is insufficient.

## Reviewed general interfaces

All 36 interfaces build from the explicit PNP root and have exact reviewed
kernel-type fingerprints. Six use only propext; the other 30 use only propext
and Quot.sound. No project-specific axiom or Classical.choice is used.

| Exact declaration | Checked interface |
| --- | --- |
| `PNP.DirectWire.WireUnarySupportSearch.maximalSelection_admissible` | The source scan selects only gates admissible for its boundary and omitted gate. |
| `PNP.DirectWire.WireUnarySupportSearch.maximalSelection_contains` | Every admissible selection is contained in the maximal source-derived selection. |
| `PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected_iff` | Canonical gate records select exactly the indicated physical gates. |
| `PNP.DirectWire.WireUnarySupportSearch.gateRecords_selected` | Canonical records recover the selected gate list. |
| `PNP.DirectWire.WireUnarySupportSearch.admissible_boundary` | Each actual incoming boundary wire is the chosen wire. |
| `PNP.DirectWire.WireUnarySupportSearch.admissible_boundary_small` | An admissible support has at most one actual incoming boundary. |
| `PNP.DirectWire.WireUnarySupportSearch.candidateRecords_boundary` | Every maximal candidate has a zero/unary actual boundary. |
| `PNP.DirectWire.WireUnarySupportSearch.candidateRecords_proper` | Every maximal candidate retains a positive original exterior. |
| `PNP.DirectWire.WireUnarySupportSearch.consumedWires_length` | There are at most two gate-consumed wire occurrences per original gate. |
| `PNP.DirectWire.WireUnarySupportSearch.boundary_mem_consumedWires` | Every actual support boundary wire occurs among gate-consumed wires. |
| `PNP.DirectWire.WireUnarySupportSearch.boundaryChoices_length` | The boundary-choice list has at most twice the gate count plus one entry. |
| `PNP.DirectWire.WireUnarySupportSearch.candidateFamily_length` | The complete candidate family satisfies its physical quadratic count bound. |
| `PNP.DirectWire.WireUnarySupportSearch.candidateFamily_maximal_mem` | Every chosen-boundary and omitted-gate maximal support occurs in the family. |
| `PNP.DirectWire.WireUnarySupportSearch.candidateFamily_singleton_mem` | Every canonical singleton support occurs in the family. |
| `PNP.DirectWire.WireUnarySupportSearch.supportChoice_wire_mem` | The selected boundary choice is an actual boundary wire. |
| `PNP.DirectWire.WireUnarySupportSearch.supportChoice_of_mem` | A zero/unary support boundary determines its unique selected choice. |
| `PNP.DirectWire.WireUnarySupportSearch.supportChoice_external` | The selected boundary is outside the support. |
| `PNP.DirectWire.WireUnarySupportSearch.supportChoice_mem` | Every zero/unary support choice occurs in the computed choices. |
| `PNP.DirectWire.WireUnarySupportSearch.support_admissible` | Every eligible support is admissible for its own boundary and any exterior gate. |
| `PNP.DirectWire.WireUnarySupportSearch.support_contained_in_candidate` | Every eligible support is contained in its computed maximal candidate. |
| `PNP.DirectWire.WireUnarySupportSearch.selected_length_mono` | Physical selected-gate count is monotone under selection containment. |
| `PNP.DirectWire.WireUnarySupportSearch.selected_length_le` | The selected physical gate count cannot exceed the source gate count. |
| `PNP.DirectWire.WireUnarySupportSearch.candidateFamily_entry_length` | Each candidate contains at most the source gate count in records. |
| `PNP.DirectWire.WireUnarySupportSearch.extracted_gateCount_mono` | Extracted gate count is monotone under physical selection containment. |
| `PNP.DirectWire.WireUnarySupportSearch.singleton_selection` | A one-gate support and its canonical singleton select the same physical gate. |
| `PNP.DirectWire.WireUnarySupportSearch.checkedGain_selection_invariant` | Proper-gain recognition is invariant under the same selected gate predicate. |
| `PNP.DirectWire.WireUnarySupportSearch.candidateFamily_complete` | Every eligible strict local gain makes some computed family candidate succeed. |
| `PNP.DirectWire.WireUnarySupportSearch.findGain_complete` | The executable carrier-only search succeeds for every proper zero/unary local gain. |
| `PNP.DirectWire.WireUnarySupportSearch.findGain_member` | Every returned support belongs to the computed family. |
| `PNP.DirectWire.WireUnarySupportSearch.findGain_records_bound` | Every returned support respects the physical record-count bound. |
| `PNP.DirectWire.WireUnarySupportSearch.GainResult.checked` | A returned result has a proper zero/unary support, strict saving, full fields and exact charge. |
| `PNP.DirectWire.WireUnarySupportSearch.findGain_none_excludes` | No result rules out every strict local gain in this precise support class. |
| `PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_source_exact` | The R7 witness uses the actual expanded source for the original R5 identity. |
| `PNP.DirectWire.WireUnarySupportSearch.GainResult.dischargeR7_full_value` | The R7 witness preserves its original full computational field value. |
| `PNP.DirectWire.WireUnarySupportSearch.findReplacement_isSome` | Public replacement recognition agrees with the actual support search. |
| `PNP.DirectWire.WireUnarySupportSearch.findReplacement_sound` | Every returned replacement is a strict equivalent gain and preserves all fields. |

See the [main Lean source](../lean/PNP/NANDWireUnarySupportSearch.lean),
[root-importing regressions](../lean-regression/PNPWireUnarySupportSearch.lean),
[exact axiom audit](../lean-audit/PNPWireUnarySupportSearchAxiomAudit.lean),
[publication contracts](../audits/lean-wire-unary-support-search0.test.mjs)
and [recorded plan](./plans/2026-09-13-computed-unary-support-search.md).
No inherited theorem statement, definition or proof body changes in M258.

## Regression and hostile evidence

Eighteen guarded scenarios cover empty dimensions, free fields, no proper gain,
whole-support-only saving, singleton constants, maximal multi-gate savings,
primary and external-gate boundaries, early constant observations, hidden fields,
unrealizable open boundary bits, repeated and metadata records, two-boundary
rejection and the public returned replacement.

Tiny exhaustive comparisons are regression evidence for the general completeness
theorem, not the production algorithm. The wide unused-input fixture checks only
candidate enumeration and the runtime guard; it does not enumerate all valuations.
Runtime execution is test evidence, not theorem authority.

Hostile contracts reject supplied candidate families and completeness premises,
weakened signatures, assumption-backed types, stale fingerprints, omitted full
fields, wrong physical bounds and claims of global or polynomial completion.

## Remaining boundary and publication decision

Completeness is for proper physical supports with zero or one actual incoming boundary in a computational wire carrier. It is not completeness for all boundary widths, every R7 case or all ambient circuit optimizations. A negative search result is not global minimality or unconditional ZeroSlack; a guarded two-boundary duplicate fixture has an explicit smaller global realization while this scoped search correctly returns no gain. A whole-support saving is not a proper-support Package E certificate. Boundary-choice enumeration excludes unused declared inputs, but inherited physical-port extraction and compilation retain their own execution costs. The physical candidate and record counts are not a theorem of total uniformly polynomial encoded-input-size execution, output size or certificate size. The full manuscript carrier, noncomputational profile fields, arbitrary obligation dependency DAGs, every R5-R8 interaction, all-trace N1-N10 normalization, complete Package E, global routing, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and its complete polynomial bounds remain open. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

Publication decision: publish a batched PNPLabs update only after this complete
support-search capability is fully earned and released. It materially changes
the end-to-end computational R7 path from the published M231 bottom line.
The trigger is the general capability, not the accumulated milestone count.

Keep the coherent published source pin unchanged until all release gates pass.
Then batch pending earned core results from the latest exact verified merge and
audit the complete site publication surface, reusing the core Lean and report
evidence. No fixed weighted checkpoint or global gate closes.
