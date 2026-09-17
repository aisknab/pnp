# Structural normalization and arbitrary-support transport

Status: bounded general construction kernel checked; release integration pending.
No milestone is earned until the complete release verification and merge.

## Manuscript anchor and dependency

The document pinned by archive/legacy-v0/ARCHIVE.json specifies structural
congruence R1 and topological reorder/renaming N1 in sections 6.1 and 6.2.
Section 4 and the traceable-normalization theorem require a predecessor support
and replacement expansion with equal surcharge for every compatible descendant
support. Whole-program Boolean equivalence alone does not provide this map.

The intended next bounded result is the physical reordering component of that
all-support transport obligation. It is not a replacement for the remaining
full-profile and materializer rules. It must cover arbitrary dimensions and
arbitrary supports, not a fixed circuit or a selected finite prefix.

## Construction and exact first target

Start from the existing actual raw-graph compiler. Prove that for every accepted
compilation, raw node and corresponding emitted physical position, the program's
literal two source wires are exactly the original pair translated by the
compiler's computed placement map. The target is:

    RawNandWireStructure.compile_sources graph compiled accepted node

with conclusion:

    compiled.program.terminalGateSources (compiled.position node) =
      (compiled.translateSource (graph.gate node).left,
       compiled.translateSource (graph.gate node).right)

The acceptance equation binds the theorem to the actual executable compiler;
an arbitrary result structure with only semantic soundness is insufficient.
Prove the initial-state invariant, emitted-gate preservation, complete-run
preservation and finishing equation. Reuse the computed inverse position map.
Do not add a source-fidelity field as a caller-supplied premise.

This first lemma is only an implementation substep, not the completed milestone.

## Required complete transport result

From a valid finite source circuit and a checked raw node renaming, construct the
reindexed graph and its complete order using the actual compiler. For every
descendant support, derive the predecessor gate set, ordered boundary/interface
bijections and literal replacement reindexing. Prove:

- all independent open valuations and ordered computational field values agree;
- selected gates and the retained exterior correspond bijectively;
- each physical gate is owned once, with no omitted or duplicated component;
- predecessor support and descendant support have equal physical gate count;
- expanded and offered replacements have equal physical gate count;
- the two surcharge differences are zero and strict savings transport backward;
- malformed renamings and cyclic raw graphs fail closed.

Support coordinates and the proposed renaming are operation inputs. Successful
orders, transport maps, equality witnesses or padding are not supplied substitutes
for the missing construction.

Before claiming this complete target, confirm the actual boundary and interface
ordering contracts and the construction's compatibility with literal splicing.
If the general transport proof fails, retain the blocker honestly; do not replace
it with another fixed fixture or a supplied-map conditional theorem.

## Source and expectation matrix

| Producer | Consumers to reconcile | Cheapest evidence |
| --- | --- | --- |
| New literal source-fidelity module | New generic Lean regression and axiom expectations | Exact module build, then imported regression |
| Arbitrary-support transport construction | Generic transport regression, malformed-input and wire/ownership negative fixtures | Targeted module and fixture runs |
| Any changed existing module | Existing Lean regressions and every source-contract audit naming its path or declarations | Source-contract positives and mutations before broad work |
| Final public module set | Explicit root import closure, required names, compiled inventory, publication/status and report generators | Name-set/root-source preflight, then changed chain and root |
| Final milestone claims | Plan, current documentation, fixed progress ledger and normal workflows | Generated current-surface and hostile publication checks |

Keep the existing release candidate frozen while this isolated work runs. Start
the eventual publication branch from the actual verified merge, preserving these
reviewed source changes. Do not treat this detached research checkout as a release.

The cheap current-document preflight must inspect the README's current FAQ table
independently of its leading summary block. Derive all four metrics from the
canonical progress ledger and reconcile the current verification row as well.
A correct metric elsewhere in the document must not mask a stale current table.

## Evidence reuse and remaining boundary

The isolated checkout starts at the exact verified source tree and pinned
toolchain. Seed only the matching existing compiled cache; compile the changed
module before any importing regression. Run no full suite, inventory or report
until the intended general result and all expectation inputs stabilize.

No score change is justified by the structural lemma or an added publication row.
Full manuscript profile semantics, the other normalization/materializer rules,
global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack,
complete polynomial PCCMin, deterministic SAT and the eligible root remain open.
Do not present computational reordering as full manuscript normalization.

Website decision: deferred during research. Reassess only after the complete
general capability is proved; preserve the coherent existing publication pin.

## Concrete raw reordering operation

The next construction takes a valid direct-wire candidate and an arbitrary
finite list of raw natural-number index swaps. The decoder checks every
coordinate, constructs forward and inverse maps by composition, and rejects an
invalid instruction anywhere in the list. Source references and the ordered
output word are relabelled from those maps. Acyclicity follows from the original
program's actual source order, and the existing compiler derives its own order.

Before transport claims, prove the actual physical forward/backward maps are
inverse, each source pair and output reference is mapped exactly, all ordered
outputs agree for all input valuations, and the physical count is unchanged.
The source and regression expectations are added together. Existing source
modules are unchanged.

This constructs the operation, not arbitrary-support transport. Do not infer
full manuscript N1 or the completeness of a permutation-level API from a
fixture. If the final statement quantifies over arbitrary permutations rather
than the checked swap language, establish the encoding's corresponding
expressiveness before publishing that statement.

## Derived physical support correspondence

The current source branch is based on the actual merged predecessor, with the
same verified source tree. The next component constructs forward and inverse
maps for physical wires and primitive records from the reindexer's actual
placement. Record-list round trips must preserve order and duplicates.

The generic contracts require exact selected-gate, external-wire, source-use,
boundary and interface predicates. Every descendant record list is pulled back
by the inverse map; no support family or coverage certificate is supplied.
Boundary and interface lists can change their canonical coordinate order, so
membership correspondence alone does not complete the ordered-port contract.

Add generic imported theorem/axiom regressions together with the source and
guarded runtime checks for nonidentity ordering, empty/full/duplicate supports,
non-gate labels, actual global outputs and local constants. These fixtures are
execution checks, never theorem authority. Only build the new module and imported
regression while this component is isolated; preserve previous verified modules.

After these incidence lemmas, derive finite ordered-port index bijections,
independent open valuations and literal replacement transport. Until those
obligations and exact surcharge identities are proved, the milestone remains
unearned and the website remains deferred.

## Ordered port and ownership indices

For every arbitrary descendant record list, compute the predecessor list by the
actual inverse gate map. Construct explicit finite index bijections between the
two canonical boundary lists, interface lists, selected-gate lists and exterior
lists. Prove both round trips, literal lookup correspondence and equal lengths.
The list helper is internal; the public constructors take only the original
candidate, checked reordering and arbitrary descendant records.

Reindex all independent boundary valuations with the computed port maps and
prove both valuation round trips. Add matching generic imported and axiom
contracts, plus runtime fixtures where incoming and outgoing port order really
changes. Do not confuse valuation bijectivity with preservation of the open
support function: that semantic theorem and literal replacement/surcharge
transport remain the next obligations.

## Independent evaluator equation interface

The existing evaluator is unchanged. Add a small public source-value definition,
its gate-source equation for every independent boundary valuation, exact
boundary-position lookup and the external-absent fallback equation. Prove the
source equation from the evaluator's own recursive implementation with two
private structural lemmas, not from supplied semantic data.

The affected closed-interface consumers are the terminal-support-extraction,
context-aware-square-transport, wire-history-arbitrary-support and
wire-unary-arbitrary-support audits. Append only the four intended public names
and two private helper names where applicable; preserve all previous statement,
source-provenance, import, assumption and hostile-mutation contracts. The profile
locality audit reads unchanged earlier declarations and is included in the
source-only targeted verification.

Build the exact evaluator module before importing its new generic/axiom
regression. Include independent boundary values that cannot be induced by any
whole-circuit input, inert unselected coordinates, actual boundary lookup and
literal constants. This is an equation interface for the existing semantics,
not yet the reordering theorem. Previously proved reordering/support lemmas keep
their statements; their import chain must rebuild after this additive API change
before a downstream imported regression is reused.

## Literal replacement and exact surcharge

Construct the predecessor replacement directly from any descendant candidate:
rename its primary inputs through the computed inverse boundary index and
reindex its output word through the computed forward interface index. Preserve
each offered gate at the same replacement coordinate and prove its two literal
sources, all independent input semantics and exact gate count.

Transport actual extracted-support compatibility, prove both signed surcharge
differences are zero and equal, and preserve the full signed saving and strict
local gain. Add generic imported contracts and runtime negatives for separately
omitting either port permutation, a proper four-gate support replaced by zero
gates, duplicate records, and a nonempty replacement with exact source checks.

These local replacement theorems do not assert acyclicity of an arbitrary splice.
The complete milestone still requires the literal raw-splice node/source/output
correspondence, physical ownership and acceptance/acyclicity transport. Keep all
global, profile and materializer limits unchanged and award no milestone credit
until that remaining boundary is proved and integrated.

## Actual literal-splice coordinate equations

The raw-splice transport needs exact source positions, not just induced Boolean
values. Extend the existing splice module additively with four equations:
primary boundary inputs, gate boundary exterior positions, retained exterior
sources and selected interface replacement outputs. Derive lookup uniqueness
from canonical-list distinctness; do not change the splice algorithm or expose
private generated declaration names.

Append the four public names to the existing arbitrary-splice, wire-history and
wire-unary closed-interface fixtures in the same edit. Preserve all historical
theorem-name, compiled-type, statement, assumption and hostile contracts. The
computed causal dependency audit reads unchanged earlier declarations and needs
no fixture edit. Run the affected source-only contracts before the exact module
and new generic/axiom/runtime regression.

Then derive the two raw-splice node maps from the exterior bijection and identity
replacement indices. Prove exact source pairs and output references, dependency
correspondence, and both directions of acyclicity and compiler acceptance. Do
not assume a compatible arbitrary replacement always produces an acyclic graph.

## Whole raw-splice transport

Construct the complete raw node correspondence by combining the existing
exterior index bijection with identity coordinates for all replacement gates.
Prove both round trips, then actual boundary-source and replacement-source
transport. Use the verified literal exterior/interface equations to transport
all original sources without adding successful-order or source-equality premises.

Prove each raw gate's two literal sources and every ordered global output
reference agree under this map. Derive exact directed-edge correspondence and
transport accessibility in both directions, yielding equivalence of the two
actual compilers' success and failure. These statements cover every offered
replacement, independently of semantic compatibility, including cyclic cases.

The new generic regression must check the complete dependency and compiler
contracts. Guarded execution fixtures cover nonidentity exterior positions,
zero- and nonzero-gate replacements, ordered constants, duplicate records and
a rejected cycle on a nonconvex support. Finite fixtures are not theorem
authority. Refresh the importing Lake target after the additive splice API,
then run the imported regression; do not repeat unchanged broad proof suites.

## Actual compiled physical transport and final replacement theorem

Compose each predecessor compiler physical position through its actual inverse
raw-node map, the computed raw-splice correspondence and the descendant
compiler placement. Prove both physical round trips, exact exterior/replacement
ownership, both literal gate sources and every ordered output reference.
Bind source fidelity to successful actual compiler equations, not just to the
semantic fields of an arbitrary compiled-result record.

From an actual successful descendant compile, compute the predecessor result
from the predecessor compiler itself. Combine independent open compatibility,
whole-circuit semantics, equal physical counts, exact local and whole signed
saving and strict-gain pullback. Acceptance remains conditional on actual
acyclic wiring; preserve the previously proved bidirectional rejection result.

Add focused generic, axiom and runtime regression coverage for this final
compiled boundary before integrating the explicit root and publication model.
Use the earlier verified source and raw-splice evidence unchanged; do not rerun
their isolated suites. This closes the bounded structural reordering target,
not full manuscript profile/materializer semantics or the remaining global
and polynomial obligations. Award no new score merely for the integration.

## Release integration decision

The bounded construction now includes the actual compiler-source invariant, checked raw swaps, arbitrary-record and canonical-port bijections, independent open semantics, literal replacement with zero matched surcharge, both raw dependency and rejection directions, and computed compiled physical transport. Component builds and imported generic, axiom and runtime regressions are verified. Exact theorem-type, module and axiom expectations are frozen before the full explicit-root inventory; no new assumption or weakened theorem is introduced.

Synchronize the explicit-root inventory names, required-name contract, publication row and exact type fingerprints before exporting the full inventory. Update package scripts and their closed fixture, status fields, hostile publication tests and the durable workflow in the same integration. The inventory exporter performs the root build once; do not add a redundant unchanged root build. Run the new exact axiom/regression workflow block only after that root exists. Then derive status, the unchanged fixed-checkpoint score, report and current documentation from the actual generated values. Complete normal PR and exact-merge checks and one independent exact-object reproduction before earning the release.

Publication decision: defer. This closes the computational structural-reordering and literal arbitrary-support replacement-transport edge, but not full manuscript profiles, materializer transport or a global proof obligation. No fixed weighted checkpoint or global gate changes, and the published global bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.

## Compiled release evidence and generated status

The complete explicit-root build and compiled inventory match all 108 pre-reviewed theorem types, defining modules and exact axiom closures. The new durable workflow block has been syntax checked and executed as written, including the explicit-root axiom audit and all ten regression families. No project-specific axioms or eligible root theorem were introduced. Generated status and report source now bind the complete inventory and exact source closure; final hostile publication checks, report verification, full release checks and merge remain pending.

Formal artefact coverage: 246 of 248 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.
