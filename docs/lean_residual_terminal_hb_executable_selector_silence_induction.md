# Executable residual-terminal HB selector-silence induction

`lean/PNP/ResidualTerminalHBExecutableSelectorSilenceInduction.lean`
reconstructs the `Selector-silence induction` named in Section 15 of the pinned
legacy manuscript. It does not assume global semantic exclusion or the
preceding closure theorem's explicit global semantic no-gain premise. Instead,
one executable check verifies the actual
oracle-side condition: every canonical selector row records a typed bottom and
every faithful row passes the existing realizer validator.

## Exact selector-silence check

`TerminalPacketTypedRealizerClaim.isBotBool` distinguishes the claim
constructors directly. It returns false for every gain constructor, including a
gain whose replacement blueprint is otherwise valid, and true only for one of
the typed bottom constructors.

`TerminalPacketTypedRealizerTable.checkSelectorSilent` combines:

- the existing exhaustive faithful-row validity check; and
- an exhaustive bottom-constructor scan over
  `family.packetSelectorHandles`.

The checker-equivalence theorem proves that acceptance is exactly faithful-row
validity plus a bottom equation for every canonical handle. No proof field,
silence flag, selected sublist, or semantic no-gain proposition is accepted as
input.

## Strong rank induction

`TerminalPacketTypedRealizerTable.noFaithful_of_selectorSilent` consumes only
accepted selector silence and accepted HB no-outcome active-dependency closure.
For a faithful handle at rank `r`, existing checked evidence reduces its claim
to a gain or a faithful lower seed after HN and budget activity are eliminated.
The all-row bottom equation makes the gain constructor impossible. The lower
seed has strictly smaller `Fin` rank, so strong induction makes its
faithfulness equation impossible too.

The theorem ranges over arbitrary finite rank and selector carriers. The
rank-indexed corollary exposes the manuscript form for every selector at or
below every supplied rank. The canonical contract retains all-handle selector
silence, exact bottom equations, checked dependency validity, all-node HN/BUD
silence, and well-foundedness together.

## Audit surface

The source-derived axiom transcript covers all 9 public declarations in the
module. The reviewed milestone theorems use only Lean's approved standard
axiom closure and do not reach `Classical.choice`, `sorryAx`, or a
project-specific axiom.

Run the focused checks with:

```text
lake build PNP.ResidualTerminalHBExecutableSelectorSilenceInduction
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalHBExecutableSelectorSilenceInductionAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalHBExecutableSelectorSilenceInduction.lean
node --test audits/lean-residual-terminal-hb-executable-selector-silence-induction0.test.mjs
```

## Boundary

The grouped family, finite rank and faithfulness functions, realizer claim
function, blocker activity functions, dependency rows, and finite-to-exact rank
map remain explicit data inputs. The executable checks validate these data but
do not derive them from terminal candidates or establish manuscript selector
faithfulness, selector compatibility, blocker semantics, or semantic
dependency completeness.

The result establishes the executable selector-silence induction, not the full
unconditional `HB negative closure`. It does not connect positive residual
slack through SaturatePositive and BCELReady to a faithful selector, derive
complete route silence, prove unconditional ZeroSlack or PCCMin, establish
encoded-size or polynomial-runtime bounds, put CNF-SAT in P, remove a project
assumption, or prove `P = NP`.
