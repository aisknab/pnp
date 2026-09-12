# M247: computed constant propagation for arbitrary NAND programs

## Legacy anchor and dependency edge

The pinned manuscript's section 2 direct-wire language explicitly includes
constant 0/1 sources, earlier gate outputs and an ordered output tuple. Section 5
Package E names R1 structural congruence, alongside R4 sharing, as primitive
rewrite work. M242 constructs gate-to-gate sharing, but its alias type cannot
replace a gate by a constant source.

Close that concrete R1 construction edge for all finite programs: derive source
aliases from the program, substitute them before inspecting each NAND gate,
eliminate NAND gates whose value follows from literal constant sources, and
rewrite every ordered output. This is an unbounded program pass, not another
fixed circuit, supplied optimizer or semantic enumeration.

The pass uses exactly the constant NAND identities: a false input yields true;
two true inputs yield false. Other gates are retained. Earlier eliminated
constants must propagate through later gates in the same traversal.

## Exact general targets

For arbitrary program dimensions, construct the result together with:

- An alias in the retained source language for every original gate.
- Alias semantics for every input assignment and original gate.
- Retained gate count plus actual elimination count equal to source gate count.

For every complete implementation, prove full ordered-output equivalence,
non-increasing physical size, reference-minimum invariance, exact residual-slack
savings, strict gain exactly when an elimination happened, and strict residual
descent. Package the actual pass in the existing total normalizer interface.

The primitive constant recognizer has a general soundness theorem over every
source pair and input/gate valuation. The main equivalence theorem has no
supplied correctness premise:

    Equivalent (constantPropagationImplementation current).candidate.program
      (constantPropagationImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord

## Claim boundary and downstream obligations

A no-elimination result is not semantic minimality or ZeroSlack. In particular,
NAND(x, NAND(x,x)) is constant true without any literal constant source; the pass
must retain it and the regression must exhibit a smaller equivalent word.
Do not broaden the recognizer merely to make that stopping test disappear.

This is a physical structural-congruence component. It does not derive the
manuscript's complete carrier, traceable arbitrary-support pullback/expansion,
R5/R6-R8 obligation ledger, N1-N10 normalization, complete Package E, total PCCMin
oracle or any unconditional global route. Reference minima occur in specification
theorems, not in execution. No encoded-size polynomial runtime theorem is claimed.

## Source and expectation changes together

Prepare general type regressions, exact reviewed names and axiom expectations
with the source. Bound runtime fixtures to constant truth cases, left/right
false sources, cascading eliminations, a surviving nonconstant gate, primary
inputs, constants and repeated outputs, empty dimensions, and the no-elimination
nonminimum example.

Hostile contracts must reject invented aliases, skipped output rewriting,
incorrect NAND constants, fake elimination counts, supplied correctness, finite
or weakened theorem types, axiom injection and global-completion overclaims.
Update the root, compiled inventory producer/consumer, audit, permanent workflow,
status fields and publication fingerprints as one interface.

## Verification and publication

Use one independent remote checkout and an exact source-tree/toolchain cache
preflight. Run bounded leaf feedback, arbitrary type/runtime regressions, root,
exact workflow block and fingerprints; freeze Lean before inventory sealing.
Reconcile status, canonical progress, current documentation and compiled contracts
before their focused checks. Run one reproducible report and one deduplicated
standard suite. Preserve PR/post-merge and exact-object checks while reusing
unchanged-tree heavyweight evidence.

No fixed checkpoint is expected to close. Formal artefact coverage may increase;
risk-weighted proof completion stays 40% with 20% to 40% uncertainty unless a named
checkpoint is actually earned. The five global gates and eligible root remain open.

Publication decision: defer PNPLabs. This physical R1 component does not change
the coherent published M231 bottom line. Notify meaningful verified substeps
independently of site cadence.

Remove the exact temporary checkout, fixtures, logs and transport parent after
release verification or the completed diagnosis of an abandoned approach.
