# Lean concrete machine and cost kernel

`lean/PNP/Concrete/BitString.lean` and `lean/PNP/Concrete/Machine.lean` provide the first concrete
complexity-model foundation. Every executable object is syntax interpreted by Lean; no `String`
field or arbitrary function is treated as machine code.

## Encodings and bounds

`BitString` is `List Bool` with length as its input-size measure. A frame contains a unary length,
a delimiter, and the payload. The decoder rejects missing delimiters, short payloads, and trailing
data. Lean proves frame and pair round trips, injectivity, the frame prefix-free property, and exact
encoded lengths.

`NatPolynomial` is executable syntax built from natural constants, one variable, addition, and
multiplication. Its monotonicity theorem is constructive; there is no subtraction or caller-supplied
runtime function hidden in the bound.

## Machine semantics

`Machine` contains a finite `List Rule`, a start state, and designated accept/reject states. A
configuration contains a natural control state and a focused single tape. `step?` selects the first
matching rule; `run` consumes an explicit transition budget and performs no transition at zero
fuel. `boundedDecide` inspects the configuration after the bounded run and returns `accept`,
`reject`, or `timeout`.

`PolynomialTimeMachine language` contains:

- the finite rule-list machine;
- a `NatPolynomial` time bound;
- a proof that execution does not time out at that bound; and
- a proof that acceptance at that bound is equivalent to `language input`.

The zero-step accept/reject machines and a stuck machine exercise all three verdicts. A one-rule
machine proves separately that zero fuel cannot execute a transition and one fuel can execute one
transition.

## Audit

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPConcreteBitStringAxiomAudit.lean
lake env lean -DwarningAsError=true lean-audit/PNPConcreteMachineAxiomAudit.lean
node --test audits/lean-concrete-machine0.test.mjs
```

The transcripts cover all 41 explicit bitstring/polynomial declarations and all 38 explicit
machine declarations. Every printed declaration has an empty axiom closure.

## Boundary

This machine-kernel milestone by itself does not define P, NP, reductions, SAT, NP-completeness, or
`P = NP`. The later axiom-free
[finite charged-pipeline complexity interface](./lean_concrete_complexity.md) now defines bitstring
P/NP witnesses, polynomial reductions, and the inactive `PNP.Main.ConcretePEqualsNP` target. Its
finite syntax is grounded at `Machine` leaves, but no compiler/refinement from an arbitrary
composite pipeline to one raw single-tape machine has been proved. The local framed simulator now
lifts every supplied exact `n`-step successful raw execution from an already represented frame to
exactly `3 * n` successful work steps; ordinary compiled `run` with fuel `18 * n` reaches the
encoded endpoint. These factors are not an input-size bound, and the layer supplies no initial
framing, `boundedDecide` or output theorem, output handoff, or composite refinement. Therefore
`Formal.ConcreteComplexityMachineLink` remains the first of seven blockers. All five
reviewed activation fingerprints remain unset, the four project-specific axioms remain,
`PNP.Main.p_eq_np` is absent, and the publication gate is false.
