# Concrete Cook–Levin complete-width-header machine

`lean/PNP/Concrete/CookLevinBuilderUnaryPolynomial.lean` and
`lean/PNP/Concrete/CookLevinBuilderCompleteHeader.lean` define one literal
finite work machine for the next bounded builder milestone. Starting from an
ordinary raw `BitString`, it runs the already-audited input/first-token prefix,
evaluates the verifier's formula-width polynomial into unary scratch space,
and emits the complete canonical unary-width header.

The endpoint contains exactly

```text
T repeated FormulaWidth times, followed by F
```

so its token-pair encoding is the prefix
`encodedFormula.take (2 * (FormulaWidth + 1))`. This milestone does not
construct the formula body, run the formula cursor, provide a builder
`RawRefinement`, package a polynomial reduction, decide CNF-SAT, or prove
`P = NP`.

## Literal unary polynomial evaluator

The evaluator compiles the inductive `NatPolynomial` syntax into a finite
table of ordinary `WorkRule`s. Each polynomial node owns a fixed state block.
Registers are laid out in postorder and use literal unary cells separated by
markers. Constants append their fixed number of units, the variable copies
the already-framed input tally, addition concatenates unary values, and
multiplication performs a marked repeated-copy loop.

The machine table does not call `NatPolynomial.eval`. Evaluation appears only
in semantic endpoint statements and in proofs that the unary register length
has the intended value. For a polynomial `p`, the public table facts are:

- `ruleCount p = 9 * stateCount p`;
- `rules_length p` proves the generated table has exactly that length;
- `rules_pairwise_query_distinct p` proves deterministic queries;
- `rule_source_lt_acceptState p` separates all rule sources from both halts;
- `workRunExact p input outside output` proves the exact trace and tape;
- `workTimePolynomial_eval p input` identifies the exact work-step count with
  an external `NatPolynomial` evaluated at `input.length`.

Because the verifier fixes `p`, this structurally generated list is still one
finite literal machine for that verifier. No caller-supplied trace,
certificate, minimization result, or SAT result is accepted by the table.

## Header controller and composition

The complete machine places five components in the residue classes modulo
five:

| Component | Global state image |
| --- | --- |
| Existing raw-input/first-token prefix | `5 * state` |
| Unary polynomial evaluator | `5 * state + 1` |
| Sixteen-rule unary-root controller | `5 * state + 2` |
| Reusable `T` appender | `5 * state + 3` |
| Final `F` appender | `5 * state + 4` |

All maps are proved injective and their cross-images are audited as disjoint.
Five nine-symbol-total bridge tables connect the phase endpoints. The global
literal rule count is therefore

```text
45 bridges + 184 prefix + evaluator rules + 16 controller
  + 59 T-appender + 59 F-appender
= 363 + evaluator.ruleCount
```

Only the final `F` appender's accept and reject images are global halts.
Bridge rules come first, and the pairwise query theorem checks the complete
table, including endpoint-source separation, rather than assuming that list
concatenation preserves determinism.

The controller consumes one unit from the evaluated root register. A
remaining unit launches the `T` appender and loops back; consuming the last
unit launches the final `F` appender. Its exact one-decrement trace covers
both the zero-remaining and successor cases, and the composed induction proves
the entire repeated header loop.

## Exact trace and external polynomial fuel

For a verifier problem, the exact work count is

```text
first-token-prefix work
+ 1 bridge into the evaluator
+ exact evaluator work
+ 1 bridge into the controller
+ exact repeated controller/appender loop
```

Let `n` be the raw input length, `W` the exact formula width, and `Q` the
number of evaluator scratch cells through the root separator. The compiled
fuel theorem evaluates the public `rawTimeBound` to

```text
first-token-prefix raw bound
+ 12
+ 6 * exact evaluator work
+ 6 * (W * (2*Q + 4*n + 18 + 2*W) + 2*W + 1).
```

Both `W` and `Q`, and the evaluator runtime itself, are represented by
external `NatPolynomial`s. `rawTimeBound_le` proves that this expression
bounds six times the exact work trace. The compiled theorems then establish
the exact endpoint at both exact fuel and external polynomial fuel, transport
the result to the ordinary blank-equivalent start configuration, and prove
`boundedDecide = .accept` rather than merely `≠ .timeout`.

The negative boundary checks prove that the prefix endpoint times out before
its launch bridge and that removing exactly the last successful work
transition from the full trace also yields timeout.

## Kernel and regression audits

The two complete public declaration surfaces are printed by:

```sh
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderUnaryPolynomialAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteCookLevinBuilderCompleteHeaderAxiomAudit.lean
```

Every declaration closes over only the approved Lean-standard axioms
`propext` and `Quot.sound`; no declaration reaches `Classical.choice`, a
project axiom, `sorryAx`, or an unaudited assumption.

The regression module covers empty, one-bit zero/one, odd-length, even-length,
all-zero, and all-one inputs; exact controller zero/successor traces; concrete
rule and runtime evaluations; state-image separation; final tape
representation; canonical header bits; compiled acceptance; and both timeout
boundaries:

```sh
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderCompleteHeader.lean
node --test \
  audits/lean-concrete-cook-levin-builder-complete-header0.test.mjs
```

The hostile source audit rejects inserted assumptions, a state-map collision,
bridge removal or shadowing, host polynomial evaluation in the executable
table, and altered header-token bits.

## Remaining boundary

This endpoint is the complete answer-independent width header only. A dynamic
cursor, literal/clause emission, the complete formula builder, builder
refinement, the Cook–Levin reduction, CNF-SAT NP-completeness and in-P results,
and the compatibility theorem `PNP.Main.p_eq_np` all remain absent. The four
project assumptions and the publication gate are unchanged.
