# Concrete Cook–Levin layout boundary

`PNP.Concrete.CookLevinLayout` fixes the finite numeric substrate for the
concrete Cook–Levin construction.  It does not yet construct a tableau CNF or
a polynomial reduction.

The module proves:

- raw runs remain unchanged when a larger fuel budget follows either a
  designated halt or a stuck endpoint;
- a stuck nonhalting endpoint is not reclassified as rejection;
- `machineStateBound` strictly contains every distinguished state and every
  source and target state mentioned in the literal first-match rule table;
- the maximum verifier-input length is `n` in input-only mode and
  `2*n + 2*B(n) + 2` in paired certificate mode;
- the bounded tape window is `L(n) + 2*T(n) + 1`;
- Boolean variables occupy contiguous, non-overlapping blocks for tape
  symbols, head positions, control states, certificate bits, and certificate
  length selectors;
- every exposed coordinate is proved smaller than the formula's declared
  variable count; and
- the elementary at-least-one and pair-exclusion CNF clauses have their
  stated propositional semantics.

The exact state-space and input-size polynomials are executable
`NatPolynomial` terms.  There is no SAT call, host function, certificate
oracle, minimizer, exhaustive circuit enumeration, or new assumption in this
module.

Still missing after this boundary are the transition tableau, formula
soundness and completeness, variable-length certificate equivalence, the
finite emitter and its raw compiler, the polynomial reduction, and
`PNP.Concrete.cnfSATNPComplete`.  CNFSAT in P and `PNP.Main.p_eq_np` remain
absent, and the publication gate remains false.
