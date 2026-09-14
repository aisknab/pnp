import PNP.ResidualTerminalFourCornerOpenTransport

namespace PNP.DirectWire

-- Exact general interfaces: neither the valuation nor the square is a fixture.
section ExactInterfaces
variable {inputs gates outputs profileWidth : Nat}
variable {system : TerminalSaturationSystem inputs gates outputs profileWidth}
variable (carrier : TerminalFourCornerCarrier system)

example (transport : TerminalOptimumLegTransport carrier) (gate : Fin gates)
    (selected : terminalGateSelected
      (carrier.square.records transport.leg.source) gate = true) :
    terminalGateSelected (carrier.square.records transport.leg.target) gate = true :=
  transport.selectedGateTransport gate selected

example (valuation : Valuation (carrier.extracted .join).boundary.length) :
    (carrier.optimumLegTransport .meetLeft).boundaryPullback
        ((carrier.optimumLegTransport .leftJoin).boundaryPullback valuation) =
      terminalBoundaryPullback carrier.candidate
        (carrier.square.records .meet) (carrier.square.records .join) valuation :=
  carrier.boundaryPullback_meet_join_left valuation

example (valuation : Valuation (carrier.extracted .join).boundary.length) :
    (carrier.optimumLegTransport .meetRight).boundaryPullback
        ((carrier.optimumLegTransport .rightJoin).boundaryPullback valuation) =
      terminalBoundaryPullback carrier.candidate
        (carrier.square.records .meet) (carrier.square.records .join) valuation :=
  carrier.boundaryPullback_meet_join_right valuation

example (valuation : Valuation (carrier.extracted .join).boundary.length) :
    (carrier.optimumLegTransport .meetLeft).boundaryPullback
        ((carrier.optimumLegTransport .leftJoin).boundaryPullback valuation) =
      (carrier.optimumLegTransport .meetRight).boundaryPullback
        ((carrier.optimumLegTransport .rightJoin).boundaryPullback valuation) :=
  carrier.boundaryPullback_square valuation

example (transport : TerminalOptimumLegTransport carrier)
    (valuation : Valuation (carrier.extracted transport.leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted transport.leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted transport.leg.target).interface.length)
    (retained : transport.retainedOutput? sourceIndex = some targetIndex) :
    (carrier.cornerImplementation transport.leg.source).candidate.semantics
        (transport.boundaryPullback valuation) sourceIndex =
      (carrier.cornerImplementation transport.leg.target).candidate.semantics
        valuation targetIndex :=
  transport.extracted_retained_semantics valuation sourceIndex targetIndex retained

example (transport : TerminalOptimumLegTransport carrier)
    (sourceRealization : TerminalFullRealization
      (carrier.cornerImplementation transport.leg.source))
    (targetRealization : TerminalFullRealization
      (carrier.cornerImplementation transport.leg.target))
    (valuation : Valuation (carrier.extracted transport.leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted transport.leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted transport.leg.target).interface.length)
    (retained : transport.retainedOutput? sourceIndex = some targetIndex) :
    sourceRealization.implementation.candidate.semantics
        (transport.boundaryPullback valuation) sourceIndex =
      targetRealization.implementation.candidate.semantics valuation targetIndex :=
  transport.realization_retained_semantics sourceRealization targetRealization
    valuation sourceIndex targetIndex retained

example (observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth)
    (family : TerminalFourCornerOptimumFamily carrier observe)
    (leg : TerminalOptimumSquareLeg)
    (valuation : Valuation (carrier.extracted leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted leg.target).interface.length)
    (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex =
      some targetIndex) :
    (family.fullLocalRealization leg.source).implementation.candidate.semantics
        ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex =
      (family.fullLocalRealization leg.target).implementation.candidate.semantics
        valuation targetIndex :=
  family.full_retained_semantics leg valuation sourceIndex targetIndex retained

example (observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth)
    (family : TerminalFourCornerOptimumFamily carrier observe)
    (leg : TerminalOptimumSquareLeg)
    (valuation : Valuation (carrier.extracted leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted leg.target).interface.length)
    (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex =
      some targetIndex) :
    (family.quotientLocalRealization leg.source).implementation.candidate.semantics
        ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex =
      (family.quotientLocalRealization leg.target).implementation.candidate.semantics
        valuation targetIndex :=
  family.quotient_retained_semantics leg valuation sourceIndex targetIndex retained

example (observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth)
    (leg : TerminalOptimumSquareLeg)
    (valuation : Valuation (carrier.extracted leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted leg.target).interface.length)
    (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex =
      some targetIndex) :
    ((carrier.canonicalOptimumFamily observe).fullLocalRealization leg.source).implementation.candidate.semantics
        ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex =
      ((carrier.canonicalOptimumFamily observe).fullLocalRealization leg.target).implementation.candidate.semantics
        valuation targetIndex :=
  carrier.canonicalFull_retained_semantics observe leg valuation sourceIndex targetIndex retained

example (observe : Implementation (inputs + gates) gates -> TerminalProfile profileWidth)
    (leg : TerminalOptimumSquareLeg)
    (valuation : Valuation (carrier.extracted leg.target).boundary.length)
    (sourceIndex : Fin (carrier.extracted leg.source).interface.length)
    (targetIndex : Fin (carrier.extracted leg.target).interface.length)
    (retained : (carrier.optimumLegTransport leg).retainedOutput? sourceIndex =
      some targetIndex) :
    ((carrier.canonicalOptimumFamily observe).quotientLocalRealization leg.source).implementation.candidate.semantics
        ((carrier.optimumLegTransport leg).boundaryPullback valuation) sourceIndex =
      ((carrier.canonicalOptimumFamily observe).quotientLocalRealization leg.target).implementation.candidate.semantics
        valuation targetIndex :=
  carrier.canonicalQuotient_retained_semantics observe leg valuation sourceIndex targetIndex retained

end ExactInterfaces

namespace FourCornerOpenTransport.Regression

abbrev Record := TerminalPrimitiveRecord 2 4 2 1

def gate0 : Fin 4 := ⟨0, by decide⟩
def gate1 : Fin 4 := ⟨1, by decide⟩
def gate2 : Fin 4 := ⟨2, by decide⟩
def gate3 : Fin 4 := ⟨3, by decide⟩

-- Independently hand-computed circuit: g0 = not x, g1 = true, g2 = x,
-- g3 = not x. Constants, repeated consumers and two outputs remain explicit.
def prefix0 : Program 2 1 :=
  (.empty : Program 2 0).snoc ⟨.input 0, .constant true⟩
def prefix1 : Program 2 2 :=
  prefix0.snoc ⟨.input 1, .constant false⟩
def prefix2 : Program 2 3 :=
  prefix1.snoc ⟨.gate ⟨0, by decide⟩, .gate ⟨1, by decide⟩⟩
def program : Program 2 4 :=
  prefix2.snoc ⟨.gate ⟨2, by decide⟩, .input 0⟩
def candidate : Candidate 2 4 2 :=
  Candidate.ofDirectWireWord program
    ⟨fun output => if output.val = 0 then .gate gate0 else .gate gate2⟩

def small : List Record := [.gate gate2]
def left : List Record := [.gate gate0, .gate gate2]
def right : List Record := [.gate gate1, .gate gate2]
def large : List Record := [.gate gate0, .gate gate1, .gate gate2]

def system : TerminalSaturationSystem 2 4 2 1 :=
  { profileSystem :=
      { role := fun _ => .origin
        observe := fun _ _ => false }
    requires := fun _ _ _ => false }
def carrier : TerminalFourCornerCarrier system :=
  (terminalSaturatedSupportSquare system left right).fourCornerCarrier candidate
    { keep := fun _ => true }

def values {width : Nat} (valuation : Valuation width) : List Bool :=
  (allFin width).map valuation

def assignment (x y : Bool) :
    Valuation (terminalBoundaryPorts program large).length :=
  fun index => if index.val = 0 then x else y

def check (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError (name ++ ": open transport regression failed"))
  IO.println ("M261_FIXTURE_GREEN=" ++ name)

-- Only these tiny declared dimensions are evaluated. Canonical exhaustive
-- minimum realizers are checked through the universal types above, not run.
#eval (show IO Unit from do
  check "empty-selected-support"
    (values (terminalBoundaryPullback candidate ([] : List Record) large
      (assignment true false)) == [])
  check "exact-small-boundary"
    ((terminalBoundaryPorts program small).map TerminalSupportWire.orderCode == [2, 3])
  check "retained-primary-and-external-gate"
    ((terminalBoundaryPorts program left).map TerminalSupportWire.orderCode == [0, 3])
  check "right-corner-boundary-order"
    ((terminalBoundaryPorts program right).map TerminalSupportWire.orderCode == [1, 2])
  check "join-boundary-only-actual-primary-sources"
    ((terminalBoundaryPorts program large).map TerminalSupportWire.orderCode == [0, 1])
  check "internalized-values-are-computed"
    (values (terminalBoundaryPullback candidate small large (assignment true false))
      == [false, true])
  check "identity-all-four-boundary-valuations"
    ([false, true].all fun x => [false, true].all fun y =>
      values (terminalBoundaryPullback candidate large large (assignment x y))
        == [x, y])
  check "left-nested-substitution-all-valuations"
    ([false, true].all fun x => [false, true].all fun y =>
      values (terminalBoundaryPullback candidate small left
        (terminalBoundaryPullback candidate left large (assignment x y)))
        == [!x, true])
  check "right-nested-substitution-all-valuations"
    ([false, true].all fun x => [false, true].all fun y =>
      values (terminalBoundaryPullback candidate small right
        (terminalBoundaryPullback candidate right large (assignment x y)))
        == [!x, true])
  check "duplicate-unordered-support"
    (values (terminalBoundaryPullback candidate
      ([.gate gate2, .gate gate0, .gate gate2] : List Record) large
      (assignment true false)) == [true, true])
  check "retained-two-output-semantics"
    ([false, true].all fun x => [false, true].all fun y =>
      let valuation := assignment x y
      let pulled := terminalBoundaryPullback candidate left large valuation
      values (terminalOpenSupportSemantics candidate left pulled) == [!x, x] &&
      values (terminalOpenSupportSemantics candidate large valuation) == [!x, x])
  check "computed-square-has-genuine-meet"
    ((terminalSelectedGates (carrier.square.records .meet)).map Fin.val == [2])
  check "computed-square-two-paths"
    ([false, true].all fun x => [false, true].all fun y =>
      let valuation : Valuation (carrier.extracted .join).boundary.length :=
        fun index => if index.val = 0 then x else y
      let leftPath := (carrier.optimumLegTransport .meetLeft).boundaryPullback
        ((carrier.optimumLegTransport .leftJoin).boundaryPullback valuation)
      let rightPath := (carrier.optimumLegTransport .meetRight).boundaryPullback
        ((carrier.optimumLegTransport .rightJoin).boundaryPullback valuation)
      values leftPath == [!x, true] && values rightPath == [!x, true])
  check "internalized-ambient-bit-is-not-free"
    (terminalOpenSupportSemantics candidate small (fun _ => false)
        ⟨0, by decide⟩ == true &&
      terminalOpenSupportSemantics candidate small
        (terminalBoundaryPullback candidate small large (assignment false false))
        ⟨0, by decide⟩ == false)
  check "unconstrained-ambient-comparison-remains-distinct"
    ((carrier.ambientImplementation .meet).candidate.semantics
        (fun _ => false) gate2 == true &&
      (carrier.ambientImplementation .join).candidate.semantics
        (fun _ => false) gate2 == false)
  check "retained-output-producer-order"
    ((carrier.optimumLegTransport .meetLeft).retainedOutput? ⟨0, by decide⟩ ==
      some ⟨1, by decide⟩)
  IO.println "M261_FOUR_CORNER_OPEN_TRANSPORT_RUNTIME_GREEN")

end FourCornerOpenTransport.Regression
end PNP.DirectWire
