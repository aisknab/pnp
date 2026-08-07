import PNP.ResidualTerminalFourCornerOptimumCompatibility

namespace PNP
namespace DirectWire

abbrev optimumRecord := TerminalPrimitiveRecord 1 3 1 2

def optimumInput0 : Fin 1 := ⟨0, by decide⟩
def optimumGate0 : Fin 3 := ⟨0, by decide⟩
def optimumGate1 : Fin 3 := ⟨1, by decide⟩
def optimumGate2 : Fin 3 := ⟨2, by decide⟩
def optimumProfile0 : Fin 2 := ⟨0, by decide⟩
def optimumProfile1 : Fin 2 := ⟨1, by decide⟩

def optimumProgram0 : Program 1 1 :=
  .snoc .empty
    { left := .input optimumInput0
      right := .input optimumInput0 }

def optimumProgram1 : Program 1 2 :=
  .snoc optimumProgram0
    { left := .gate ⟨0, by decide⟩
      right := .input optimumInput0 }

def optimumProgram : Program 1 3 :=
  .snoc optimumProgram1
    { left := .gate ⟨1, by decide⟩
      right := .input optimumInput0 }

def optimumWord : DirectWireWord 1 3 1 :=
  ⟨fun _output => .gate optimumGate2⟩

def optimumCandidate : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord optimumProgram optimumWord

def optimumProfileSystem : TerminalProfileSystem 1 1 2 :=
  { role := fun coordinate =>
      if coordinate.val = 0 then .origin else .charge
    observe := fun _implementation _coordinate => false }

def optimumSaturationSystem : TerminalSaturationSystem 1 3 1 2 :=
  { profileSystem := optimumProfileSystem
    requires := fun _kind _dependent _required => false }

def optimumSquare : TerminalSaturatedSupportSquare optimumSaturationSystem :=
  terminalSaturatedSupportSquare optimumSaturationSystem
    [.gate optimumGate0, .profile optimumProfile0]
    [.gate optimumGate1, .profile optimumProfile0, .profile optimumProfile1]

def optimumProjection : TerminalProfileProjection 2 :=
  { keep := fun coordinate => coordinate.val = 0 }

def optimumCarrier : TerminalFourCornerCarrier optimumSaturationSystem :=
  optimumSquare.fourCornerCarrier optimumCandidate optimumProjection

def optimumEmptySquare :
    TerminalSaturatedSupportSquare optimumSaturationSystem :=
  terminalSaturatedSupportSquare optimumSaturationSystem [] []

def optimumEmptyCarrier : TerminalFourCornerCarrier optimumSaturationSystem :=
  optimumEmptySquare.fourCornerCarrier optimumCandidate optimumProjection

def optimumObserve (implementation : Implementation 4 3) : TerminalProfile 2 :=
  fun coordinate =>
    if coordinate.val = 0 then implementation.gateCount == 0
    else implementation.gateCount == 1

example : (optimumCarrier.extracted .meet).boundary.length = 0 := by decide
example : (optimumCarrier.extracted .left).boundary.length = 1 := by decide
example : (optimumCarrier.extracted .right).boundary.length = 2 := by decide
example : (optimumCarrier.extracted .join).boundary.length = 1 := by decide

example : (optimumCarrier.extracted .meet).interface.length = 0 := by decide
example : (optimumCarrier.extracted .left).interface.length = 1 := by decide
example : (optimumCarrier.extracted .right).interface.length = 1 := by decide
example : (optimumCarrier.extracted .join).interface.length = 1 := by decide

example : terminalSupportWireAt
    (TerminalSupportWire.input optimumInput0 :
      TerminalSupportWire 1 3).ambientIndex =
      (TerminalSupportWire.input optimumInput0 :
        TerminalSupportWire 1 3) := by
  exact terminalSupportWireAt_ambientIndex _

example : terminalSupportWireAt
    (TerminalSupportWire.gate optimumGate1 :
      TerminalSupportWire 1 3).ambientIndex =
      (TerminalSupportWire.gate optimumGate1 :
        TerminalSupportWire 1 3) := by
  exact terminalSupportWireAt_ambientIndex _

example : optimumCarrier.boundaryIndex? .right
    (TerminalSupportWire.input optimumInput0).ambientIndex = some ⟨0, by decide⟩ :=
  by decide

example : optimumCarrier.boundaryIndex? .right
    (TerminalSupportWire.gate optimumGate0).ambientIndex = some ⟨1, by decide⟩ :=
  by decide

example : optimumCarrier.boundaryIndex? .right
    (TerminalSupportWire.gate optimumGate2).ambientIndex = none := by decide

example : optimumCarrier.interfaceIndex? .left optimumGate0 =
    some ⟨0, by decide⟩ := by decide

example : optimumCarrier.interfaceIndex? .left optimumGate1 = none := by decide

example (input : Valuation 4) :
    (optimumCarrier.ambientCandidate .left).semantics input optimumGate0 =
      (optimumCarrier.extracted .left).extractedCandidate.semantics
        (fun index => input
          ((optimumCarrier.extracted .left).boundary.get index).ambientIndex)
        ⟨0, by decide⟩ :=
  optimumCarrier.ambientizeCandidate_semantics_present .left
    (optimumCarrier.extracted .left).extractedCandidate input ⟨0, by decide⟩

example (input : Valuation 4) :
    (optimumCarrier.ambientCandidate .left).semantics input optimumGate2 = false :=
  optimumCarrier.ambientizeCandidate_semantics_absent .left
    (optimumCarrier.extracted .left).extractedCandidate input optimumGate2
    (by decide)

example (input : Valuation (optimumCarrier.extracted .right).boundary.length)
    (output : Fin (optimumCarrier.extracted .right).interface.length) :
    (optimumCarrier.localizeCandidate .right
      (optimumCarrier.ambientCandidate .right)).semantics input output =
        (optimumCarrier.extracted .right).extractedCandidate.semantics
          input output :=
  optimumCarrier.localize_ambientize_semantics .right
    (optimumCarrier.extracted .right).extractedCandidate input output

example (corner : TerminalSupportSquareCorner) :
    referenceMinimum (optimumCarrier.ambientImplementation corner) =
      referenceMinimum (optimumCarrier.cornerImplementation corner) :=
  optimumCarrier.ambient_referenceMinimum_eq_corner corner

example : (optimumCarrier.optimizationCorners optimumObserve).system.role
    optimumProfile0 = .origin := by decide

example : (optimumCarrier.optimizationCorners optimumObserve).projection.keep
    optimumProfile0 = true := by decide

example : (optimumCarrier.optimizationCorners optimumObserve).projection.keep
    optimumProfile1 = false := by decide

example : (optimumCarrier.canonicalOptimumFamily optimumObserve).Compatible :=
  optimumCarrier.fourCornerOptimaCarrierCompatible optimumObserve

example (corner : TerminalSupportSquareCorner) :
    ((optimumCarrier.canonicalOptimumFamily optimumObserve).fullLocalRealization
      corner).implementation.gateCount =
        (optimumCarrier.optimizationCorners optimumObserve).fullMinimumSizes.at
          corner :=
  (optimumCarrier.fourCornerOptimaCarrierCompatible optimumObserve).fullLocalMinimum
    corner

example (corner : TerminalSupportSquareCorner) :
    ((optimumCarrier.canonicalOptimumFamily
      optimumObserve).quotientLocalRealization corner).implementation.gateCount =
        (optimumCarrier.optimizationCorners
          optimumObserve).quotientMinimumSizes.at corner :=
  (optimumCarrier.fourCornerOptimaCarrierCompatible
    optimumObserve).quotientLocalMinimum corner

example : (optimumEmptyCarrier.canonicalOptimumFamily optimumObserve).Compatible :=
  optimumEmptyCarrier.fourCornerOptimaCarrierCompatible optimumObserve

example (corner : TerminalSupportSquareCorner) :
    (optimumEmptyCarrier.extracted corner).boundary = [] := by
  cases corner <;> decide

example (corner : TerminalSupportSquareCorner) :
    (optimumEmptyCarrier.extracted corner).interface = [] := by
  cases corner <;> decide

end DirectWire
end PNP
