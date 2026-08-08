import PNP.ResidualTerminalFourCornerTightBasisMaximum

set_option maxRecDepth 100000

namespace PNP
namespace DirectWire

def tightMaximumInput0 : Fin 2 := ⟨0, by decide⟩
def tightMaximumInput1 : Fin 2 := ⟨1, by decide⟩
def tightMaximumAmbientInput0 : Fin 3 := ⟨0, by decide⟩
def tightMaximumAmbientInput1 : Fin 3 := ⟨1, by decide⟩
def tightMaximumGate0 : Fin 1 := ⟨0, by decide⟩

def tightMaximumProgram : Program 2 1 :=
  .snoc .empty
    { left := .input tightMaximumInput0
      right := .input tightMaximumInput1 }

def tightMaximumWord : DirectWireWord 2 1 1 :=
  ⟨fun _output => .gate tightMaximumGate0⟩

def tightMaximumCandidate : Candidate 2 1 1 :=
  Candidate.ofDirectWireWord tightMaximumProgram tightMaximumWord

def tightMaximumProfileSystem : TerminalProfileSystem 2 1 0 :=
  { role := fun coordinate => Fin.elim0 coordinate
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def tightMaximumSaturationSystem : TerminalSaturationSystem 2 1 1 0 :=
  { profileSystem := tightMaximumProfileSystem
    requires := fun _kind _dependent _required => false }

def tightMaximumSquare :
    TerminalSaturatedSupportSquare tightMaximumSaturationSystem :=
  terminalSaturatedSupportSquare tightMaximumSaturationSystem
    [.gate tightMaximumGate0] [.gate tightMaximumGate0]

def tightMaximumProjection : TerminalProfileProjection 0 :=
  { keep := fun coordinate => Fin.elim0 coordinate }

def tightMaximumCarrier :
    TerminalFourCornerCarrier tightMaximumSaturationSystem :=
  tightMaximumSquare.fourCornerCarrier tightMaximumCandidate
    tightMaximumProjection

def tightMaximumObserver
    (_implementation : Implementation 3 1) : TerminalProfile 0 :=
  fun coordinate => Fin.elim0 coordinate

def tightMaximumSwappedProgram : Program 3 1 :=
  .snoc .empty
    { left := .input tightMaximumAmbientInput1
      right := .input tightMaximumAmbientInput0 }

def tightMaximumSwappedWord : DirectWireWord 3 1 1 :=
  ⟨fun _output => .gate tightMaximumGate0⟩

def tightMaximumSwappedImplementation : Implementation 3 1 :=
  ⟨1, Candidate.ofDirectWireWord tightMaximumSwappedProgram
    tightMaximumSwappedWord⟩

def tightMaximumSwappedBasis :
    TerminalFourCornerImplementationBasis 3 1 :=
  { meet := tightMaximumSwappedImplementation
    left := tightMaximumSwappedImplementation
    right := tightMaximumSwappedImplementation
    join := tightMaximumSwappedImplementation }

example (mode : TerminalOptimumCoherenceMode)
    (corner : TerminalSupportSquareCorner) :
    (mode.minimumSizes
      (tightMaximumCarrier.optimizationCorners tightMaximumObserver)).at corner ≤
      ((tightMaximumCarrier.optimizationCorners tightMaximumObserver).at
        corner).gateCount :=
  mode.minimumAt_le_current
    (tightMaximumCarrier.optimizationCorners tightMaximumObserver) corner

example (mode : TerminalOptimumCoherenceMode)
    (corner : TerminalSupportSquareCorner)
    (implementation : Implementation 3 1) :
    implementation ∈
        (tightMaximumCarrier.optimizationCorners
          tightMaximumObserver).minimumImplementationsAt mode corner ↔
      mode.profileMatchBool
          (tightMaximumCarrier.optimizationCorners tightMaximumObserver)
          corner implementation = true ∧
        implementation.gateCount =
          (mode.minimumSizes
            (tightMaximumCarrier.optimizationCorners
              tightMaximumObserver)).at corner :=
  TerminalProjectionFourCorners.mem_minimumImplementationsAt_iff
    (tightMaximumCarrier.optimizationCorners tightMaximumObserver)
    mode corner implementation

example : tightMaximumSwappedBasis.IsTightCoherent tightMaximumCarrier
    tightMaximumObserver .full :=
  (tightMaximumCarrier.tightBasisBool_eq_true_iff
    tightMaximumObserver .full tightMaximumSwappedBasis).1 (by decide)

example : tightMaximumSwappedBasis.IsTightCoherent tightMaximumCarrier
    tightMaximumObserver .quotient :=
  (tightMaximumCarrier.tightBasisBool_eq_true_iff
    tightMaximumObserver .quotient tightMaximumSwappedBasis).1 (by decide)

example : tightMaximumCarrier.firstBasisCoherenceFailure?
    tightMaximumObserver .full tightMaximumSwappedBasis.at = none := by decide

example : tightMaximumSwappedBasis ∈
    tightMaximumCarrier.tightBasisFamily tightMaximumObserver .full :=
  tightMaximumCarrier.mem_tightBasisFamily_complete
    tightMaximumObserver .full tightMaximumSwappedBasis
      ((tightMaximumCarrier.tightBasisBool_eq_true_iff
        tightMaximumObserver .full tightMaximumSwappedBasis).1 (by decide))

example : tightMaximumSwappedBasis ∈
    tightMaximumCarrier.tightBasisFamily tightMaximumObserver .quotient :=
  tightMaximumCarrier.mem_tightBasisFamily_complete
    tightMaximumObserver .quotient tightMaximumSwappedBasis
      ((tightMaximumCarrier.tightBasisBool_eq_true_iff
        tightMaximumObserver .quotient tightMaximumSwappedBasis).1
          (by decide))

example : tightMaximumCarrier.NoOptimumCoherenceRoutes
    tightMaximumObserver := by
  constructor <;>
    change tightMaximumCarrier.firstOptimumCoherenceFailure?
      tightMaximumObserver _ = none <;> decide

example : tightMaximumCarrier.canonicalImplementationBasis
      tightMaximumObserver .full ∈
    tightMaximumCarrier.tightBasisFamily tightMaximumObserver .full :=
  tightMaximumCarrier.canonicalImplementationBasis_mem_tightFamily
    tightMaximumObserver .full (by
      change tightMaximumCarrier.firstOptimumCoherenceFailure?
        tightMaximumObserver .full = none
      decide)

example : tightMaximumCarrier.tightBasisMaximum?
      tightMaximumObserver .full =
    some (tightMaximumCarrier.optimizationCorners
      tightMaximumObserver).fullDelta :=
  tightMaximumCarrier.tightBasisMaximum?_full tightMaximumObserver (by
    change tightMaximumCarrier.firstOptimumCoherenceFailure?
      tightMaximumObserver .full = none
    decide)

example : tightMaximumCarrier.tightBasisMaximum?
      tightMaximumObserver .quotient =
    some (tightMaximumCarrier.optimizationCorners
      tightMaximumObserver).quotientDelta :=
  tightMaximumCarrier.tightBasisMaximum?_quotient tightMaximumObserver (by
    change tightMaximumCarrier.firstOptimumCoherenceFailure?
      tightMaximumObserver .quotient = none
    decide)

example : signedMaximum? [-5, -2, -9] = some (-2) := by decide

example : signedMaximum? ([] : List Int) = none := rfl

end DirectWire
end PNP
