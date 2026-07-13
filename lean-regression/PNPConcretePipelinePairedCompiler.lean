import PNP

namespace PNP.Concrete.PipelinePairedCompilerRegression

open PipelinePairedCompiler

/-- Empty canonical pairs traverse the complete compiled accepting pipeline. -/
example :
    boundedDecide (pairedPipelineMachine acceptAllPolynomialTime.machine)
        ((pairedPipelineRawTimeBound acceptAllPolynomialTime.timeBound).eval
          (BitString.size (BitString.pair [] [])))
        (BitString.pair [] []) = .accept := by
  rw [pairedPipeline_boundedDecide_eq acceptAllPolynomialTime [] []]
  rfl

/-- A rejecting target remains rejected for a nonempty, mixed canonical pair. -/
example :
    boundedDecide (pairedPipelineMachine rejectAllPolynomialTime.machine)
        ((pairedPipelineRawTimeBound rejectAllPolynomialTime.timeBound).eval
          (BitString.size
            (BitString.pair [false, true, false] [true, true])))
        (BitString.pair [false, true, false] [true, true]) = .reject := by
  rw [pairedPipeline_boundedDecide_eq rejectAllPolynomialTime
    [false, true, false] [true, true]]
  rfl

/-- Terminal packing preserves every bit of a canonical pair, including odd
and even component lengths, for the zero-step identity-output target. -/
example (left right : BitString) :
    machineOutput (pairedPipelineMachine acceptAllPolynomialTime.machine)
        ((pairedPipelineRawTimeBound acceptAllPolynomialTime.timeBound).eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) = BitString.pair left right := by
  rw [pairedPipeline_machineOutput_eq acceptAllPolynomialTime left right]
  exact machineOutput_immediateAccept_zero (BitString.pair left right)

end PNP.Concrete.PipelinePairedCompilerRegression
