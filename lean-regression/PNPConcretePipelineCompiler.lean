import PNP

namespace PNP.Concrete.PipelineCompilerRegression

open PipelineCompiler

/-- Empty raw input traverses the complete accepting pipeline. -/
example :
    boundedDecide (pipelineMachine acceptAllPolynomialTime.machine)
        ((pipelineRawTimeBound acceptAllPolynomialTime.timeBound).eval
          (BitString.size []))
        [] = .accept := by
  rw [pipeline_boundedDecide_eq acceptAllPolynomialTime []]
  rfl

/-- Each one-bit odd input traverses the complete rejecting pipeline. -/
example (bit : Bool) :
    boundedDecide (pipelineMachine rejectAllPolynomialTime.machine)
        ((pipelineRawTimeBound rejectAllPolynomialTime.timeBound).eval
          (BitString.size [bit]))
        [bit] = .reject := by
  rw [pipeline_boundedDecide_eq rejectAllPolynomialTime [bit]]
  rfl

/-- Terminal packing preserves arbitrary empty, odd, even, and non-pair raw
words for the zero-step identity-output target. -/
example (input : BitString) :
    machineOutput (pipelineMachine acceptAllPolynomialTime.machine)
        ((pipelineRawTimeBound acceptAllPolynomialTime.timeBound).eval
          (BitString.size input)) input = input := by
  rw [pipeline_machineOutput_eq acceptAllPolynomialTime input]
  exact machineOutput_immediateAccept_zero input

/-- The all-input theorem specializes to the existing canonical-pair
contract without changing the executable machine. -/
example (left right : BitString) :
    boundedDecide (pipelineMachine acceptAllPolynomialTime.machine)
        ((pipelineRawTimeBound acceptAllPolynomialTime.timeBound).eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) = .accept := by
  rw [pipeline_boundedDecide_eq acceptAllPolynomialTime
    (BitString.pair left right)]
  rfl

/-- A concrete nonhalting target with no applicable rule remains timeout at
the exact all-input simulation prefix. -/
example :
    workBoundedDecide
        (PipelineTerminalBridge.terminalBridgeMachine stuckMachine)
        (simulationPrefixWorkSteps [true] 0)
        (rawInputWorkTape [true]) = .timeout := by
  exact pipeline_timeout_of_stuck_rawRunExact
    stuckMachine 0 [true] (startConfig stuckMachine [true]) rfl rfl rfl

end PNP.Concrete.PipelineCompilerRegression
