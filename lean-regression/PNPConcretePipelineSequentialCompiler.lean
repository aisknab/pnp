import PNP

namespace PNP.Concrete.PipelineSequentialCompilerRegression

open PipelineSequentialCompiler

/-- Empty input completes two accepting raw machines in the literal combined
table. -/
example :
    boundedDecide
        (sequentialMachine acceptAllPolynomialTime.machine
          acceptAllPolynomialTime.machine)
        ((sequentialRawTimeBound acceptAllPolynomialTime.timeBound
          acceptAllPolynomialTime.timeBound).eval (BitString.size [])) [] =
      .accept := by
  rw [sequential_boundedDecide_eq acceptAllPolynomialTime
    acceptAllPolynomialTime []]
  rfl

/-- The first verdict does not decide the composition: rejection by the first
machine still passes its output to an accepting second machine. -/
example (bit : Bool) :
    boundedDecide
        (sequentialMachine rejectAllPolynomialTime.machine
          acceptAllPolynomialTime.machine)
        ((sequentialRawTimeBound rejectAllPolynomialTime.timeBound
          acceptAllPolynomialTime.timeBound).eval (BitString.size [bit]))
        [bit] = .accept := by
  rw [sequential_boundedDecide_eq rejectAllPolynomialTime
    acceptAllPolynomialTime [bit]]
  rfl

/-- Conversely, the second verdict is final. -/
example (input : BitString) :
    boundedDecide
        (sequentialMachine acceptAllPolynomialTime.machine
          rejectAllPolynomialTime.machine)
        ((sequentialRawTimeBound acceptAllPolynomialTime.timeBound
          rejectAllPolynomialTime.timeBound).eval (BitString.size input))
        input = .reject := by
  rw [sequential_boundedDecide_eq acceptAllPolynomialTime
    rejectAllPolynomialTime input]
  rfl

/-- Empty, odd, even, and otherwise arbitrary raw words survive both
zero-step identity-output machines exactly. -/
example (input : BitString) :
    machineOutput
        (sequentialMachine acceptAllPolynomialTime.machine
          acceptAllPolynomialTime.machine)
        ((sequentialRawTimeBound acceptAllPolynomialTime.timeBound
          acceptAllPolynomialTime.timeBound).eval (BitString.size input))
        input = input := by
  rw [sequential_machineOutput_eq acceptAllPolynomialTime
    acceptAllPolynomialTime input]
  change machineOutput immediateAcceptMachine 0
      (machineOutput immediateAcceptMachine 0 input) = input
  rw [machineOutput_immediateAccept_zero]
  exact machineOutput_immediateAccept_zero input

/-- A stuck nonhalting first endpoint remains timeout before any second-stage
launch. -/
example :
    workBoundedDecide
        (PipelineSequentialStateNamespace.sequentialWorkMachine stuckMachine
          acceptAllPolynomialTime.machine)
        (PipelineCompiler.simulationPrefixWorkSteps [true] 0)
        (rawInputWorkTape [true]) = .timeout := by
  exact sequential_timeout_of_stuck_first_rawRunExact
    stuckMachine acceptAllPolynomialTime.machine 0 [true]
    (startConfig stuckMachine [true]) rfl rfl rfl

end PNP.Concrete.PipelineSequentialCompilerRegression
