import PNP

namespace PNP.Concrete.TapeBlankEquivalenceRegression

/-- Empty raw input and the two-cell work focus differ only by a materialized
right blank. -/
example :
    Tape.BlankEquivalent (Tape.ofInput [])
      (encodeWorkTape (rawInputWorkTape [])) := by
  exact encodeWorkTape_rawInputWorkTape_blankEquivalent []

/-- A one-bit input retains its bit while the work view materializes the
missing second cell. -/
example :
    Tape.BlankEquivalent (Tape.ofInput [true])
      (encodeWorkTape (rawInputWorkTape [true])) := by
  exact encodeWorkTape_rawInputWorkTape_blankEquivalent [true]

/-- Odd inputs preserve every bit rather than treating the padding blank as a
false output bit. -/
example :
    Tape.outputBits (Tape.ofInput [false, true, false]) =
      Tape.outputBits
        (encodeWorkTape (rawInputWorkTape [false, true, false])) := by
  exact Tape.outputBits_eq_of_blankEquivalent
    (encodeWorkTape_rawInputWorkTape_blankEquivalent
      [false, true, false])

/-- Positive even input retains the older exact structural bridge. -/
example (left right : BitString) :
    startConfig (compileWorkMachine PipelineInputFramer.pairedInputFramer)
        (BitString.pair left right) =
      encodeWorkConfiguration
        (workStartConfiguration PipelineInputFramer.pairedInputFramer
          (rawInputWorkTape (BitString.pair left right))) := by
  unfold rawInputWorkTape
  exact startConfig_compileWorkMachine_paired
    PipelineInputFramer.pairedInputFramer left right

end PNP.Concrete.TapeBlankEquivalenceRegression
