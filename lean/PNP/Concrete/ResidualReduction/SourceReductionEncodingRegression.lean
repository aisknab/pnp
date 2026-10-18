import PNP.Concrete.ResidualReduction.SourceReductionInputEncoding

namespace PNP.Concrete.ResidualReduction.SourceEncoding.Regression
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

example : (pointCodec 3).decode [true, false, true] = some (true, false, true, ()) := rfl
example : (pointCodec 3).decode [true, false] = none := rfl
example : (pointCodec 2).decode [true, false, true] = none := rfl
example : (affineCodec 2).encode (true, false, true) = [true, false, true] := rfl
example : dataCodec.decode [] = none := rfl
example : dataCodec.decode [false, false] = none := rfl
example : dataCodec.decode [false, false, false] = some ⟨0, [], []⟩ := rfl
example : dataCodec.decode [false, false, false, true] = none := rfl

private def mismatched : StepRecord := ⟨0, [], ⟨(), 0, (), []⟩⟩

example : liftHistory 0 0 [mismatched] () = none := rfl
example : projectHistory 0 0 [mismatched] () = none := rfl
example : recoverBytes 0 [false, false, false] [true] = none := rfl
example : recoverBytes 0 [false, false, false] [] = some [] := rfl

/-- Syntactic encoding does not turn an unknown residual into a SAT verdict. -/
example (n : Nat) (F : Family (n + 1)) : zeroVerdict (n + 1) F = none := rfl

example (n : Nat) (F : Family n) :
    dataCodec.decode (dataCodec.encode (toData (reduce n F))) = some (toData (reduce n F)) :=
  data_roundtrip _

example (n : Nat) (F : Family n) : Replays (reduce n F) := reduce_replays n F

example (n : Nat) (F : Family n) :
    (dataCodec.encode (toData (reduce n F))).length ≤ dataBound n F.length :=
  reduce_encoded_bound n F

example (input : BitString) :
    (sourceEncode input).length ≤ sourceOutputPolynomial.eval input.length :=
  source_encoded_bound input

example : encodeNativePacket .malformed = [false] := rfl

end PNP.Concrete.ResidualReduction.SourceEncoding.Regression
