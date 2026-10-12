import PNP.Concrete.NormalizerBitLookup
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example : (BitLookup.result {initialRegisters [false,true] with target := [false]}).output = [true] := rfl
example : (BitLookup.result {initialRegisters [true] with target := [true,true]}).output = [false] := rfl
example : (BitLookup.result (initialRegisters [])).output = [false] := rfl
example (r : Registers) : (BitLookup.result r).output.length = 1 := rfl
#print axioms BitLookup.drain_exec
#print axioms BitLookup.emitHead_exec
#print axioms BitLookup.read_exec
#print axioms BitLookup.head_drop
#print axioms BitLookup.result_output
#print axioms BitLookup.result_target
#print axioms BitLookup.canonical
end PNP.Concrete.NormalizerBlocks
