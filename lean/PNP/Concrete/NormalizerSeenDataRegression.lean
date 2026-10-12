import PNP.Concrete.NormalizerSeenData
namespace PNP.Concrete.NormalizerBlocks
example : SeenTrace.value [(⟨true, 0⟩, some ⟨false, 7⟩)] = [none] := by decide
example : SeenTrace.value [(⟨false, 2⟩, some ⟨false, 7⟩), (⟨true, 2⟩, none)] = [some 2, none] := by decide
example : SeenTrace.value [(⟨false, 1⟩, none), (⟨false, 1⟩, none)] = [some 1, some 1] := by decide
#print axioms SeenTrace.bytes_cons
#print axioms SeenTrace.encode_bytes
#print axioms SeenTrace.entryBytes_none
#print axioms SeenTrace.entryBytes_some
#print axioms SeenTrace.same_nodes
end PNP.Concrete.NormalizerBlocks
