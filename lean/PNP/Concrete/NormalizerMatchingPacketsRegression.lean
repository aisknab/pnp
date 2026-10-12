import PNP.Concrete.NormalizerMatchingPackets
namespace PNP.Concrete.NormalizerBlocks
open BitRegister
example (r : Occurrence.Registers) : (MatchingPacket.bitsPrepended r).output = r.input ++ r.output := rfl
example (r : Occurrence.Registers) : (MatchingPacket.countPrepended r).output =
    TableInit.encodeCount r.remaining.length r.output := rfl
example (r : Occurrence.Registers) : Exec MatchingPacket.prependBits r.store
    (8 * r.input.length + 7) (MatchingPacket.bitsPrepended r).store := MatchingPacket.prependBits_exec r
#print axioms MatchingPacket.prepareCount_exec
#print axioms MatchingPacket.finishCount_exec
#print axioms MatchingPacket.prependCount_exec
#print axioms MatchingPacket.countPrepended_output
#print axioms MatchingPacket.prepareBits_exec
#print axioms MatchingPacket.reverseFirst_exec
#print axioms MatchingPacket.restoreSuffix_exec
#print axioms MatchingPacket.prependBits_exec
#print axioms MatchingPacket.bitsPrepended_output
end PNP.Concrete.NormalizerBlocks
