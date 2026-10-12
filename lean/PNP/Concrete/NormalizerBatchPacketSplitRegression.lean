import PNP.Concrete.NormalizerBatchPacketSplit

namespace PNP.Concrete.NormalizerBlocks

example (counter : BitString) (r : Occurrence.Registers) :
    Exec BatchPacket.takeLoop ({r with target := counter}).store (BatchPacket.takeResult counter r).fuel
      (BatchPacket.takeResult counter r).state.store := BatchPacket.take_exec counter r
example (counter : BitString) (r : Occurrence.Registers) :
    (BatchPacket.takeResult counter r).fuel ≤ 5 * counter.length + 4 := BatchPacket.take_fuel_bound counter r
example (counter : BitString) (r : Occurrence.Registers) :
    (BatchPacket.takeResult counter r).state.excess.length + (BatchPacket.takeResult counter r).state.input.length ≤
      r.excess.length + r.input.length := BatchPacket.take_size counter r
example (data suffix : BitString) (r : Occurrence.Registers) :
    (BatchPacket.takeResult (List.replicate data.length true) {r with input := data ++ suffix}).state =
      {r with input := suffix, target := [], excess := data.reverse ++ r.excess} := BatchPacket.take_canonical data suffix r

#print axioms BatchPacket.take_exec
#print axioms BatchPacket.take_fuel_bound
#print axioms BatchPacket.take_size
#print axioms BatchPacket.take_canonical

end PNP.Concrete.NormalizerBlocks
