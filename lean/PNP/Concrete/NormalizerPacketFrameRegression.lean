import PNP.Concrete.NormalizerPacketFrame
namespace PNP.Concrete.NormalizerBlocks
open Occurrence
def packetExample (payload count : BitString) : Registers :=
  ⟨[],[],[],count,[],[],[],[],payload⟩
example : (PacketFrame.modelResult (packetExample [] [])).output = [false,false,true,false] := rfl
example : (PacketFrame.modelResult (packetExample [false,true] [])).output =
    [false,false,true,true,true,false,false,true] := rfl
example : (PacketFrame.systemResult (packetExample [true,false] [])).output =
    [false,true,false,false,true,false] := rfl
example : (PacketFrame.systemResult (packetExample [false] [true,false])).output =
    [false,true,false,true,true,false,false] := rfl
#print axioms PacketFrame.tag_exec
#print axioms PacketFrame.count_exec
#print axioms PacketFrame.lengthPrefix_exec
#print axioms PacketFrame.model_exec
#print axioms PacketFrame.model_output
#print axioms PacketFrame.system_exec
#print axioms PacketFrame.system_output
#print axioms PacketFrame.malformed_exec
#print axioms PacketFrame.modelFuel_bound
#print axioms PacketFrame.systemFuel_bound
end PNP.Concrete.NormalizerBlocks
