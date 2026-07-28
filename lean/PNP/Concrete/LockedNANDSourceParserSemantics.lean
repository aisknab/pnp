/-
Copyright (c) 2026 PNP Labs.

Constructive success semantics for the strict locked-NAND source codec.

The literal source parser can check the finite token grammar and the displayed
unary bounds without executing the pure decoder.  This module identifies the
predicate it must recognize: decoding followed by intrinsic elaboration
succeeds exactly when strict circuit decoding produces a well-formed raw
circuit.

This file defines no machine, transition table, runtime bound, reduction, or
complexity-class result.
-/

import PNP.Concrete.LockedNANDReduction

namespace PNP
namespace Concrete
namespace LockedNAND

open DirectWire

/-! ### Constructive elaboration success -/

/-- A raw source elaborates exactly when its input or gate index is in range.
Constants always elaborate. -/
theorem RawSource.elaborate_exists_iff_wellFormed
    (source : RawSource) (inputs priorGates : Nat) :
    (∃ elaborated,
        source.elaborate inputs priorGates = some elaborated) ↔
      source.wellFormed inputs priorGates = true := by
  cases source with
  | input index =>
      constructor
      · rintro ⟨elaborated, hElaborated⟩
        by_cases inRange : index < inputs
        · simp [RawSource.wellFormed, inRange]
        · simp [RawSource.elaborate, inRange] at hElaborated
      · intro wellFormed
        have inRange : index < inputs := by
          simpa [RawSource.wellFormed] using wellFormed
        refine ⟨.input ⟨index, inRange⟩, ?_⟩
        simp [RawSource.elaborate, inRange]
  | constant value =>
      simp [RawSource.elaborate, RawSource.wellFormed]
  | gate index =>
      constructor
      · rintro ⟨elaborated, hElaborated⟩
        by_cases inRange : index < priorGates
        · simp [RawSource.wellFormed, inRange]
        · simp [RawSource.elaborate, inRange] at hElaborated
      · intro wellFormed
        have inRange : index < priorGates := by
          simpa [RawSource.wellFormed] using wellFormed
        refine ⟨.gate ⟨index, inRange⟩, ?_⟩
        simp [RawSource.elaborate, inRange]

/-- A raw NAND gate elaborates exactly when both of its sources are in range
at the same prior-gate coordinate. -/
theorem RawGate.elaborate_exists_iff_wellFormed
    (gate : RawGate) (inputs priorGates : Nat) :
    (∃ elaborated,
        gate.elaborate inputs priorGates = some elaborated) ↔
      gate.wellFormed inputs priorGates = true := by
  cases gate with
  | mk left right =>
      constructor
      · rintro ⟨elaborated, hElaborated⟩
        unfold RawGate.elaborate at hElaborated
        cases hLeft : left.elaborate inputs priorGates with
        | none =>
            rw [hLeft] at hElaborated
            contradiction
        | some typedLeft =>
            cases hRight : right.elaborate inputs priorGates with
            | none =>
                rw [hLeft, hRight] at hElaborated
                contradiction
            | some typedRight =>
                have leftWellFormed :
                    left.wellFormed inputs priorGates = true :=
                  (RawSource.elaborate_exists_iff_wellFormed
                    left inputs priorGates).mp ⟨typedLeft, hLeft⟩
                have rightWellFormed :
                    right.wellFormed inputs priorGates = true :=
                  (RawSource.elaborate_exists_iff_wellFormed
                    right inputs priorGates).mp ⟨typedRight, hRight⟩
                simp [RawGate.wellFormed, leftWellFormed,
                  rightWellFormed]
      · intro gateWellFormed
        have leftWellFormed :
            left.wellFormed inputs priorGates = true := by
          cases hLeft : left.wellFormed inputs priorGates with
          | false =>
              simp [RawGate.wellFormed, hLeft] at gateWellFormed
          | true =>
              rfl
        have rightWellFormed :
            right.wellFormed inputs priorGates = true := by
          simpa [RawGate.wellFormed, leftWellFormed] using gateWellFormed
        rcases
            (RawSource.elaborate_exists_iff_wellFormed
              left inputs priorGates).mpr leftWellFormed with
          ⟨typedLeft, hLeft⟩
        rcases
            (RawSource.elaborate_exists_iff_wellFormed
              right inputs priorGates).mpr rightWellFormed with
          ⟨typedRight, hRight⟩
        refine
          ⟨{ left := typedLeft, right := typedRight }, ?_⟩
        simp [RawGate.elaborate, hLeft, hRight]

/-- Intrinsic elaboration of a raw gate list succeeds exactly when every gate
uses only inputs and earlier gates.  The starting prior-gate count is
arbitrary so the statement composes through `Program.snoc`. -/
theorem elaborateGatesAux_exists_iff_rawGatesWellFormed
    {inputs priorGates : Nat} (program : Program inputs priorGates)
    (gates : List RawGate) :
    (∃ packed, elaborateGatesAux program gates = some packed) ↔
      rawGatesWellFormed inputs priorGates gates = true := by
  induction gates generalizing priorGates with
  | nil =>
      simp [elaborateGatesAux, rawGatesWellFormed]
  | cons gate rest ih =>
      constructor
      · rintro ⟨packed, hPacked⟩
        simp only [elaborateGatesAux] at hPacked
        cases hGate : gate.elaborate inputs priorGates with
        | none =>
            rw [hGate] at hPacked
            contradiction
        | some typedGate =>
            rw [hGate] at hPacked
            have gateWellFormed :
                gate.wellFormed inputs priorGates = true :=
              (RawGate.elaborate_exists_iff_wellFormed
                gate inputs priorGates).mp ⟨typedGate, hGate⟩
            have restWellFormed :
                rawGatesWellFormed inputs (priorGates + 1) rest = true :=
              (ih (.snoc program typedGate)).mp ⟨packed, hPacked⟩
            simp [rawGatesWellFormed, gateWellFormed,
              restWellFormed]
      · intro allWellFormed
        have gateWellFormed :
            gate.wellFormed inputs priorGates = true := by
          cases hGate : gate.wellFormed inputs priorGates with
          | false =>
              simp [rawGatesWellFormed, hGate] at allWellFormed
          | true =>
              rfl
        have restWellFormed :
            rawGatesWellFormed inputs (priorGates + 1) rest = true := by
          simpa [rawGatesWellFormed, gateWellFormed] using allWellFormed
        rcases
            (RawGate.elaborate_exists_iff_wellFormed
              gate inputs priorGates).mpr gateWellFormed with
          ⟨typedGate, hGate⟩
        rcases
            (ih (.snoc program typedGate)).mpr restWellFormed with
          ⟨packed, hPacked⟩
        refine ⟨packed, ?_⟩
        simp [elaborateGatesAux, hGate, hPacked]

/-- Successful gate-list elaboration retains the starting gate coordinate and
adds exactly the number of raw gates. -/
theorem elaborateGatesAux_gateCount_eq
    {inputs priorGates : Nat} (program : Program inputs priorGates)
    (gates : List RawGate) (packed : PackedProgram inputs)
    (hPacked : elaborateGatesAux program gates = some packed) :
    packed.gateCount = priorGates + gates.length := by
  induction gates generalizing priorGates with
  | nil =>
      simp only [elaborateGatesAux] at hPacked
      have packedEq :
          ({ gateCount := priorGates, program := program } :
            PackedProgram inputs) = packed :=
        Option.some.inj hPacked
      rw [← packedEq]
      rfl
  | cons gate rest ih =>
      simp only [elaborateGatesAux] at hPacked
      cases hGate : gate.elaborate inputs priorGates with
      | none =>
          rw [hGate] at hPacked
          contradiction
      | some typedGate =>
          rw [hGate] at hPacked
          have hCount := ih (.snoc program typedGate) hPacked
          simp only [List.length_cons]
          omega

/-- Top-level gate-list elaboration succeeds exactly for a well-formed
topological list beginning at gate coordinate zero. -/
theorem elaborateGates_exists_iff_rawGatesWellFormed
    (inputs : Nat) (gates : List RawGate) :
    (∃ packed, elaborateGates inputs gates = some packed) ↔
      rawGatesWellFormed inputs 0 gates = true := by
  exact elaborateGatesAux_exists_iff_rawGatesWellFormed
    (Program.empty : Program inputs 0) gates

/-- The existential gate count returned by top-level elaboration is the raw
list length. -/
theorem elaborateGates_gateCount_eq_length
    (inputs : Nat) (gates : List RawGate)
    (packed : PackedProgram inputs)
    (hPacked : elaborateGates inputs gates = some packed) :
    packed.gateCount = gates.length := by
  have hCount := elaborateGatesAux_gateCount_eq
    (Program.empty : Program inputs 0) gates packed hPacked
  simpa using hCount

/-! ### Normalization preserves the raw validity predicate -/

/-- Topological gate validity composes over concatenation, with the second
list starting after every gate in the first list. -/
theorem rawGatesWellFormed_append
    (inputs priorGates : Nat) (first second : List RawGate) :
    rawGatesWellFormed inputs priorGates (first ++ second) =
      (rawGatesWellFormed inputs priorGates first &&
        rawGatesWellFormed inputs (priorGates + first.length) second) := by
  induction first generalizing priorGates with
  | nil =>
      simp [rawGatesWellFormed]
  | cons gate rest ih =>
      simp only [List.cons_append, List.length_cons, rawGatesWellFormed]
      rw [ih]
      have coordinateEq :
          priorGates + 1 + rest.length =
            priorGates + Nat.succ rest.length := by
        omega
      rw [coordinateEq]
      cases gate.wellFormed inputs priorGates <;>
        cases rawGatesWellFormed inputs (priorGates + 1) rest <;>
        cases rawGatesWellFormed inputs
          (priorGates + Nat.succ rest.length) second <;>
        rfl

/-- The legacy output normalization adds only the gates needed to turn an
input or constant output into a final gate.  It neither admits nor rejects a
raw circuit that the original boundary predicate classified differently. -/
theorem RawCircuit.normalize_wellFormed (raw : RawCircuit) :
    raw.normalize.wellFormed = raw.wellFormed := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          rfl
      | input index =>
          by_cases valid : index < inputs
          · simp [RawCircuit.normalize, RawCircuit.wellFormed,
              rawGatesWellFormed_append, rawGatesWellFormed,
              RawGate.wellFormed, RawSource.wellFormed, valid]
          · simp [RawCircuit.normalize, RawCircuit.wellFormed,
              rawGatesWellFormed_append, rawGatesWellFormed,
              RawGate.wellFormed, RawSource.wellFormed, valid]
      | constant value =>
          cases value <;>
            simp [RawCircuit.normalize, RawCircuit.wellFormed,
              rawGatesWellFormed_append, rawGatesWellFormed,
              RawGate.wellFormed, RawSource.wellFormed]

/-- Every normalized raw circuit has an actual gate as its output source. -/
theorem RawCircuit.normalize_output_eq_gate (raw : RawCircuit) :
    ∃ index, raw.normalize.output = .gate index := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          exact ⟨index, rfl⟩
      | input index =>
          exact ⟨gates.length + 1, rfl⟩
      | constant value =>
          cases value <;> exact ⟨gates.length, rfl⟩

/-! ### Circuit and external decoder success -/

private theorem RawCircuit.elaborate_exists_iff_wellFormed_of_output_gate
    (raw : RawCircuit) (index : Nat)
    (hOutput : raw.output = .gate index) :
    (∃ packed, raw.elaborate = some packed) ↔
      raw.wellFormed = true := by
  cases raw with
  | mk inputs gates output =>
      cases hOutput
      cases hGates : elaborateGates inputs gates with
      | none =>
          have gatesNotWellFormed :
              rawGatesWellFormed inputs 0 gates = false := by
            cases hWellFormed :
                rawGatesWellFormed inputs 0 gates with
            | false =>
                rfl
            | true =>
                rcases
                    (elaborateGates_exists_iff_rawGatesWellFormed
                      inputs gates).mpr hWellFormed with
                  ⟨packed, hPacked⟩
                rw [hGates] at hPacked
                contradiction
          simp [RawCircuit.elaborate, RawCircuit.normalize, hGates,
            RawCircuit.wellFormed, gatesNotWellFormed]
      | some packedProgram =>
          have gatesWellFormed :
              rawGatesWellFormed inputs 0 gates = true :=
            (elaborateGates_exists_iff_rawGatesWellFormed
              inputs gates).mp ⟨packedProgram, hGates⟩
          have gateCountEq :
              packedProgram.gateCount = gates.length :=
            elaborateGates_gateCount_eq_length inputs gates
              packedProgram hGates
          by_cases outputInRange : index < gates.length
          · simp [RawCircuit.elaborate, RawCircuit.normalize, hGates,
              RawCircuit.wellFormed, RawSource.elaborate,
              RawSource.wellFormed,
              gatesWellFormed, gateCountEq, outputInRange]
          · simp [RawCircuit.elaborate, RawCircuit.normalize, hGates,
              RawCircuit.wellFormed, RawSource.elaborate,
              RawSource.wellFormed,
              gatesWellFormed, gateCountEq, outputInRange]

/-- Intrinsic circuit elaboration succeeds exactly for the raw
topological/input/output bounds.  Output normalization is accounted for
constructively rather than treated as an additional parser rule. -/
theorem RawCircuit.elaborate_exists_iff_wellFormed
    (raw : RawCircuit) :
    (∃ packed, raw.elaborate = some packed) ↔
      raw.wellFormed = true := by
  rcases raw.normalize_output_eq_gate with ⟨index, hOutput⟩
  have normalized :=
    RawCircuit.elaborate_exists_iff_wellFormed_of_output_gate
      raw.normalize index hOutput
  rw [RawCircuit.elaborate_normalize,
    RawCircuit.normalize_wellFormed] at normalized
  exact normalized

/-! ### Canonical reconstruction from strict decoders -/

private theorem Token.bits_eq_of_ofBits_eq_some
    (a b c d : Bool) (token : Token)
    (hToken : Token.ofBits a b c d = some token) :
    token.bits = [a, b, c, d] := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases token <;> first | rfl | contradiction

private theorem encodeTokens_eq_of_decodeTokens_eq_some
    (bits : BitString) (tokens : List Token)
    (hDecoded : decodeTokens bits = some tokens) :
    encodeTokens tokens = bits := by
  induction tokens generalizing bits with
  | nil =>
      cases bits with
      | nil =>
          rfl
      | cons a afterA =>
          cases afterA with
          | nil =>
              simp [decodeTokens] at hDecoded
          | cons b afterB =>
              cases afterB with
              | nil =>
                  simp [decodeTokens] at hDecoded
              | cons c afterC =>
                  cases afterC with
                  | nil =>
                      simp [decodeTokens] at hDecoded
                  | cons d rest =>
                      simp only [decodeTokens] at hDecoded
                      cases hToken : Token.ofBits a b c d with
                      | none =>
                          rw [hToken] at hDecoded
                          contradiction
                      | some token =>
                          cases hRest : decodeTokens rest with
                          | none =>
                              rw [hToken, hRest] at hDecoded
                              contradiction
                          | some decodedRest =>
                              rw [hToken, hRest] at hDecoded
                              have impossible :
                                  token :: decodedRest = [] :=
                                Option.some.inj hDecoded
                              contradiction
  | cons token rest ih =>
      cases bits with
      | nil =>
          simp [decodeTokens] at hDecoded
      | cons a afterA =>
          cases afterA with
          | nil =>
              contradiction
          | cons b afterB =>
              cases afterB with
              | nil =>
                  contradiction
              | cons c afterC =>
                  cases afterC with
                  | nil =>
                      contradiction
                  | cons d suffix =>
                      simp only [decodeTokens] at hDecoded
                      cases hToken : Token.ofBits a b c d with
                      | none =>
                          rw [hToken] at hDecoded
                          contradiction
                      | some decodedToken =>
                          cases hSuffix : decodeTokens suffix with
                          | none =>
                              rw [hToken, hSuffix] at hDecoded
                              contradiction
                          | some decodedRest =>
                              rw [hToken, hSuffix] at hDecoded
                              have decodedEq :
                                  decodedToken :: decodedRest =
                                    token :: rest :=
                                Option.some.inj hDecoded
                              have tokenEq : decodedToken = token :=
                                List.cons.inj decodedEq |>.1
                              have restEq : decodedRest = rest :=
                                List.cons.inj decodedEq |>.2
                              subst decodedToken
                              subst decodedRest
                              have tokenBits :=
                                Token.bits_eq_of_ofBits_eq_some
                                  a b c d token hToken
                              have suffixBits := ih suffix hSuffix
                              simp only [encodeTokens]
                              rw [tokenBits, suffixBits]
                              rfl

private theorem encodeNatTokens_append_eq_of_decodeNatTokens_eq_some
    (tokens : List Token) (value : Nat) (suffix : List Token)
    (hDecoded : decodeNatTokens tokens = some (value, suffix)) :
    encodeNatTokens value ++ suffix = tokens := by
  induction tokens generalizing value suffix with
  | nil =>
      contradiction
  | cons token rest ih =>
      cases token <;> simp only [decodeNatTokens] at hDecoded
      case unit =>
        cases hRest : decodeNatTokens rest with
        | none =>
            rw [hRest] at hDecoded
            contradiction
        | some decoded =>
            rcases decoded with ⟨decodedValue, decodedSuffix⟩
            rw [hRest] at hDecoded
            have decodedEq :
                (decodedValue + 1, decodedSuffix) = (value, suffix) :=
              Option.some.inj hDecoded
            have valueEq : decodedValue + 1 = value :=
              congrArg Prod.fst decodedEq
            have suffixEq : decodedSuffix = suffix :=
              congrArg Prod.snd decodedEq
            subst value
            subst suffix
            have hTail := ih decodedValue decodedSuffix hRest
            simp only [encodeNatTokens, List.cons_append]
            exact congrArg (List.cons Token.unit) hTail
      case natEnd =>
        have decodedEq : (0, rest) = (value, suffix) :=
          Option.some.inj hDecoded
        have valueEq : 0 = value := congrArg Prod.fst decodedEq
        have suffixEq : rest = suffix := congrArg Prod.snd decodedEq
        subst value
        subst suffix
        rfl
      all_goals contradiction

private theorem encodeSourceTokens_append_eq_of_decodeSourceTokens_eq_some
    (tokens : List Token) (source : RawSource) (suffix : List Token)
    (hDecoded : decodeSourceTokens tokens = some (source, suffix)) :
    encodeSourceTokens source ++ suffix = tokens := by
  cases tokens with
  | nil =>
      contradiction
  | cons token rest =>
      cases token <;> simp only [decodeSourceTokens] at hDecoded
      case input =>
        cases hNat : decodeNatTokens rest with
        | none =>
            rw [hNat] at hDecoded
            contradiction
        | some decoded =>
            rcases decoded with ⟨index, decodedSuffix⟩
            rw [hNat] at hDecoded
            have decodedEq :
                (RawSource.input index, decodedSuffix) = (source, suffix) :=
              Option.some.inj hDecoded
            have sourceEq : RawSource.input index = source :=
              congrArg Prod.fst decodedEq
            have suffixEq : decodedSuffix = suffix :=
              congrArg Prod.snd decodedEq
            subst source
            subst suffix
            have hNatCanonical :=
              encodeNatTokens_append_eq_of_decodeNatTokens_eq_some
                rest index decodedSuffix hNat
            simp only [encodeSourceTokens, List.cons_append]
            exact congrArg (List.cons Token.input) hNatCanonical
      case constantFalse =>
        have decodedEq :
            (RawSource.constant false, rest) = (source, suffix) :=
          Option.some.inj hDecoded
        cases decodedEq
        rfl
      case constantTrue =>
        have decodedEq :
            (RawSource.constant true, rest) = (source, suffix) :=
          Option.some.inj hDecoded
        cases decodedEq
        rfl
      case gate =>
        cases hNat : decodeNatTokens rest with
        | none =>
            rw [hNat] at hDecoded
            contradiction
        | some decoded =>
            rcases decoded with ⟨index, decodedSuffix⟩
            rw [hNat] at hDecoded
            have decodedEq :
                (RawSource.gate index, decodedSuffix) = (source, suffix) :=
              Option.some.inj hDecoded
            have sourceEq : RawSource.gate index = source :=
              congrArg Prod.fst decodedEq
            have suffixEq : decodedSuffix = suffix :=
              congrArg Prod.snd decodedEq
            subst source
            subst suffix
            have hNatCanonical :=
              encodeNatTokens_append_eq_of_decodeNatTokens_eq_some
                rest index decodedSuffix hNat
            simp only [encodeSourceTokens, List.cons_append]
            exact congrArg (List.cons Token.gate) hNatCanonical
      all_goals contradiction

private theorem decodeNGatesTokens_length_and_canonical
    (count : Nat) (tokens : List Token)
    (gates : List RawGate) (suffix : List Token)
    (hDecoded :
      decodeNGatesTokens count tokens = some (gates, suffix)) :
    gates.length = count ∧
      encodeGateListTokens gates ++ suffix = tokens := by
  induction count generalizing tokens gates suffix with
  | zero =>
      simp only [decodeNGatesTokens] at hDecoded
      have decodedEq : ([], tokens) = (gates, suffix) :=
        Option.some.inj hDecoded
      cases decodedEq
      exact ⟨rfl, rfl⟩
  | succ count ih =>
      simp only [decodeNGatesTokens] at hDecoded
      cases hLeft : decodeSourceTokens tokens with
      | none =>
          rw [hLeft] at hDecoded
          contradiction
      | some decodedLeft =>
          rcases decodedLeft with ⟨left, afterLeft⟩
          rw [hLeft] at hDecoded
          simp only at hDecoded
          cases hRight : decodeSourceTokens afterLeft with
          | none =>
              rw [hRight] at hDecoded
              contradiction
          | some decodedRight =>
              rcases decodedRight with ⟨right, afterRight⟩
              rw [hRight] at hDecoded
              simp only at hDecoded
              cases afterRight with
              | nil =>
                  contradiction
              | cons terminator afterGate =>
                  cases terminator <;> simp only at hDecoded
                  case gateEnd =>
                    cases hRest :
                        decodeNGatesTokens count afterGate with
                    | none =>
                        rw [hRest] at hDecoded
                        contradiction
                    | some decodedRest =>
                        rcases decodedRest with
                          ⟨restGates, decodedSuffix⟩
                        rw [hRest] at hDecoded
                        simp only at hDecoded
                        have decodedEq :
                            ({ left := left, right := right } :: restGates,
                              decodedSuffix) = (gates, suffix) :=
                          Option.some.inj hDecoded
                        have gatesEq :
                            { left := left, right := right } :: restGates =
                              gates :=
                          congrArg Prod.fst decodedEq
                        have suffixEq : decodedSuffix = suffix :=
                          congrArg Prod.snd decodedEq
                        subst gates
                        subst suffix
                        have leftCanonical :=
                          encodeSourceTokens_append_eq_of_decodeSourceTokens_eq_some
                            tokens left afterLeft hLeft
                        have rightCanonical :=
                          encodeSourceTokens_append_eq_of_decodeSourceTokens_eq_some
                            afterLeft right
                              (Token.gateEnd :: afterGate) hRight
                        have restResult :=
                          ih afterGate restGates decodedSuffix hRest
                        constructor
                        · simp [restResult.1]
                        · calc
                            encodeGateListTokens
                                  ({ left := left, right := right } ::
                                    restGates) ++
                                decodedSuffix =
                              encodeSourceTokens left ++
                                (encodeSourceTokens right ++
                                  (Token.gateEnd ::
                                    (encodeGateListTokens restGates ++
                                      decodedSuffix))) := by
                                simp [encodeGateListTokens,
                                  encodeGateTokens, List.append_assoc]
                            _ = encodeSourceTokens left ++
                                  (encodeSourceTokens right ++
                                    (Token.gateEnd :: afterGate)) := by
                              rw [restResult.2]
                            _ = encodeSourceTokens left ++ afterLeft := by
                              rw [rightCanonical]
                            _ = tokens := leftCanonical
                  all_goals contradiction

private theorem encodeCircuitTokens_eq_of_decodeCircuitTokens_eq_some
    (tokens : List Token) (raw : RawCircuit)
    (hDecoded : decodeCircuitTokens tokens = some raw) :
    encodeCircuitTokens raw = tokens := by
  cases tokens with
  | nil =>
      contradiction
  | cons first afterVersion =>
      cases first <;> simp only [decodeCircuitTokens] at hDecoded
      case version0 =>
        cases hInputs : decodeNatTokens afterVersion with
        | none =>
            rw [hInputs] at hDecoded
            contradiction
        | some decodedInputs =>
            rcases decodedInputs with ⟨inputs, afterInputs⟩
            rw [hInputs] at hDecoded
            simp only at hDecoded
            cases hGateCount : decodeNatTokens afterInputs with
            | none =>
                rw [hGateCount] at hDecoded
                contradiction
            | some decodedGateCount =>
                rcases decodedGateCount with
                  ⟨gateCount, afterGateCount⟩
                rw [hGateCount] at hDecoded
                simp only at hDecoded
                cases hGates :
                    decodeNGatesTokens gateCount afterGateCount with
                | none =>
                    rw [hGates] at hDecoded
                    contradiction
                | some decodedGates =>
                    rcases decodedGates with ⟨gates, afterGates⟩
                    rw [hGates] at hDecoded
                    cases afterGates with
                    | nil =>
                        contradiction
                    | cons programTerminator afterProgram =>
                        cases programTerminator <;>
                          simp only at hDecoded
                        case programEnd =>
                          cases hOutput :
                              decodeSourceTokens afterProgram with
                          | none =>
                              rw [hOutput] at hDecoded
                              contradiction
                          | some decodedOutput =>
                              rcases decodedOutput with
                                ⟨output, afterOutput⟩
                              rw [hOutput] at hDecoded
                              cases afterOutput with
                              | nil =>
                                  contradiction
                              | cons outputsTerminator afterOutputs =>
                                  cases outputsTerminator
                                  case outputsEnd =>
                                    cases afterOutputs with
                                    | nil =>
                                        contradiction
                                    | cons instanceTerminator trailing =>
                                        cases instanceTerminator
                                        case instanceEnd =>
                                          cases trailing with
                                          | cons extra more =>
                                              contradiction
                                          | nil =>
                                              have rawEq :
                                                  { inputCount := inputs
                                                    gates := gates
                                                    output := output } =
                                                    raw :=
                                                Option.some.inj hDecoded
                                              rw [← rawEq]
                                              have inputsCanonical :=
                                                encodeNatTokens_append_eq_of_decodeNatTokens_eq_some
                                                  afterVersion inputs
                                                    afterInputs hInputs
                                              have gateCountCanonical :=
                                                encodeNatTokens_append_eq_of_decodeNatTokens_eq_some
                                                  afterInputs gateCount
                                                    afterGateCount
                                                    hGateCount
                                              have gatesResult :=
                                                decodeNGatesTokens_length_and_canonical
                                                  gateCount afterGateCount
                                                    gates
                                                    (Token.programEnd ::
                                                      afterProgram)
                                                    hGates
                                              have outputCanonical :=
                                                encodeSourceTokens_append_eq_of_decodeSourceTokens_eq_some
                                                  afterProgram output
                                                    [Token.outputsEnd,
                                                      Token.instanceEnd]
                                                    hOutput
                                              simp only [encodeCircuitTokens,
                                                gatesResult.1,
                                                List.append_assoc,
                                                List.singleton_append]
                                              rw [← inputsCanonical,
                                                ← gateCountCanonical,
                                                ← gatesResult.2,
                                                ← outputCanonical]
                                              simp only [List.cons_append]
                                        all_goals contradiction
                                  all_goals contradiction
                        all_goals contradiction
      all_goals contradiction

/-- Strict circuit decoding is canonical in the reverse direction: every
successful parse reconstructs exactly the original bitstring, including all
terminators and the absence of trailing data. -/
theorem encodeCircuit_eq_of_decodeCircuit_eq_some
    (bits : BitString) (raw : RawCircuit)
    (hDecoded : decodeCircuit bits = some raw) :
    encodeCircuit raw = bits := by
  unfold decodeCircuit at hDecoded
  cases hTokens : decodeTokens bits with
  | none =>
      rw [hTokens] at hDecoded
      contradiction
  | some tokens =>
      rw [hTokens] at hDecoded
      have tokenBits :=
        encodeTokens_eq_of_decodeTokens_eq_some bits tokens hTokens
      have circuitTokens :=
        encodeCircuitTokens_eq_of_decodeCircuitTokens_eq_some
          tokens raw hDecoded
      unfold encodeCircuit
      rw [circuitTokens, tokenBits]

/-- The complete strict source boundary succeeds exactly when token decoding
returns a raw circuit whose gate list and output references are well formed.
This is the semantic contract for the later literal parser machine. -/
theorem decodeElaboratedCircuit_exists_iff
    (bits : BitString) :
    (∃ packed, decodeElaboratedCircuit bits = some packed) ↔
      ∃ raw,
        decodeCircuit bits = some raw ∧ raw.wellFormed = true := by
  cases decoded : decodeCircuit bits with
  | none =>
      simp [decodeElaboratedCircuit, decoded]
  | some raw =>
      simpa [decodeElaboratedCircuit, decoded] using
        (RawCircuit.elaborate_exists_iff_wellFormed raw)

/-- A successful elaborated decode therefore carries a canonical raw
preimage: the supplied bytes are exactly its strict encoding, and the raw
circuit satisfies every source bound. -/
theorem decodeElaboratedCircuit_eq_some_exists_encoded_wellFormed
    (bits : BitString) (packed : PackedCircuit)
    (hDecoded : decodeElaboratedCircuit bits = some packed) :
    ∃ raw,
      bits = encodeCircuit raw ∧ raw.wellFormed = true := by
  unfold decodeElaboratedCircuit at hDecoded
  cases hCircuit : decodeCircuit bits with
  | none =>
      rw [hCircuit] at hDecoded
      contradiction
  | some raw =>
      rw [hCircuit] at hDecoded
      refine
        ⟨raw,
          (encodeCircuit_eq_of_decodeCircuit_eq_some
            bits raw hCircuit).symm,
          ?_⟩
      exact
        (RawCircuit.elaborate_exists_iff_wellFormed raw).mp
          ⟨packed, hDecoded⟩

end LockedNAND
end Concrete
end PNP
