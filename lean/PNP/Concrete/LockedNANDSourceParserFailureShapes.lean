/-
Copyright (c) 2026 PNP Labs.

Constructive normal forms for failures at the strict-v0 locked-NAND source
boundary.  These shapes are deliberately phrased as exact list
decompositions: the operational parser proofs can consume them without
performing a host-side decoder lookup.
-/

import PNP.Concrete.LockedNANDEncoding
import PNP.Concrete.WorkInput

namespace PNP.Concrete.LockedNAND.SourceParser

/-! ### Four-bit framing failures -/

/-- A canonical first failure while dividing a bitstring into four-bit
tokens.  In the reserved-code case, `tokenPrefix` is the complete
successfully decoded token prefix and `suffix` is everything after the first `11xx`
codepoint. -/
inductive TokenDecodeFailure : BitString → Prop where
  | reserved (tokenPrefix : List Token) (third fourth : Bool)
      (suffix : BitString) :
      TokenDecodeFailure
        (encodeTokens tokenPrefix ++
          [true, true, third, fourth] ++ suffix)
  | trailingOne (tokenPrefix : List Token) (first : Bool) :
      TokenDecodeFailure (encodeTokens tokenPrefix ++ [first])
  | trailingTwo (tokenPrefix : List Token) (first second : Bool) :
      TokenDecodeFailure
        (encodeTokens tokenPrefix ++ [first, second])
  | trailingThree (tokenPrefix : List Token)
      (first second third : Bool) :
      TokenDecodeFailure
        (encodeTokens tokenPrefix ++ [first, second, third])

theorem decodeTokens_encodeTokens_append
    (tokenPrefix : List Token) (suffix : BitString) :
    decodeTokens (encodeTokens tokenPrefix ++ suffix) =
      match decodeTokens suffix with
      | none => none
      | some tokens => some (tokenPrefix ++ tokens) := by
  induction tokenPrefix with
  | nil =>
      change
        decodeTokens suffix =
          match decodeTokens suffix with
          | none => none
          | some tokens => some tokens
      cases decodeTokens suffix <;> rfl
  | cons token tokenPrefix ih =>
      cases token <;>
        simp [encodeTokens, Token.bits, Token.ofBits,
          decodeTokens, ih] <;>
        cases decodeTokens suffix <;> rfl

theorem TokenDecodeFailure.decodeTokens_eq_none
    {bits : BitString} (failure : TokenDecodeFailure bits) :
    decodeTokens bits = none := by
  cases failure with
  | reserved tokenPrefix third fourth suffix =>
      rw [List.append_assoc, decodeTokens_encodeTokens_append]
      cases third <;> cases fourth <;> rfl
  | trailingOne tokenPrefix first =>
      rw [decodeTokens_encodeTokens_append]
      cases first <;> rfl
  | trailingTwo tokenPrefix first second =>
      rw [decodeTokens_encodeTokens_append]
      cases first <;> cases second <;> rfl
  | trailingThree tokenPrefix first second third =>
      rw [decodeTokens_encodeTokens_append]
      cases first <;> cases second <;> cases third <;> rfl

private theorem token_bits_eq_of_ofBits_eq_some
    (first second third fourth : Bool) (token : Token)
    (decoded :
      Token.ofBits first second third fourth = some token) :
    [first, second, third, fourth] = token.bits := by
  cases first <;> cases second <;> cases third <;> cases fourth <;>
    simp [Token.ofBits] at decoded <;>
    subst token <;> rfl

private theorem ofBits_eq_none_iff_first_two_true
    (first second third fourth : Bool) :
    Token.ofBits first second third fourth = none ↔
      first = true ∧ second = true := by
  cases first <;> cases second <;> cases third <;> cases fourth <;>
    simp [Token.ofBits]

theorem TokenDecodeFailure.prepend
    {bits : BitString} (failure : TokenDecodeFailure bits)
    (token : Token) :
    TokenDecodeFailure (token.bits ++ bits) := by
  cases failure with
  | reserved tokenPrefix third fourth suffix =>
      simpa [encodeTokens, List.append_assoc] using
        (TokenDecodeFailure.reserved (token :: tokenPrefix)
          third fourth suffix)
  | trailingOne tokenPrefix first =>
      simpa [encodeTokens, List.append_assoc] using
        (TokenDecodeFailure.trailingOne (token :: tokenPrefix) first)
  | trailingTwo tokenPrefix first second =>
      simpa [encodeTokens, List.append_assoc] using
        (TokenDecodeFailure.trailingTwo (token :: tokenPrefix)
          first second)
  | trailingThree tokenPrefix first second third =>
      simpa [encodeTokens, List.append_assoc] using
        (TokenDecodeFailure.trailingThree (token :: tokenPrefix)
          first second third)

private def tokenFailureOfNone :
    (bits : BitString) →
      decodeTokens bits = none → TokenDecodeFailure bits
  | [], rejected => by
      simp [decodeTokens] at rejected
  | [first], _ =>
      .trailingOne [] first
  | [first, second], _ =>
      .trailingTwo [] first second
  | [first, second, third], _ =>
      .trailingThree [] first second third
  | first :: second :: third :: fourth :: rest, rejected => by
      cases tokenEq :
          Token.ofBits first second third fourth with
      | none =>
          have firstTwo :=
            (ofBits_eq_none_iff_first_two_true
              first second third fourth).mp tokenEq
          have firstEq := firstTwo.1
          have secondEq := firstTwo.2
          subst first
          subst second
          exact .reserved [] third fourth rest
      | some token =>
          have restRejected : decodeTokens rest = none := by
            cases restEq : decodeTokens rest with
            | none => rfl
            | some decoded =>
                simp [decodeTokens, tokenEq, restEq] at rejected
          have failure := tokenFailureOfNone rest restRejected
          change
            TokenDecodeFailure
              ([first, second, third, fourth] ++ rest)
          rw [token_bits_eq_of_ofBits_eq_some
            first second third fourth token tokenEq]
          exact failure.prepend token

theorem decodeTokens_eq_none_iff_failure (bits : BitString) :
    decodeTokens bits = none ↔ TokenDecodeFailure bits := by
  constructor
  · exact tokenFailureOfNone bits
  · exact TokenDecodeFailure.decodeTokens_eq_none

/-! ### Exact packed shapes of four-bit framing failures -/

/-- The work-cell word obtained by pairing an arbitrary raw bitstring.
Unlike a canonical token word, an odd final bit is paired with blank. -/
def packedRawBits (bits : BitString) : List WorkSymbol :=
  packWorkSymbols (bits.map TapeSymbol.ofBool)

/-- The ordinary work cell occupied by two raw Boolean bits. -/
def boolPairWorkCell (first second : Bool) : WorkSymbol :=
  { first := TapeSymbol.ofBool first
    second := TapeSymbol.ofBool second }

/-- The final work cell occupied by one unpaired raw Boolean bit. -/
def danglingWorkCell (first : Bool) : WorkSymbol :=
  { first := TapeSymbol.ofBool first
    second := TapeSymbol.blank }

/-- The six work symbols that can occur while packing raw Boolean input.
The last two alternatives are the two possible dangling-bit cells. -/
def SourcePackedCell (symbol : WorkSymbol) : Prop :=
  symbol = WorkSymbol.zeroZero ∨
    symbol = WorkSymbol.zeroOne ∨
    symbol = WorkSymbol.zeroBlank ∨
    symbol = WorkSymbol.oneBlank ∨
    symbol = WorkSymbol.oneZero ∨
    symbol = WorkSymbol.oneOne

/-- The work-cell suffix installed by each canonical four-bit framing
failure.  The reserved-code constructor deliberately retains every raw bit
after the first `11xx` codepoint. -/
inductive MalformedWorkTail : BitString → List WorkSymbol → Prop where
  | reserved (third fourth : Bool) (suffix : BitString) :
      MalformedWorkTail
        ([true, true, third, fourth] ++ suffix)
        (WorkSymbol.oneOne ::
          boolPairWorkCell third fourth ::
            packedRawBits suffix)
  | trailingOne (first : Bool) :
      MalformedWorkTail
        [first] [danglingWorkCell first]
  | trailingTwo (first second : Bool) :
      MalformedWorkTail
        [first, second] [boolPairWorkCell first second]
  | trailingThree (first second third : Bool) :
      MalformedWorkTail
        [first, second, third]
        [boolPairWorkCell first second, danglingWorkCell third]

private theorem packedRawBits_token_append
    (token : Token) (tail : BitString) :
    packedRawBits (token.bits ++ tail) =
      packedRawBits token.bits ++ packedRawBits tail := by
  cases token <;> rfl

/-- A canonical token prefix occupies a whole number of work cells, so
packing commutes exactly with appending an arbitrary raw suffix. -/
theorem packedRawBits_encodeTokens_append
    (tokens : List Token) (tail : BitString) :
    packedRawBits (encodeTokens tokens ++ tail) =
      packedRawBits (encodeTokens tokens) ++
        packedRawBits tail := by
  induction tokens with
  | nil =>
      rfl
  | cons token rest ih =>
      simp only [encodeTokens]
      rw [List.append_assoc]
      rw [packedRawBits_token_append,
        packedRawBits_token_append, ih,
        List.append_assoc]

/-- Every decoder framing failure exposes its complete canonical token
prefix, the exact failing raw-bit tail, and the exact corresponding packed
work-cell decomposition. -/
theorem TokenDecodeFailure.packedShape
    {bits : BitString} (failure : TokenDecodeFailure bits) :
    ∃ tokenPrefix rawTail workTail,
      MalformedWorkTail rawTail workTail ∧
      bits = encodeTokens tokenPrefix ++ rawTail ∧
      packedRawBits bits =
        packedRawBits (encodeTokens tokenPrefix) ++ workTail := by
  cases failure with
  | reserved tokenPrefix third fourth suffix =>
      refine
        ⟨tokenPrefix,
          [true, true, third, fourth] ++ suffix,
          WorkSymbol.oneOne ::
            boolPairWorkCell third fourth ::
              packedRawBits suffix,
          .reserved third fourth suffix,
          List.append_assoc _ _ _, ?_⟩
      rw [List.append_assoc,
        packedRawBits_encodeTokens_append]
      cases third <;> cases fourth <;> rfl
  | trailingOne tokenPrefix first =>
      refine
        ⟨tokenPrefix, [first], [danglingWorkCell first],
          .trailingOne first, rfl, ?_⟩
      rw [packedRawBits_encodeTokens_append]
      cases first <;> rfl
  | trailingTwo tokenPrefix first second =>
      refine
        ⟨tokenPrefix, [first, second],
          [boolPairWorkCell first second],
          .trailingTwo first second, rfl, ?_⟩
      rw [packedRawBits_encodeTokens_append]
      cases first <;> cases second <;> rfl
  | trailingThree tokenPrefix first second third =>
      refine
        ⟨tokenPrefix, [first, second, third],
          [boolPairWorkCell first second,
            danglingWorkCell third],
          .trailingThree first second third, rfl, ?_⟩
      rw [packedRawBits_encodeTokens_append]
      cases first <;> cases second <;> cases third <;> rfl

/-- The indexed work tail is exactly the generic pairing of its indexed raw
tail. -/
theorem MalformedWorkTail.workTail_eq_packedRawBits
    {rawTail : BitString} {workTail : List WorkSymbol}
    (failure : MalformedWorkTail rawTail workTail) :
    workTail = packedRawBits rawTail := by
  cases failure with
  | reserved third fourth suffix =>
      cases third <;> cases fourth <;> rfl
  | trailingOne first =>
      cases first <;> rfl
  | trailingTwo first second =>
      cases first <;> cases second <;> rfl
  | trailingThree first second third =>
      cases first <;> cases second <;> cases third <;> rfl

/-- Pairing raw bits never produces a work cell whose first component is
blank. -/
theorem packedRawBits_first_ne_blank :
    ∀ (bits : BitString) (symbol : WorkSymbol),
      symbol ∈ packedRawBits bits →
        symbol.first ≠ TapeSymbol.blank
  | [], symbol, member => by
      contradiction
  | first :: [], symbol, member => by
      simp only [packedRawBits, List.map,
        packWorkSymbols, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst symbol
      cases first <;> decide
  | first :: second :: rest, symbol, member => by
      simp only [packedRawBits, List.map,
        packWorkSymbols, List.mem_cons] at member
      rcases member with head | inRest
      · subst symbol
        cases first <;> cases second <;> decide
      · exact packedRawBits_first_ne_blank
          rest symbol inRest

/-- Every packed raw-input cell is one of the six source-cell shapes. -/
theorem packedRawBits_allSourcePacked :
    ∀ (bits : BitString) (symbol : WorkSymbol),
      symbol ∈ packedRawBits bits → SourcePackedCell symbol
  | [], symbol, member => by
      contradiction
  | first :: [], symbol, member => by
      simp only [packedRawBits, List.map,
        packWorkSymbols, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst symbol
      cases first <;>
        simp [SourcePackedCell, TapeSymbol.ofBool,
          WorkSymbol.zeroBlank, WorkSymbol.oneBlank]
  | first :: second :: rest, symbol, member => by
      simp only [packedRawBits, List.map,
        packWorkSymbols, List.mem_cons] at member
      rcases member with head | inRest
      · subst symbol
        cases first <;> cases second <;>
          simp [SourcePackedCell, TapeSymbol.ofBool,
            WorkSymbol.zeroZero, WorkSymbol.zeroOne,
            WorkSymbol.oneZero, WorkSymbol.oneOne]
      · exact packedRawBits_allSourcePacked
          rest symbol inRest

/-- Every malformed work tail is nonempty. -/
theorem MalformedWorkTail.nonempty
    {rawTail : BitString} {workTail : List WorkSymbol}
    (failure : MalformedWorkTail rawTail workTail) :
    workTail ≠ [] := by
  cases failure <;> simp

/-- Every malformed-tail work cell has a nonblank first component. -/
theorem MalformedWorkTail.first_ne_blank
    {rawTail : BitString} {workTail : List WorkSymbol}
    (failure : MalformedWorkTail rawTail workTail)
    (symbol : WorkSymbol) (member : symbol ∈ workTail) :
    symbol.first ≠ TapeSymbol.blank := by
  apply packedRawBits_first_ne_blank rawTail symbol
  rwa [failure.workTail_eq_packedRawBits] at member

/-- In particular, no malformed-tail cell is the all-blank work symbol. -/
theorem MalformedWorkTail.nonblank
    {rawTail : BitString} {workTail : List WorkSymbol}
    (failure : MalformedWorkTail rawTail workTail)
    (symbol : WorkSymbol) (member : symbol ∈ workTail) :
    symbol ≠ WorkSymbol.blank := by
  intro symbolEq
  have firstEq := congrArg WorkSymbol.first symbolEq
  exact
    (failure.first_ne_blank symbol member)
      (by simpa [WorkSymbol.blank] using firstEq)

/-- No malformed-tail cell can be confused with a blank/zero left guard. -/
theorem MalformedWorkTail.noBlankZero
    {rawTail : BitString} {workTail : List WorkSymbol}
    (failure : MalformedWorkTail rawTail workTail)
    (symbol : WorkSymbol) (member : symbol ∈ workTail) :
    symbol ≠ WorkSymbol.blankZero := by
  intro symbolEq
  have firstEq := congrArg WorkSymbol.first symbolEq
  exact
    (failure.first_ne_blank symbol member)
      (by simpa [WorkSymbol.blankZero] using firstEq)

/-- Every malformed-tail cell has one of the six raw source-cell shapes. -/
theorem MalformedWorkTail.allSourcePacked
    {rawTail : BitString} {workTail : List WorkSymbol}
    (failure : MalformedWorkTail rawTail workTail)
    (symbol : WorkSymbol) (member : symbol ∈ workTail) :
    SourcePackedCell symbol := by
  apply packedRawBits_allSourcePacked rawTail symbol
  rwa [failure.workTail_eq_packedRawBits] at member

/-- Pairing raw bits cannot create more work cells than there are raw bits. -/
theorem packedRawBits_length_le :
    ∀ bits : BitString,
      (packedRawBits bits).length ≤ bits.length
  | [] => by
      change 0 ≤ 0
      omega
  | first :: [] => by
      simp [packedRawBits, packWorkSymbols]
  | first :: second :: rest => by
      have tailBound := packedRawBits_length_le rest
      simp only [packedRawBits, List.map,
        packWorkSymbols, List.length_cons] at tailBound ⊢
      omega

/-- The same length bound specialized to a malformed tail. -/
theorem MalformedWorkTail.length_le_rawTail
    {rawTail : BitString} {workTail : List WorkSymbol}
    (failure : MalformedWorkTail rawTail workTail) :
    workTail.length ≤ rawTail.length := by
  rw [failure.workTail_eq_packedRawBits]
  exact packedRawBits_length_le rawTail

/-! ### Token-grammar component failures -/

/-- A unary natural is malformed precisely when its initial run of `unit`
tokens is not terminated by `natEnd`. -/
inductive NatTokenFailure : List Token → Prop where
  | missingEnd (units : Nat) :
      NatTokenFailure (List.replicate units .unit)
  | wrongToken (units : Nat) (token : Token) (suffix : List Token)
      (notUnit : token ≠ .unit) (notNatEnd : token ≠ .natEnd) :
      NatTokenFailure
        (List.replicate units .unit ++ token :: suffix)

private theorem encodeNatTokens_append_eq_of_decodeNatTokens_eq_some
    (tokens : List Token) (value : Nat) (suffix : List Token)
    (decoded : decodeNatTokens tokens = some (value, suffix)) :
    encodeNatTokens value ++ suffix = tokens := by
  induction tokens generalizing value suffix with
  | nil =>
      contradiction
  | cons token rest ih =>
      cases token <;> simp only [decodeNatTokens] at decoded
      case unit =>
        cases restEq : decodeNatTokens rest with
        | none =>
            rw [restEq] at decoded
            contradiction
        | some decodedPair =>
            rcases decodedPair with ⟨prior, tail⟩
            rw [restEq] at decoded
            have pairEq :
                (prior + 1, tail) = (value, suffix) :=
              Option.some.inj decoded
            have valueEq : prior + 1 = value :=
              congrArg Prod.fst pairEq
            have suffixEq : tail = suffix :=
              congrArg Prod.snd pairEq
            subst value
            subst suffix
            have tailShape := ih prior tail restEq
            simp only [encodeNatTokens, List.cons_append]
            exact congrArg (List.cons Token.unit) tailShape
      case natEnd =>
        have pairEq : (0, rest) = (value, suffix) :=
          Option.some.inj decoded
        have valueEq : 0 = value := congrArg Prod.fst pairEq
        have suffixEq : rest = suffix := congrArg Prod.snd pairEq
        subst value
        subst suffix
        rfl
      all_goals contradiction

theorem decodeNatTokens_eq_some_iff
    (tokens : List Token) (value : Nat) (suffix : List Token) :
    decodeNatTokens tokens = some (value, suffix) ↔
      tokens = encodeNatTokens value ++ suffix := by
  constructor
  · intro decoded
    exact
      (encodeNatTokens_append_eq_of_decodeNatTokens_eq_some
        tokens value suffix decoded).symm
  · intro shape
    rw [shape, decodeNatTokens_encodeNatTokens_append]

theorem NatTokenFailure.decodeNatTokens_eq_none
    {tokens : List Token} (failure : NatTokenFailure tokens) :
    decodeNatTokens tokens = none := by
  cases failure with
  | missingEnd units =>
      induction units with
      | zero => rfl
      | succ units ih =>
          rw [List.replicate_succ]
          change
            (match decodeNatTokens (List.replicate units Token.unit) with
              | none => none
              | some (value, suffix) => some (value + 1, suffix)) =
                none
          rw [ih]
  | wrongToken units token suffix notUnit notNatEnd =>
      induction units with
      | zero =>
          cases token <;>
            simp [decodeNatTokens] at notUnit notNatEnd ⊢
      | succ units ih =>
          rw [List.replicate_succ, List.cons_append]
          change
            (match
                decodeNatTokens
                  (List.replicate units Token.unit ++ token :: suffix)
              with
              | none => none
              | some (value, tail) => some (value + 1, tail)) =
                none
          rw [ih]

theorem decodeNatTokens_eq_none_iff_failure (tokens : List Token) :
    decodeNatTokens tokens = none ↔ NatTokenFailure tokens := by
  constructor
  · induction tokens with
    | nil =>
        intro _
        exact .missingEnd 0
    | cons token rest ih =>
        intro h
        if unitEq : token = .unit then
          subst token
          cases restEq : decodeNatTokens rest with
          | some decoded => simp [decodeNatTokens, restEq] at h
          | none =>
              cases ih restEq with
              | missingEnd units =>
                  simpa [List.replicate_succ] using
                    (NatTokenFailure.missingEnd (units + 1))
              | wrongToken units bad suffix notUnit notNatEnd =>
                  simpa [List.replicate_succ, List.append_assoc] using
                    (NatTokenFailure.wrongToken (units + 1)
                      bad suffix notUnit notNatEnd)
        else if endEq : token = .natEnd then
          subst token
          simp [decodeNatTokens] at h
        else
          exact .wrongToken 0 token rest unitEq endEq
  · exact NatTokenFailure.decodeNatTokens_eq_none

/-- A source failure retains the exact malformed source suffix. -/
inductive SourceTokenFailure : List Token → Prop where
  | missing : SourceTokenFailure []
  | wrongHead (token : Token) (suffix : List Token)
      (notInput : token ≠ .input)
      (notFalse : token ≠ .constantFalse)
      (notTrue : token ≠ .constantTrue)
      (notGate : token ≠ .gate) :
      SourceTokenFailure (token :: suffix)
  | inputIndex {tokens : List Token}
      (failure : NatTokenFailure tokens) :
      SourceTokenFailure (.input :: tokens)
  | gateIndex {tokens : List Token}
      (failure : NatTokenFailure tokens) :
      SourceTokenFailure (.gate :: tokens)

private theorem encodeSourceTokens_append_eq_of_decodeSourceTokens_eq_some
    (tokens : List Token) (source : RawSource) (suffix : List Token)
    (decoded : decodeSourceTokens tokens = some (source, suffix)) :
    encodeSourceTokens source ++ suffix = tokens := by
  cases tokens with
  | nil =>
      contradiction
  | cons token rest =>
      cases token <;> simp only [decodeSourceTokens] at decoded
      case input =>
        cases natEq : decodeNatTokens rest with
        | none =>
            rw [natEq] at decoded
            contradiction
        | some decodedPair =>
            rcases decodedPair with ⟨index, tail⟩
            rw [natEq] at decoded
            have pairEq :
                (RawSource.input index, tail) = (source, suffix) :=
              Option.some.inj decoded
            have sourceEq : RawSource.input index = source :=
              congrArg Prod.fst pairEq
            have suffixEq : tail = suffix :=
              congrArg Prod.snd pairEq
            subst source
            subst suffix
            have natShape :=
              encodeNatTokens_append_eq_of_decodeNatTokens_eq_some
                rest index tail natEq
            simp only [encodeSourceTokens, List.cons_append]
            exact congrArg (List.cons Token.input) natShape
      case constantFalse =>
        have pairEq :
            (RawSource.constant false, rest) = (source, suffix) :=
          Option.some.inj decoded
        cases pairEq
        rfl
      case constantTrue =>
        have pairEq :
            (RawSource.constant true, rest) = (source, suffix) :=
          Option.some.inj decoded
        cases pairEq
        rfl
      case gate =>
        cases natEq : decodeNatTokens rest with
        | none =>
            rw [natEq] at decoded
            contradiction
        | some decodedPair =>
            rcases decodedPair with ⟨index, tail⟩
            rw [natEq] at decoded
            have pairEq :
                (RawSource.gate index, tail) = (source, suffix) :=
              Option.some.inj decoded
            have sourceEq : RawSource.gate index = source :=
              congrArg Prod.fst pairEq
            have suffixEq : tail = suffix :=
              congrArg Prod.snd pairEq
            subst source
            subst suffix
            have natShape :=
              encodeNatTokens_append_eq_of_decodeNatTokens_eq_some
                rest index tail natEq
            simp only [encodeSourceTokens, List.cons_append]
            exact congrArg (List.cons Token.gate) natShape
      all_goals contradiction

theorem decodeSourceTokens_eq_some_iff
    (tokens : List Token) (source : RawSource) (suffix : List Token) :
    decodeSourceTokens tokens = some (source, suffix) ↔
      tokens = encodeSourceTokens source ++ suffix := by
  constructor
  · intro decoded
    exact
      (encodeSourceTokens_append_eq_of_decodeSourceTokens_eq_some
        tokens source suffix decoded).symm
  · intro shape
    rw [shape, decodeSourceTokens_encodeSourceTokens_append]

theorem SourceTokenFailure.decodeSourceTokens_eq_none
    {tokens : List Token} (failure : SourceTokenFailure tokens) :
    decodeSourceTokens tokens = none := by
  cases failure with
  | missing => rfl
  | wrongHead token suffix notInput notFalse notTrue notGate =>
      cases token <;> simp [decodeSourceTokens] at *
  | inputIndex failure =>
      simp [decodeSourceTokens,
        failure.decodeNatTokens_eq_none]
  | gateIndex failure =>
      simp [decodeSourceTokens,
        failure.decodeNatTokens_eq_none]

theorem decodeSourceTokens_eq_none_iff_failure (tokens : List Token) :
    decodeSourceTokens tokens = none ↔ SourceTokenFailure tokens := by
  constructor
  · cases tokens with
    | nil =>
        intro _
        exact .missing
    | cons token rest =>
        intro h
        if inputEq : token = .input then
          subst token
          simp only [decodeSourceTokens] at h
          have natNone : decodeNatTokens rest = none := by
            cases natEq : decodeNatTokens rest with
            | none => rfl
            | some decoded =>
                rw [natEq] at h
                contradiction
          exact .inputIndex
            ((decodeNatTokens_eq_none_iff_failure rest).mp natNone)
        else if falseEq : token = .constantFalse then
          subst token
          simp [decodeSourceTokens] at h
        else if trueEq : token = .constantTrue then
          subst token
          simp [decodeSourceTokens] at h
        else if gateEq : token = .gate then
          subst token
          simp only [decodeSourceTokens] at h
          have natNone : decodeNatTokens rest = none := by
            cases natEq : decodeNatTokens rest with
            | none => rfl
            | some decoded =>
                rw [natEq] at h
                contradiction
          exact .gateIndex
            ((decodeNatTokens_eq_none_iff_failure rest).mp natNone)
        else
          exact .wrongHead token rest
            inputEq falseEq trueEq gateEq
  · exact SourceTokenFailure.decodeSourceTokens_eq_none

/-- Failure while reading exactly the declared number of gates.  Successful
left and right sources are represented canonically by their encodings, so each
constructor gives an exact forward-trace input shape. -/
inductive NGatesTokenFailure : Nat → List Token → Prop where
  | left {count : Nat} {tokens : List Token}
      (failure : SourceTokenFailure tokens) :
      NGatesTokenFailure (count + 1) tokens
  | right (count : Nat) (left : RawSource)
      {tokens : List Token}
      (failure : SourceTokenFailure tokens) :
      NGatesTokenFailure (count + 1)
        (encodeSourceTokens left ++ tokens)
  | missingGateEnd (count : Nat) (left right : RawSource) :
      NGatesTokenFailure (count + 1)
        (encodeSourceTokens left ++ encodeSourceTokens right)
  | wrongGateEnd (count : Nat) (left right : RawSource)
      (token : Token) (suffix : List Token)
      (notGateEnd : token ≠ .gateEnd) :
      NGatesTokenFailure (count + 1)
        (encodeSourceTokens left ++ encodeSourceTokens right ++
          token :: suffix)
  | rest (count : Nat) (left right : RawSource)
      {tokens : List Token}
      (failure : NGatesTokenFailure count tokens) :
      NGatesTokenFailure (count + 1)
        (encodeSourceTokens left ++ encodeSourceTokens right ++
          .gateEnd :: tokens)

private theorem decodeNGatesTokens_length_and_canonical
    (count : Nat) (tokens : List Token)
    (gates : List RawGate) (suffix : List Token)
    (decoded :
      decodeNGatesTokens count tokens = some (gates, suffix)) :
    gates.length = count ∧
      encodeGateListTokens gates ++ suffix = tokens := by
  induction count generalizing tokens gates suffix with
  | zero =>
      simp only [decodeNGatesTokens] at decoded
      have pairEq : ([], tokens) = (gates, suffix) :=
        Option.some.inj decoded
      cases pairEq
      exact ⟨rfl, rfl⟩
  | succ count ih =>
      simp only [decodeNGatesTokens] at decoded
      cases leftEq : decodeSourceTokens tokens with
      | none =>
          rw [leftEq] at decoded
          contradiction
      | some decodedLeft =>
          rcases decodedLeft with ⟨left, afterLeft⟩
          rw [leftEq] at decoded
          simp only at decoded
          cases rightEq : decodeSourceTokens afterLeft with
          | none =>
              rw [rightEq] at decoded
              contradiction
          | some decodedRight =>
              rcases decodedRight with ⟨right, afterRight⟩
              rw [rightEq] at decoded
              simp only at decoded
              cases afterRight with
              | nil =>
                  contradiction
              | cons terminator afterGate =>
                  cases terminator <;> simp only at decoded
                  case gateEnd =>
                    cases restEq :
                        decodeNGatesTokens count afterGate with
                    | none =>
                        rw [restEq] at decoded
                        contradiction
                    | some decodedRest =>
                        rcases decodedRest with
                          ⟨restGates, decodedSuffix⟩
                        rw [restEq] at decoded
                        simp only at decoded
                        have pairEq :
                            ({ left := left, right := right } :: restGates,
                              decodedSuffix) = (gates, suffix) :=
                          Option.some.inj decoded
                        have gatesEq :
                            { left := left, right := right } :: restGates =
                              gates :=
                          congrArg Prod.fst pairEq
                        have suffixEq : decodedSuffix = suffix :=
                          congrArg Prod.snd pairEq
                        subst gates
                        subst suffix
                        have leftCanonical :=
                          encodeSourceTokens_append_eq_of_decodeSourceTokens_eq_some
                            tokens left afterLeft leftEq
                        have rightCanonical :=
                          encodeSourceTokens_append_eq_of_decodeSourceTokens_eq_some
                            afterLeft right
                              (Token.gateEnd :: afterGate) rightEq
                        have restResult :=
                          ih afterGate restGates decodedSuffix restEq
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

theorem decodeNGatesTokens_eq_some_iff
    (count : Nat) (tokens : List Token)
    (gates : List RawGate) (suffix : List Token) :
    decodeNGatesTokens count tokens = some (gates, suffix) ↔
      gates.length = count ∧
        tokens = encodeGateListTokens gates ++ suffix := by
  constructor
  · intro decoded
    have result :=
      decodeNGatesTokens_length_and_canonical
        count tokens gates suffix decoded
    exact ⟨result.1, result.2.symm⟩
  · rintro ⟨lengthEq, shape⟩
    subst count
    rw [shape, decodeNGatesTokens_encodeGateListTokens_append]

theorem NGatesTokenFailure.decodeNGatesTokens_eq_none
    {count : Nat} {tokens : List Token}
    (failure : NGatesTokenFailure count tokens) :
    decodeNGatesTokens count tokens = none := by
  cases failure with
  | left failure =>
      simp only [decodeNGatesTokens]
      rw [failure.decodeSourceTokens_eq_none]
  | right count left failure =>
      simp only [decodeNGatesTokens]
      rw [decodeSourceTokens_encodeSourceTokens_append]
      simp only
      rw [failure.decodeSourceTokens_eq_none]
  | missingGateEnd count left right =>
      simp only [decodeNGatesTokens]
      rw [decodeSourceTokens_encodeSourceTokens_append]
      simp only
      have rightDecoded :
          decodeSourceTokens (encodeSourceTokens right) =
            some (right, []) := by
        simpa using
          (decodeSourceTokens_encodeSourceTokens_append right [])
      rw [rightDecoded]
  | wrongGateEnd count left right token suffix notGateEnd =>
      simp only [decodeNGatesTokens, List.append_assoc,
        decodeSourceTokens_encodeSourceTokens_append]
      cases token <;> simp at *
  | rest count left right failure =>
      simp only [decodeNGatesTokens, List.append_assoc,
        decodeSourceTokens_encodeSourceTokens_append,
        failure.decodeNGatesTokens_eq_none]

theorem decodeNGatesTokens_eq_none_iff_failure
    (count : Nat) (tokens : List Token) :
    decodeNGatesTokens count tokens = none ↔
      NGatesTokenFailure count tokens := by
  constructor
  · induction count generalizing tokens with
    | zero =>
        intro h
        simp [decodeNGatesTokens] at h
    | succ count ih =>
        intro h
        simp only [decodeNGatesTokens] at h
        cases leftEq : decodeSourceTokens tokens with
        | none =>
            exact .left
              ((decodeSourceTokens_eq_none_iff_failure tokens).mp
                leftEq)
        | some leftPair =>
            rcases leftPair with ⟨left, afterLeft⟩
            rw [leftEq] at h
            simp only at h
            have leftShape :=
              (decodeSourceTokens_eq_some_iff
                tokens left afterLeft).mp leftEq
            cases rightEq : decodeSourceTokens afterLeft with
            | none =>
                rw [leftShape]
                exact .right count left
                  ((decodeSourceTokens_eq_none_iff_failure
                    afterLeft).mp rightEq)
            | some rightPair =>
                rcases rightPair with ⟨right, afterRight⟩
                rw [rightEq] at h
                simp only at h
                have rightShape :=
                  (decodeSourceTokens_eq_some_iff
                    afterLeft right afterRight).mp rightEq
                cases afterRight with
                | nil =>
                    rw [leftShape, rightShape]
                    simpa [List.append_assoc] using
                      (NGatesTokenFailure.missingGateEnd
                        count left right)
                | cons token afterGate =>
                    if gateEndEq : token = .gateEnd then
                      subst token
                      cases restEq :
                          decodeNGatesTokens count afterGate with
                      | some restPair =>
                          simp [restEq] at h
                      | none =>
                          rw [leftShape, rightShape]
                          simpa only [List.append_assoc] using
                            (NGatesTokenFailure.rest count left right
                              (ih afterGate restEq))
                    else
                      rw [leftShape, rightShape]
                      simpa [List.append_assoc] using
                        (NGatesTokenFailure.wrongGateEnd
                          count left right token afterGate gateEndEq)
  · exact NGatesTokenFailure.decodeNGatesTokens_eq_none

/-! ### Complete strict-v0 circuit grammar failures -/

def circuitHeaderTokens (inputs gateCount : Nat) : List Token :=
  .version0 ::
    (encodeNatTokens inputs ++ encodeNatTokens gateCount)

def circuitGatesPrefixTokens
    (inputs : Nat) (gates : List RawGate) : List Token :=
  circuitHeaderTokens inputs gates.length ++
    encodeGateListTokens gates

def circuitOutputPrefixTokens
    (inputs : Nat) (gates : List RawGate)
    (output : RawSource) : List Token :=
  circuitGatesPrefixTokens inputs gates ++ [.programEnd] ++
    encodeSourceTokens output

/-- Exhaustive, stage-normalized failure shapes for `decodeCircuitTokens`.
The final five constructors separate output framing failures so a forward
machine proof never needs to inspect an opaque rejected suffix. -/
inductive CircuitTokenFailure : List Token → Prop where
  | missingVersion : CircuitTokenFailure []
  | wrongVersion (token : Token) (suffix : List Token)
      (notVersion : token ≠ .version0) :
      CircuitTokenFailure (token :: suffix)
  | inputCount {tokens : List Token}
      (failure : NatTokenFailure tokens) :
      CircuitTokenFailure (.version0 :: tokens)
  | gateCount (inputs : Nat) {tokens : List Token}
      (failure : NatTokenFailure tokens) :
      CircuitTokenFailure
        (.version0 :: (encodeNatTokens inputs ++ tokens))
  | gates (inputs gateCount : Nat) {tokens : List Token}
      (failure : NGatesTokenFailure gateCount tokens) :
      CircuitTokenFailure
        (circuitHeaderTokens inputs gateCount ++ tokens)
  | missingProgramEnd (inputs : Nat) (gates : List RawGate) :
      CircuitTokenFailure (circuitGatesPrefixTokens inputs gates)
  | wrongProgramEnd (inputs : Nat) (gates : List RawGate)
      (token : Token) (suffix : List Token)
      (notProgramEnd : token ≠ .programEnd) :
      CircuitTokenFailure
        (circuitGatesPrefixTokens inputs gates ++ token :: suffix)
  | output (inputs : Nat) (gates : List RawGate)
      {tokens : List Token}
      (failure : SourceTokenFailure tokens) :
      CircuitTokenFailure
        (circuitGatesPrefixTokens inputs gates ++
          .programEnd :: tokens)
  | missingOutputsEnd (inputs : Nat) (gates : List RawGate)
      (output : RawSource) :
      CircuitTokenFailure
        (circuitOutputPrefixTokens inputs gates output)
  | wrongOutputsEnd (inputs : Nat) (gates : List RawGate)
      (output : RawSource) (token : Token) (suffix : List Token)
      (notOutputsEnd : token ≠ .outputsEnd) :
      CircuitTokenFailure
        (circuitOutputPrefixTokens inputs gates output ++
          token :: suffix)
  | missingInstanceEnd (inputs : Nat) (gates : List RawGate)
      (output : RawSource) :
      CircuitTokenFailure
        (circuitOutputPrefixTokens inputs gates output ++
          [.outputsEnd])
  | wrongInstanceEnd (inputs : Nat) (gates : List RawGate)
      (output : RawSource) (token : Token) (suffix : List Token)
      (notInstanceEnd : token ≠ .instanceEnd) :
      CircuitTokenFailure
        (circuitOutputPrefixTokens inputs gates output ++
          [.outputsEnd, token] ++ suffix)
  | trailingToken (inputs : Nat) (gates : List RawGate)
      (output : RawSource) (token : Token) (suffix : List Token) :
      CircuitTokenFailure
        (circuitOutputPrefixTokens inputs gates output ++
          [.outputsEnd, .instanceEnd, token] ++ suffix)

private theorem decodeNGatesTokens_encodeGateListTokens
    (gates : List RawGate) :
    decodeNGatesTokens gates.length (encodeGateListTokens gates) =
      some (gates, []) := by
  simpa using
    (decodeNGatesTokens_encodeGateListTokens_append gates [])

private theorem decodeSourceTokens_encodeSourceTokens
    (source : RawSource) :
    decodeSourceTokens (encodeSourceTokens source) =
      some (source, []) := by
  simpa using
    (decodeSourceTokens_encodeSourceTokens_append source [])

theorem decodeCircuitTokens_eq_none_iff_failure
    (tokens : List Token) :
    decodeCircuitTokens tokens = none ↔ CircuitTokenFailure tokens := by
  constructor
  · intro rejected
    cases tokens with
    | nil =>
        exact .missingVersion
    | cons token afterVersion =>
        if versionEq : token = .version0 then
          subst token
          simp only [decodeCircuitTokens] at rejected
          cases inputsEq : decodeNatTokens afterVersion with
          | none =>
              exact .inputCount
                ((decodeNatTokens_eq_none_iff_failure
                  afterVersion).mp inputsEq)
          | some inputsPair =>
              rcases inputsPair with ⟨inputs, afterInputs⟩
              rw [inputsEq] at rejected
              simp only at rejected
              have inputsShape :=
                (decodeNatTokens_eq_some_iff
                  afterVersion inputs afterInputs).mp inputsEq
              cases gateCountEq : decodeNatTokens afterInputs with
              | none =>
                  rw [inputsShape]
                  exact .gateCount inputs
                    ((decodeNatTokens_eq_none_iff_failure
                      afterInputs).mp gateCountEq)
              | some gateCountPair =>
                  rcases gateCountPair with
                    ⟨gateCount, afterGateCount⟩
                  rw [gateCountEq] at rejected
                  simp only at rejected
                  have gateCountShape :=
                    (decodeNatTokens_eq_some_iff
                      afterInputs gateCount afterGateCount).mp
                        gateCountEq
                  cases gatesEq :
                      decodeNGatesTokens gateCount afterGateCount with
                  | none =>
                      rw [inputsShape, gateCountShape]
                      simpa [circuitHeaderTokens,
                        List.append_assoc] using
                        (CircuitTokenFailure.gates inputs gateCount
                          ((decodeNGatesTokens_eq_none_iff_failure
                            gateCount afterGateCount).mp gatesEq))
                  | some gatesPair =>
                      rcases gatesPair with ⟨gates, afterGates⟩
                      rw [gatesEq] at rejected
                      have gatesShape :=
                        (decodeNGatesTokens_eq_some_iff
                          gateCount afterGateCount gates
                          afterGates).mp gatesEq
                      have gateLength : gates.length = gateCount :=
                        gatesShape.1
                      cases afterGates with
                      | nil =>
                          rw [inputsShape, gateCountShape,
                            gatesShape.2, ← gateLength]
                          simpa [circuitHeaderTokens,
                            circuitGatesPrefixTokens,
                            List.append_assoc] using
                            (CircuitTokenFailure.missingProgramEnd
                              inputs gates)
                      | cons next afterProgram =>
                          if programEndEq : next = .programEnd then
                            subst next
                            simp only at rejected
                            cases outputEq :
                                decodeSourceTokens afterProgram with
                            | none =>
                                rw [inputsShape, gateCountShape,
                                  gatesShape.2, ← gateLength]
                                simpa [circuitHeaderTokens,
                                  circuitGatesPrefixTokens,
                                  List.append_assoc] using
                                  (CircuitTokenFailure.output inputs gates
                                    ((decodeSourceTokens_eq_none_iff_failure
                                      afterProgram).mp outputEq))
                            | some outputPair =>
                                rcases outputPair with
                                  ⟨output, afterOutput⟩
                                rw [outputEq] at rejected
                                have outputShape :=
                                  (decodeSourceTokens_eq_some_iff
                                    afterProgram output afterOutput).mp
                                      outputEq
                                cases afterOutput with
                                | nil =>
                                    rw [inputsShape, gateCountShape,
                                      gatesShape.2, outputShape,
                                      ← gateLength]
                                    simpa [circuitOutputPrefixTokens,
                                      circuitGatesPrefixTokens,
                                      circuitHeaderTokens,
                                      List.append_assoc] using
                                      (CircuitTokenFailure.missingOutputsEnd
                                        inputs gates output)
                                | cons next afterOutputsEnd =>
                                    if outputsEndEq :
                                        next = .outputsEnd then
                                      subst next
                                      cases afterOutputsEnd with
                                      | nil =>
                                          rw [inputsShape,
                                            gateCountShape,
                                            gatesShape.2, outputShape,
                                            ← gateLength]
                                          simpa [circuitOutputPrefixTokens,
                                            circuitGatesPrefixTokens,
                                            circuitHeaderTokens,
                                            List.append_assoc] using
                                            (CircuitTokenFailure.missingInstanceEnd
                                              inputs gates output)
                                      | cons next afterInstanceEnd =>
                                          if instanceEndEq :
                                              next = .instanceEnd then
                                            subst next
                                            cases afterInstanceEnd with
                                            | nil =>
                                                simp at rejected
                                            | cons extra trailing =>
                                                rw [inputsShape,
                                                  gateCountShape,
                                                  gatesShape.2,
                                                  outputShape,
                                                  ← gateLength]
                                                simpa [circuitOutputPrefixTokens,
                                                  circuitGatesPrefixTokens,
                                                  circuitHeaderTokens,
                                                  List.append_assoc] using
                                                  (CircuitTokenFailure.trailingToken
                                                    inputs gates output
                                                    extra trailing)
                                          else
                                            rw [inputsShape,
                                              gateCountShape,
                                              gatesShape.2, outputShape,
                                              ← gateLength]
                                            simpa [circuitOutputPrefixTokens,
                                              circuitGatesPrefixTokens,
                                              circuitHeaderTokens,
                                              List.append_assoc] using
                                              (CircuitTokenFailure.wrongInstanceEnd
                                                inputs gates output next
                                                afterInstanceEnd instanceEndEq)
                                    else
                                      rw [inputsShape, gateCountShape,
                                        gatesShape.2, outputShape,
                                        ← gateLength]
                                      simpa [circuitOutputPrefixTokens,
                                        circuitGatesPrefixTokens,
                                        circuitHeaderTokens,
                                        List.append_assoc] using
                                        (CircuitTokenFailure.wrongOutputsEnd
                                          inputs gates output next
                                          afterOutputsEnd outputsEndEq)
                          else
                            rw [inputsShape, gateCountShape,
                              gatesShape.2, ← gateLength]
                            simpa [circuitHeaderTokens,
                              circuitGatesPrefixTokens,
                              List.append_assoc] using
                              (CircuitTokenFailure.wrongProgramEnd
                                inputs gates next afterProgram
                                programEndEq)
        else
          exact .wrongVersion token afterVersion versionEq
  · intro failure
    cases failure with
    | missingVersion => rfl
    | wrongVersion token suffix notVersion =>
        cases token <;>
          simp [decodeCircuitTokens] at notVersion ⊢
    | inputCount failure =>
        simp [decodeCircuitTokens,
          failure.decodeNatTokens_eq_none]
    | gateCount inputs failure =>
        simp [decodeCircuitTokens,
          decodeNatTokens_encodeNatTokens_append,
          failure.decodeNatTokens_eq_none]
    | gates inputs gateCount failure =>
        simp [circuitHeaderTokens, decodeCircuitTokens,
          List.append_assoc,
          decodeNatTokens_encodeNatTokens_append,
          failure.decodeNGatesTokens_eq_none]
    | missingProgramEnd inputs gates =>
        simp [circuitGatesPrefixTokens, circuitHeaderTokens,
          decodeCircuitTokens, List.append_assoc,
          decodeNatTokens_encodeNatTokens_append,
          decodeNGatesTokens_encodeGateListTokens]
    | wrongProgramEnd inputs gates token suffix notProgramEnd =>
        cases token <;>
          simp [circuitGatesPrefixTokens, circuitHeaderTokens,
            decodeCircuitTokens, List.append_assoc,
            decodeNatTokens_encodeNatTokens_append,
            decodeNGatesTokens_encodeGateListTokens_append] at *
    | output inputs gates failure =>
        simp [circuitGatesPrefixTokens, circuitHeaderTokens,
          decodeCircuitTokens, List.append_assoc,
          decodeNatTokens_encodeNatTokens_append,
          decodeNGatesTokens_encodeGateListTokens_append,
          failure.decodeSourceTokens_eq_none]
    | missingOutputsEnd inputs gates output =>
        simp [circuitOutputPrefixTokens, circuitGatesPrefixTokens,
          circuitHeaderTokens, decodeCircuitTokens, List.append_assoc,
          decodeNatTokens_encodeNatTokens_append,
          decodeNGatesTokens_encodeGateListTokens_append,
          decodeSourceTokens_encodeSourceTokens]
    | wrongOutputsEnd inputs gates output token suffix
        notOutputsEnd =>
        cases token <;>
          simp [circuitOutputPrefixTokens, circuitGatesPrefixTokens,
            circuitHeaderTokens, decodeCircuitTokens, List.append_assoc,
            decodeNatTokens_encodeNatTokens_append,
            decodeNGatesTokens_encodeGateListTokens_append,
            decodeSourceTokens_encodeSourceTokens_append] at *
    | missingInstanceEnd inputs gates output =>
        simp [circuitOutputPrefixTokens, circuitGatesPrefixTokens,
          circuitHeaderTokens, decodeCircuitTokens, List.append_assoc,
          decodeNatTokens_encodeNatTokens_append,
          decodeNGatesTokens_encodeGateListTokens_append,
          decodeSourceTokens_encodeSourceTokens_append]
    | wrongInstanceEnd inputs gates output token suffix
        notInstanceEnd =>
        cases token <;>
          simp [circuitOutputPrefixTokens, circuitGatesPrefixTokens,
            circuitHeaderTokens, decodeCircuitTokens, List.append_assoc,
            decodeNatTokens_encodeNatTokens_append,
            decodeNGatesTokens_encodeGateListTokens_append,
            decodeSourceTokens_encodeSourceTokens_append] at *
    | trailingToken inputs gates output token suffix =>
        simp [circuitOutputPrefixTokens, circuitGatesPrefixTokens,
          circuitHeaderTokens, decodeCircuitTokens, List.append_assoc,
          decodeNatTokens_encodeNatTokens_append,
          decodeNGatesTokens_encodeGateListTokens_append,
          decodeSourceTokens_encodeSourceTokens_append]

end PNP.Concrete.LockedNAND.SourceParser
