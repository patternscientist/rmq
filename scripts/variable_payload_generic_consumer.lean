import RMQ.Core.EncodingVariableLowerBound

namespace RMQ.VariablePayloadGenericConsumer

theorem genericBoundConsumer (n B : Nat) (E : ExactRMQBoundedEncoding n B) :
    EncodingLowerBound.doubledLogSlackLower n <= 2 * (B + 1) :=
  ExactRMQBoundedEncoding.doubledLogSlackLower_le E

theorem genericCountConsumer (n B : Nat) (E : ExactRMQBoundedEncoding n B) :
    Cartesian.shapeCount n <= 2 ^ (B + 1) - 1 :=
  ExactRMQBoundedEncoding.shapeCount_le E

theorem genericExactnessConsumer (n B : Nat) (E : ExactRMQBoundedEncoding n B)
    (xs : List Int) (hs : xs.length = n) (left len : Nat)
    (hp : 0 < len) (hb : left + len <= n) :
    E.query (E.encode xs) left (left + len) = some (scanWindow xs left len) :=
  E.query_exact xs hs left len hp hb

theorem emptyDomain : Nonempty (ExactRMQBoundedEncoding 0 0) :=
  ⟨ExactRMQBoundedEncoding.emptyEncoding⟩

theorem sizeOnlyAdviceAccepted :
    ExactRMQBoundedEncoding.singletonEncoding.query [] 0 1 = some 0 := rfl

theorem everySizeHasAnInput (n : Nat) : ∃ xs : List Int, xs.length = n :=
  ⟨List.replicate n 0, by simp⟩

theorem nullDecoderRejected (n B : Nat) (E : ExactRMQBoundedEncoding n B)
    (hn : 0 < n) (hnull : ∀ bits left right, E.query bits left right = none) : False :=
  E.null_decoder_impossible hn hnull

theorem wrongDecoderRejected (B : Nat) (E : ExactRMQBoundedEncoding 2 B)
    (hwrong : E.query (E.encode [7, 7]) 0 2 = some 1) : False := by
  rw [E.equal_key_leftmost] at hwrong
  cases hwrong

/-- Fixing one input as uncounted advice cannot satisfy the original uniform
exactness proposition on the empty payload. Quantifiers match query_exact. -/
theorem inputAdviceRejected (advice : List Int)
    (hexact : ∀ xs : List Int, xs.length = 2 →
      ∀ left len, 0 < len → left + len ≤ 2 →
        some (scanWindow advice left (left + len - left)) =
          some (scanWindow xs left len)) : False :=
  ExactRMQBoundedEncoding.constant_payload_exactness_impossible
    (fun _ left right => some (scanWindow advice left (right - left))) hexact

/-- Replacing input advice by its shape representative does not evade the same
fixed-decoder exactness contract. The shape is fixed across all size-two inputs. -/
theorem shapeAdviceRejected (advice : Cartesian.CartesianShape)
    (hexact : ∀ xs : List Int, xs.length = 2 →
      ∀ left len, 0 < len → left + len ≤ 2 →
        some (scanWindow advice.representative left (left + len - left)) =
          some (scanWindow xs left len)) : False :=
  inputAdviceRejected advice.representative hexact

end RMQ.VariablePayloadGenericConsumer
