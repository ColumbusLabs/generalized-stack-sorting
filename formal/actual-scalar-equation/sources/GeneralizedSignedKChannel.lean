import GeneralizedSignedJChannel

namespace StackSorting.Generalized.Decorated
namespace SignedCompletion
open StackSorting.FiniteGraph StackSorting.SignedWord UnarySuffix

theorem f0_exceptional_word (q : Nat) (factor : Factor) :
    f0 (List.replicate q .T ++ [factor]) = some (exceptionalF0 q factor) :=
  f0_exceptional (exceptional_word q factor)

theorem union01_exceptional_word (q : Nat) (factor : Factor) :
    union01 (List.replicate q .T ++ [factor]) = some (exceptionalU q factor) := by
  simp only [union01, exceptional_word]

theorem K_of_no_exceptional {word : Word}
    (he : exceptional (decodeWord word) = none) : K word = [] := by
  rcases K_support word with hk | ⟨q, hw⟩
  · exact hk
  · have hx : exceptional (decodeWord word) = some (q, .B) := by
      rw [hw]
      simp only [decodeWord_append, decodeWord_replicate, decodeWord_cons,
        decodeWord_nil, letterFactor, exceptional_word]
    rw [he] at hx
    cases hx

/-- K is precisely the count difference U-F, justified by actual terminal
clause valuation on its only nonzero exceptional suffix. -/
theorem evalCount_K {pre : State} (hp : ThreeLetters pre) (word : Word) (n : Nat) :
    evalCount pre n (K word) =
      optionalCount pre (union01 (decodeWord word)) n -
        optionalCount pre (f0 (decodeWord word)) n := by
  cases he : exceptional (decodeWord word) with
  | none =>
    rw [K_of_no_exceptional he]
    simp only [evalCount_nil, union01, he, Int.sub_self]
  | some pair =>
    obtain ⟨q, factor⟩ := pair
    have hf := exceptional_terminal (decodeWord_three word) he
    rcases hf with rfl | rfl | rfl
    · have hw := exceptional_decode (a := .z) he
      rw [hw, K_exceptional_z]
      simp only [evalCount_nil, decodeWord_append, decodeWord_replicate, decodeWord_cons,
        decodeWord_nil, letterFactor, f0_exceptional_word, union01_exceptional_word,
        exceptionalF0, exceptionalU, Int.sub_self]
    · have hw := exceptional_decode (a := .b) he
      rw [hw, K_exceptional_b]
      simp only [decodeWord_append, decodeWord_replicate, decodeWord_cons,
        decodeWord_nil, letterFactor, f0_exceptional_word, union01_exceptional_word,
        exceptionalF0, exceptionalU, optionalCount]
      exact evalCount_lambdaPow hp (q+1) n
    · have hw := exceptional_decode (a := .t) he
      rw [hw]
      have hk : K (List.replicate q .t ++ [.t]) = [] := by
        rw [← List.replicate_succ']
        exact K_pure_t (q+1)
      rw [hk]
      simp only [evalCount_nil, decodeWord_append, decodeWord_replicate, decodeWord_cons,
        decodeWord_nil, letterFactor, f0_exceptional_word, union01_exceptional_word,
        exceptionalF0, exceptionalU, Int.sub_self]

#print axioms evalCount_K
end SignedCompletion
end StackSorting.Generalized.Decorated
