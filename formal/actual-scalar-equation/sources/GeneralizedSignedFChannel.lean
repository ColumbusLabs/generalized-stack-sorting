import GeneralizedSignedKChannel

namespace StackSorting.Generalized.Decorated
namespace SignedCompletion
open StackSorting.FiniteGraph StackSorting.SignedWord UnarySuffix

theorem evalCount_F_exceptional {pre : State} (hp : ThreeLetters pre)
    (q : Nat) (a : Letter) (n : Nat) :
    evalCount pre n (F (List.replicate q .t ++ [a])) =
      optionalCount pre (f0 (decodeWord (List.replicate q .t ++ [a]))) n := by
  simp only [decodeWord_append, decodeWord_replicate, decodeWord_cons, decodeWord_nil,
    letterFactor, f0_exceptional_word, optionalCount]
  cases a with
  | z =>
    unfold evalCount
    rw [F_exceptional_z]
    simp only [decodeWord_append, decodeWord_replicate, decodeWord_cons, decodeWord_nil,
      letterFactor, exceptionalF0]
  | b =>
    have h := F_exceptional_b (fun word => (completionCount (pre ++ decodeWord word) n : Int)) q
    change evalCount pre n (F (List.replicate q .t ++ [.b])) =
      (completionCount (pre ++ [.C (q+1)]) n : Int)
    change evalCount pre n (F (List.replicate q .t ++ [.b])) =
      (completionCount (pre ++ decodeWord (List.replicate (q+1) .b)) n : Int) -
        evalCount pre n (lambdaPow (q+1)) at h
    rw [evalCount_lambdaPow hp] at h
    simp only [decodeWord_replicate, letterFactor] at h
    omega
  | t =>
    have hw : List.replicate q Letter.t ++ [.t] = List.replicate (q+1) .t := List.replicate_succ'.symm
    unfold evalCount
    rw [hw, F_pure_t]
    simp only [decodeWord_replicate, letterFactor, exceptionalF0]

/-- The exact finite signed F polynomial counts the actual state-zero suffix
image in every unary prefix context. Exceptional negative coefficients are
justified by the independently established actual-output clause valuation. -/
theorem evalCount_F {pre : State} (hp : ThreeLetters pre) (word : Word) (n : Nat) :
    evalCount pre n (F word) = optionalCount pre (f0 (decodeWord word)) n := by
  induction word generalizing pre with
  | nil => simp [F, f0, optionalCount]
  | cons a rest ih =>
    cases he : exceptional (decodeWord (a :: rest)) with
    | some pair =>
      obtain ⟨q, factor⟩ := pair
      rcases exceptional_terminal (decodeWord_three (a :: rest)) he with rfl | rfl | rfl
      · have hw := exceptional_decode (a := .z) he
        rw [hw]
        exact evalCount_F_exceptional hp q .z n
      · have hw := exceptional_decode (a := .b) he
        rw [hw]
        exact evalCount_F_exceptional hp q .b n
      · have hw := exceptional_decode (a := .t) he
        rw [hw]
        exact evalCount_F_exceptional hp q .t n
    | none =>
      cases a with
      | z =>
        change exceptional (.Z :: decodeWord rest) = none at he
        have hf : f0 (decodeWord (.z :: rest)) = prepend .Z (f1 (decodeWord rest)) := by
          simp only [decodeWord_cons, letterFactor, f0, he]
        rw [F, evalCount_prefix, hf, optionalCount_prepend]
        exact evalCount_J pre rest n
      | b =>
        change exceptional (.B :: decodeWord rest) = none at he
        have hf : f0 (decodeWord (.b :: rest)) = prepend .Z (union01 (decodeWord rest)) := by
          cases hr : exceptional (decodeWord rest) <;>
            simp only [decodeWord_cons, letterFactor, f0, he, union01, hr]
        have hpz := threeLetters_append hp (threeLetters_single (Or.inl rfl))
        rw [F, evalCount_append, evalCount_prefix, evalCount_prefix, hf, optionalCount_prepend]
        change evalCount (pre ++ [.Z]) n (F rest) + evalCount (pre ++ [.Z]) n (K rest) = _
        rw [ih hpz, evalCount_K hpz]
        omega
      | t =>
        change exceptional (.T :: decodeWord rest) = none at he
        have hn := exceptional_T_none he
        have hk := K_of_no_exceptional hn.2
        have hf : f0 (decodeWord (.t :: rest)) = prepend .B (f0 (decodeWord rest)) := by
          simp only [decodeWord_cons, letterFactor, f0, he]
        rw [F, hk, prefix_nil, List.append_nil, evalCount_prefix, hf, optionalCount_prepend]
        exact ih (threeLetters_append hp (threeLetters_single (Or.inr (Or.inl rfl))))

/-- U is the exact union suffix counting map, with its multiplicities and
subtractions justified by actual distinct-output count identities. -/
theorem evalCount_U {pre : State} (hp : ThreeLetters pre) (word : Word) (n : Nat) :
    evalCount pre n (U word) = optionalCount pre (union01 (decodeWord word)) n := by
  rw [U, evalCount_append, evalCount_F hp, evalCount_K hp]
  omega

#print axioms evalCount_F
#print axioms evalCount_U
end SignedCompletion
end StackSorting.Generalized.Decorated
