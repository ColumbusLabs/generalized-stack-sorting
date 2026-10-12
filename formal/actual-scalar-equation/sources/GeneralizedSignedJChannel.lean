import GeneralizedSignedCompletionSemantics

namespace StackSorting.Generalized.Decorated
namespace SignedCompletion
open StackSorting.FiniteGraph StackSorting.SignedWord UnarySuffix

theorem decodeWord_injective {left right : Word} (he : decodeWord left = decodeWord right) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons a left ih =>
    cases right with
    | nil => simp at he
    | cons other right =>
      have hs := List.cons.inj he
      have hab : a = other := by cases a <;> cases other <;> simp_all [letterFactor]
      subst other
      exact congrArg (a :: ·) (ih hs.2)

theorem exceptional_decode {word : Word} {q : Nat} {a : Letter}
    (he : exceptional (decodeWord word) = some (q, letterFactor a)) :
    word = List.replicate q .t ++ [a] := by
  apply decodeWord_injective
  have hs := exceptional_shape he
  simpa only [decodeWord_append, decodeWord_replicate, decodeWord_cons, decodeWord_nil,
    letterFactor] using hs

theorem f1_exceptional (q : Nat) (factor : Factor) :
    f1 (List.replicate q .T ++ [factor]) =
      some (List.replicate q .O ++ [ExceptionalSuffix.terminal factor]) := by
  have hn : List.replicate q Factor.T ++ [factor] ≠ [] := by simp
  have hm : ∀ state : State, state ≠ [] → f1 state =
      (exceptional state).map (fun pair => List.replicate pair.1 .O ++ [ExceptionalSuffix.terminal pair.2]) := by
    intro state hn
    cases state with
    | nil => exact (hn rfl).elim
    | cons a rest => rfl
  rw [hm _ hn, exceptional_word]
  rfl

theorem f0_exceptional {state : State} {q : Nat} {factor : Factor}
    (he : exceptional state = some (q, factor)) : f0 state = some (exceptionalF0 q factor) := by
  cases state with
  | nil => simp [exceptional] at he
  | cons a rest => simp only [f0, he]

theorem evalCount_J_exceptional (pre : State) (q : Nat) (a : Letter) (n : Nat) :
    evalCount (pre ++ [.Z]) n (J (List.replicate q .t ++ [a])) =
      optionalCount (pre ++ [.Z]) (f1 (decodeWord (List.replicate q .t ++ [a]))) n := by
  simp only [decodeWord_append, decodeWord_replicate, decodeWord_cons, decodeWord_nil,
    letterFactor, f1_exceptional, optionalCount]
  have horun (last : Factor) := one_run_completion_count pre q last n
  cases a with
  | z =>
    unfold evalCount
    rw [J_exceptional_z]
    simp only [decodeWord_replicate, letterFactor, ExceptionalSuffix.terminal,
      List.append_assoc, List.singleton_append]
    rw [horun]
    have hr : List.replicate (q+1) Factor.Z ++ [.Z] = .Z :: List.replicate (q+1) .Z := by
      rw [← List.replicate_succ', List.replicate_succ]
    rw [List.append_assoc, hr]
  | b =>
    unfold evalCount
    rw [J_exceptional_b]
    simp only [decodeWord_append, decodeWord_replicate, decodeWord_cons, decodeWord_nil,
      letterFactor, ExceptionalSuffix.terminal, List.append_assoc, List.singleton_append]
    rw [horun]
    simp only [List.append_assoc, List.replicate_succ, List.cons_append]
  | t =>
    have hw : List.replicate q Letter.t ++ [.t] = List.replicate (q+1) .t := List.replicate_succ'.symm
    unfold evalCount
    rw [hw, J_pure_t_succ]
    simp only [decodeWord_append, decodeWord_replicate, decodeWord_cons, decodeWord_nil,
      letterFactor, ExceptionalSuffix.terminal, List.append_assoc, List.singleton_append]
    rw [horun]
    simp only [List.append_assoc, List.replicate_succ, List.cons_append]

/-- The J surrogate is used only after its required leading Z. It counts
exactly the old state-one suffix image after the proved single-run bijection. -/
theorem evalCount_J (pre : State) (word : Word) (n : Nat) :
    evalCount (pre ++ [.Z]) n (J word) =
      optionalCount (pre ++ [.Z]) (f1 (decodeWord word)) n := by
  cases word with
  | nil => simp [J, f1, optionalCount]
  | cons a rest =>
    cases he : exceptional (decodeWord (a :: rest)) with
    | none =>
      have hj : J (a :: rest) = [] := by
        rcases J_support (a :: rest) with hj | hj
        · exact hj
        · rcases hj with he | ⟨q, last, hw⟩
          · cases he
          · have hx : exceptional (decodeWord (a :: rest)) = some (q, letterFactor last) := by
              rw [hw]
              simp only [decodeWord_append, decodeWord_replicate, decodeWord_cons,
                decodeWord_nil, letterFactor, exceptional_word]
            rw [he] at hx
            cases hx
      change exceptional (letterFactor a :: decodeWord rest) = none at he
      simp only [hj, evalCount_nil, decodeWord_cons, f1, he, Option.map_none, optionalCount]
    | some pair =>
      obtain ⟨q, factor⟩ := pair
      have hf := exceptional_terminal (decodeWord_three (a :: rest)) he
      rcases hf with rfl | rfl | rfl
      · have hw := exceptional_decode (a := .z) he
        rw [hw]
        exact evalCount_J_exceptional pre q .z n
      · have hw := exceptional_decode (a := .b) he
        rw [hw]
        exact evalCount_J_exceptional pre q .b n
      · have hw := exceptional_decode (a := .t) he
        rw [hw]
        exact evalCount_J_exceptional pre q .t n

#print axioms evalCount_J
end SignedCompletion
end StackSorting.Generalized.Decorated
