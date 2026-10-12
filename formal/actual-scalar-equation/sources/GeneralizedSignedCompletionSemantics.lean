import GeneralizedUnaryCountReductions
import GeneralizedCompletionCongruence
import SignedWordAlgebra

/-! Literal actual-completion evaluation of the finite signed suffix words.
The only subtractive channel is interpreted using the independently proved
terminal-clause valuation, not by subtracting physical histories. -/
namespace StackSorting.Generalized.Decorated
namespace SignedCompletion
open StackSorting.FiniteGraph
open StackSorting.SignedWord
open UnarySuffix

def letterFactor : Letter → Factor
  | .z => .Z
  | .b => .B
  | .t => .T

def decodeWord (word : Word) : State := word.map letterFactor

@[simp] theorem decodeWord_nil : decodeWord [] = [] := rfl
@[simp] theorem decodeWord_cons (a : Letter) (word : Word) :
    decodeWord (a :: word) = letterFactor a :: decodeWord word := rfl

@[simp] theorem decodeWord_append (left right : Word) :
    decodeWord (left ++ right) = decodeWord left ++ decodeWord right := List.map_append

@[simp] theorem decodeWord_replicate (n : Nat) (a : Letter) :
    decodeWord (List.replicate n a) = List.replicate n (letterFactor a) := List.map_replicate

theorem decodeWord_three (word : Word) : ThreeLetters (decodeWord word) := by
  intro factor hm
  obtain ⟨letter, _, rfl⟩ := List.mem_map.mp hm
  cases letter <;> simp [letterFactor]

noncomputable def evalCount (pre : State) (n : Nat) (poly : Poly) : Int :=
  eval (fun word => (completionCount (pre ++ decodeWord word) n : Int)) poly

@[simp] theorem evalCount_nil (pre : State) (n : Nat) : evalCount pre n [] = 0 := rfl

@[simp] theorem evalCount_one (pre : State) (n : Nat) :
    evalCount pre n one = (completionCount pre n : Int) := by
  simp [evalCount]

theorem evalCount_append (pre : State) (n : Nat) (left right : Poly) :
    evalCount pre n (left ++ right) = evalCount pre n left + evalCount pre n right :=
  eval_append _ _ _

theorem evalCount_prefix (pre : State) (n : Nat) (letter : Letter) (poly : Poly) :
    evalCount pre n (StackSorting.SignedWord.prefixLetter letter poly) =
      evalCount (pre ++ [letterFactor letter]) n poly := by
  unfold evalCount
  rw [eval_prefix]
  congr 1
  funext word
  simp only [decodeWord_cons, List.append_assoc, List.singleton_append]

theorem evalCount_difference (pre : State) (n : Nat) (poly : Poly) :
    evalCount pre n (difference poly) =
      evalCount (pre ++ [.B]) n poly - evalCount (pre ++ [.Z]) n poly := by
  unfold evalCount
  rw [eval_difference]
  congr 1 <;> congr 1 <;> funext word <;>
    simp only [decodeWord_cons, letterFactor, List.append_assoc, List.singleton_append]

theorem completionCount_clause_zero (pre : State) (n : Nat) :
    completionCount (pre ++ [.C 0]) n = 0 := by
  apply prefixed_count_of_no_coordinates
  intro digits hd
  have hc := (ExceptionalSuffix.denotes_single (.C 0) digits).mp hd
  have he : digits = [] := List.length_eq_zero_iff.mp hc.1
  subst digits
  exact List.not_mem_nil hc.2.2

/-- The exact signed power (b-z)^m evaluates to all binary completions minus
terminal-clause completions. This is proved for all lengths and all unary
prefixes using actual output inclusion-exclusion. -/
theorem evalCount_lambdaPow {pre : State} (hp : ThreeLetters pre) (m n : Nat) :
    evalCount pre n (lambdaPow m) =
      (completionCount (pre ++ List.replicate m .B) n : Int) -
        (completionCount (pre ++ [.C m]) n : Int) := by
  induction m generalizing pre with
  | zero => simp [lambdaPow, completionCount_clause_zero]
  | succ m ih =>
    rw [lambdaPow, evalCount_difference]
    have hb := ih (threeLetters_append hp (threeLetters_single (Or.inr (Or.inl rfl))))
    have hz := ih (threeLetters_append hp (threeLetters_single (Or.inl rfl)))
    rw [hb, hz]
    have step := completion_terminal_clause_step (show Unary pre from hp) m n
    simp only [List.append_assoc, List.singleton_append] at step ⊢
    rw [List.replicate_succ]
    omega

#print axioms evalCount_lambdaPow
end SignedCompletion
end StackSorting.Generalized.Decorated
