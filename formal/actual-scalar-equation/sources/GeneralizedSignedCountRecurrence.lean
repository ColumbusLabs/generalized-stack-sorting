import GeneralizedSignedFChannel
import GeneralizedCodeCountPartition
import SignedWordDeletion

/-! The literal accepted signed word recurrence for the actual unbounded
machine counts. The first-letter partition retains each held rank separately;
all target evaluations are the already proved physical/counting reductions. -/
namespace StackSorting.Generalized.Decorated
namespace SignedCompletion
open StackSorting.FiniteGraph StackSorting.SignedWord UnarySuffix

theorem evalCount_selected {pre : State} (hp : ThreeLetters pre)
    (a : Letter) (word : Word) (n : Nat) :
    evalCount pre n (selected a word) =
      optionalCount pre (afterSelected (letterFactor a) (decodeWord word)) n := by
  cases a with
  | z => exact evalCount_F hp word n
  | b => exact evalCount_U hp word n
  | t => exact evalCount_U hp word n

/-- Each H-rank fiber has the actual count of its exact signed successor,
with no merging of equal successor words belonging to different ranks. -/
theorem firstHeld_signed_count {pre : State} (hp : ThreeLetters pre)
    (a : Letter) (word : Word) (n : Nat)
    (hv : Valid (pre ++ decodeWord (a :: word))) :
    ((firstCodeTails (pre ++ decodeWord (a :: word)) n (.H (pre.length+1))).length : Int) =
      evalCount pre n (selected a word) := by
  have hf : letterFactor a = .Z ∨ letterFactor a = .B ∨ letterFactor a = .T := by
    cases a <;> simp [letterFactor]
  have hr := decodeWord_three word
  rw [evalCount_selected hp]
  cases he : afterSelected (letterFactor a) (decodeWord word) with
  | none =>
    have hempty : firstCodeTails (pre ++ decodeWord (a :: word)) n (.H (pre.length+1)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro code hm
      have reject := codeCompletion_held_reject hp hr hf
        (show appendOption pre (afterSelected (letterFactor a) (decodeWord word)) = none by
          simp only [appendOption, he, Option.map_none]) n code
      exact reject ((mem_firstCodeTails _ _ _ _).mp hm)
    simp only [hempty, List.length_nil, Int.natCast_zero, optionalCount]
  | some target =>
    have hsem := codeCompletion_held_target hp hr hf hv
      (show appendOption pre (afterSelected (letterFactor a) (decodeWord word)) = some (pre ++ target) by
        simp only [appendOption, he, Option.map_some]) n
    have hc := firstCodeTails_length_of_target (pre ++ decodeWord (a :: word)) (pre ++ target)
      n n (.H (pre.length+1)) hsem
    simp only [optionalCount]
    exact congrArg (fun count : Nat => (count : Int)) hc

/-- Summing H-rank fibers equals evaluation of the exact heldDelete polynomial,
including every internal coordinate with its original multiplicity. -/
theorem held_suffix_count {pre : State} (hp : ThreeLetters pre)
    (word : Word) (n : Nat) (hv : Valid (pre ++ decodeWord word)) :
    (((List.range' (pre.length+1) word.length).map (fun k =>
      ((firstCodeTails (pre ++ decodeWord word) n (.H k)).length : Int))).sum) =
      evalCount pre n (heldDelete word) := by
  induction word generalizing pre with
  | nil => simp [heldDelete]
  | cons a rest ih =>
    have hpa := threeLetters_append hp (threeLetters_single
      (show letterFactor a = .Z ∨ letterFactor a = .B ∨ letterFactor a = .T by
        cases a <;> simp [letterFactor]))
    have hva : Valid ((pre ++ [letterFactor a]) ++ decodeWord rest) := by
      simpa only [decodeWord_cons, List.append_assoc, List.singleton_append] using hv
    have tail := ih hpa hva
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.sum_cons]
    rw [firstHeld_signed_count hp a rest n hv]
    unfold evalCount at tail ⊢
    rw [heldDelete_cons_eval]
    congr 1
    simpa only [List.length_append, List.length_singleton, decodeWord_cons,
      List.append_assoc, List.singleton_append] using tail

theorem intCast_sum_map (xs : List α) (f : α → Nat) :
    (((xs.map f).sum : Nat) : Int) = (xs.map (fun x => (f x : Int))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Int.natCast_add, ih]

/-- Exact signed first-letter recurrence for every valid unary state. Its
coefficients are actual distinct outputs of the literal Run 3 3 machine. -/
theorem completionCount_signed_recurrence (word : Word) (n : Nat)
    (hv : Valid (decodeWord word)) :
    (completionCount (decodeWord word) n : Int) =
      (nilCodeContribution (decodeWord word) n : Int) +
        evalCount [] n (heldDelete word) +
        ((List.range' 1 n).map (fun batch =>
          (completionCount (appendHeld (decodeWord word) (batch-1)) (n-batch) : Int))).sum := by
  have hc := congrArg (fun count : Nat => (count : Int))
    (completionCount_first_letter (decodeWord word) n)
  simp only [Int.natCast_add, intCast_sum_map] at hc
  have hh : height (decodeWord word) = word.length := by
    rw [(decodeWord_three word).height]
    simp [decodeWord]
  have held := held_suffix_count (pre := []) (by intro a ha; cases ha) word n hv
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at held
  rw [hh, held] at hc
  exact hc

#print axioms firstHeld_signed_count
#print axioms held_suffix_count
#print axioms completionCount_signed_recurrence
end SignedCompletion
end StackSorting.Generalized.Decorated
