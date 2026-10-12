import GeneralizedCountRecurrenceUniqueness
import GeneralizedSignedFPSCoefficients

/-! Exact finite record-batch extraction. The series relation is used only as
a formal resolvent identity and will be instantiated with literal matrices. -/
namespace StackSorting.Generalized.Decorated.SignedCompletion
open StackSorting.SignedWord StackSorting.CauchyRing StackSorting.FiniteGraph

noncomputable def wordRecordCoeff (phi : Word → FPS) : Word → Nat → Rat
  | _, 0 => 0
  | word, n+1 => phi word n + wordRecordCoeff phi (pushWord word) n

theorem wordRecordCoeff_eq_sum (phi : Word → FPS) (word : Word) (n : Nat) :
    wordRecordCoeff phi word n =
      ((List.range' 1 n).map (fun batch =>
        phi (appendWord word (batch-1)) (n-batch))).sum := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih =>
    simp only [wordRecordCoeff, List.range'_succ, List.map_cons, List.sum_cons,
      Nat.add_sub_cancel, Nat.sub_self, appendWord]
    rw [ih]
    congr 1
    rw [List.range'_succ_left (s := 1), List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro batch hb
    have hpositive := (List.mem_range'_1.mp hb).1
    cases batch with
    | zero => omega
    | succ batch => simp [appendWord, Nat.add_sub_add_right]

theorem formal_record_coefficients (phi gamma : Word → FPS)
    (hrec : ∀ word, Valid (decodeWord word) →
      gamma word = phi word + X*gamma (pushWord word))
    (word : Word) (hv : Valid (decodeWord word)) (n : Nat) :
    (X*gamma word) n =
      ((List.range' 1 n).map (fun batch =>
        phi (appendWord word (batch-1)) (n-batch))).sum := by
  rw [←wordRecordCoeff_eq_sum]
  induction n generalizing word with
  | zero => exact congrFun (X_mul_coeff (gamma word)) 0
  | succ n ih =>
    have hx := congrFun (X_mul_coeff (gamma word)) (n+1)
    change (X*gamma word) (n+1)=gamma word n at hx
    rw [hx, hrec word hv]
    change phi word n+(X*gamma (pushWord word)) n =
      phi word n+wordRecordCoeff phi (pushWord word) n
    rw [ih (pushWord word) (by
      rw [decodeWord_pushWord]
      exact push_valid hv)]

theorem formal_series_recurrence_coefficients (phi gamma : Word → FPS)
    (hrec : ∀ word, Valid (decodeWord word) →
      gamma word = phi word + X*gamma (pushWord word))
    (heq : ∀ word, Valid (decodeWord word) →
      phi word = (if word=[] then 1 else 0) +
        eval phi (heldDelete word) + X*gamma word) :
    CountRecurrence (fun word n => phi word n) := by
  intro word n hv
  have h := congrArg (fun value : FPS => value n) (heq word hv)
  rw [add_apply, add_apply, eval_coefficient,
    formal_record_coefficients phi gamma hrec word hv n] at h
  have hn : ((if word=[] then (1 : FPS) else 0) n) = (nilWordContribution word n : Rat) := by
    unfold nilWordContribution
    by_cases hw : word=[]
    · subst word
      simp only [ite_true, true_and]
      rfl
    · simp only [hw, ite_false, false_and]
      change StackSorting.CauchyRing.const 0 n = (0 : Rat)
      unfold StackSorting.CauchyRing.const
      split <;> rfl
  rw [hn] at h
  exact h

#print axioms formal_record_coefficients
#print axioms formal_series_recurrence_coefficients
end StackSorting.Generalized.Decorated.SignedCompletion
