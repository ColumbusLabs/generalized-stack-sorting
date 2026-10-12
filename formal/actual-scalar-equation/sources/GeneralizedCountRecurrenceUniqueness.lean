import GeneralizedSignedCountRecurrence
import GeneralizedUnaryValidity
import SignedWordSupport

/-! Decreasing-measure uniqueness for the literal actual-count recurrence.
The competitor is arbitrary and ring-valued. Its recurrence remains an explicit
hypothesis, independently of the physical counting theorem. -/
namespace StackSorting.Generalized.Decorated
namespace SignedCompletion
open StackSorting.FiniteGraph StackSorting.SignedWord UnarySuffix
attribute [local instance] Lean.Grind.Ring.intCast
set_option linter.unusedSimpArgs false

/-- The exact appended coordinate at held heights zero, one, and at least two. -/
def pushLetter (h : Nat) : Letter := if h = 0 then .z else if h = 1 then .b else .t

def pushWord (word : Word) : Word := word ++ [pushLetter word.length]

def appendWord (word : Word) : Nat → Word
  | 0 => word
  | count+1 => appendWord (pushWord word) count

@[simp] theorem height_decodeWord (word : Word) : height (decodeWord word) = word.length := by
  rw [(decodeWord_three word).height]
  simp [decodeWord]

@[simp] theorem letterFactor_pushLetter (h : Nat) : letterFactor (pushLetter h) = pushFactor h := by
  unfold pushLetter pushFactor
  split <;> (try split) <;> rfl

@[simp] theorem decodeWord_pushWord (word : Word) : decodeWord (pushWord word) = push (decodeWord word) := by
  simp [pushWord, push]

/-- Word appending is exactly the physical record-batch state operation. -/
@[simp] theorem decodeWord_appendWord (word : Word) (count : Nat) :
    decodeWord (appendWord word count) = appendHeld (decodeWord word) count := by
  induction count generalizing word with
  | zero => rfl
  | succ count ih => simpa only [appendWord, appendHeld, decodeWord_pushWord] using ih (pushWord word)

@[simp] theorem pushWord_length (word : Word) : (pushWord word).length = word.length+1 := by
  simp [pushWord]

@[simp] theorem appendWord_length (word : Word) (count : Nat) :
    (appendWord word count).length = word.length+count := by
  induction count generalizing word with
  | zero => rfl
  | succ count ih =>
    simp only [appendWord, ih, pushWord_length]
    omega

/-- Once two coordinates are held, every further coordinate is T. -/
theorem appendWord_of_two_le (word : Word) (count : Nat) (hw : 2 ≤ word.length) :
    appendWord word count = word ++ List.replicate count .t := by
  induction count generalizing word with
  | zero => simp [appendWord]
  | succ count ih =>
    have hz : word.length ≠ 0 := by omega
    have ho : word.length ≠ 1 := by omega
    have hp : pushWord word = word ++ [.t] := by simp [pushWord, pushLetter, hz, ho]
    have hb : 2 ≤ (word ++ [Letter.t]).length := by simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have hi := ih (word ++ [Letter.t]) hb
    rw [appendWord, hp, hi]
    simp [List.replicate_succ, List.append_assoc]

@[simp] theorem appendWord_empty_zero : appendWord [] 0 = [] := rfl
@[simp] theorem appendWord_empty_one : appendWord [] 1 = [.z] := rfl

theorem appendWord_empty_add_two (count : Nat) :
    appendWord [] (count+2) = [.z,.b] ++ List.replicate count .t := by
  change appendWord [.z,.b] count = _
  exact appendWord_of_two_le [.z,.b] count (by decide)

theorem appendWord_singleton_z_succ (count : Nat) :
    appendWord [.z] (count+1) = [.z,.b] ++ List.replicate count .t := by
  change appendWord [.z,.b] count = _
  exact appendWord_of_two_le [.z,.b] count (by decide)

theorem appendWord_valid {word : Word} (hv : Valid (decodeWord word)) (count : Nat) :
    Valid (decodeWord (appendWord word count)) := by
  rw [decodeWord_appendWord]
  exact appendHeld_valid hv count

/-- Bridge from physical coordinate validity to the signed-word boundary. -/
theorem admissibleWord_of_valid {word : Word} (hv : Valid (decodeWord word)) : AdmissibleWord word := by
  cases word with
  | nil => exact Or.inl rfl
  | cons a word =>
    have ha := valid_unary_first (decodeWord_three (a::word)) hv
    cases a with
    | b => simp [letterFactor] at ha
    | t => simp [letterFactor] at ha
    | z =>
      cases word with
      | nil => exact Or.inr (Or.inl rfl)
      | cons a word =>
        have hb := valid_unary_second (decodeWord_three (.z::a::word)) hv
        cases a with
        | z => exact Or.inr (Or.inr ⟨.z, word, Or.inl rfl, rfl⟩)
        | b => exact Or.inr (Or.inr ⟨.b, word, Or.inr rfl, rfl⟩)
        | t => simp [letterFactor] at hb

theorem valid_of_admissibleWord {word : Word} (ha : AdmissibleWord word) : Valid (decodeWord word) := by
  apply boundary_valid
  rcases ha with rfl | rfl | ⟨a, rest, ha, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr ⟨letterFactor a, decodeWord rest, ?_, rfl, decodeWord_three rest⟩)
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem valid_decodeWord_iff (word : Word) : Valid (decodeWord word) ↔ AdmissibleWord word :=
  ⟨admissibleWord_of_valid, valid_of_admissibleWord⟩

/-- Every raw term is still in the genuine valid domain; no cancellation or
support normalization is used for the induction. -/
theorem heldDelete_valid {word : Word} (hv : Valid (decodeWord word))
    (term : Int × Word) (hm : term ∈ heldDelete word) : Valid (decodeWord term.2) :=
  valid_of_admissibleWord (heldDelete_admissible (admissibleWord_of_valid hv) term hm)

variable {R : Type} [Lean.Grind.CommRing R]

/-- The sole empty-code coefficient, with all boundary cases explicit. -/
def nilWordContribution (word : Word) (n : Nat) : R :=
  if word = [] ∧ n = 0 then 1 else 0

theorem nilCodeContribution_decodeWord (word : Word) (n : Nat) :
    nilCodeContribution (decodeWord word) n = if word = [] ∧ n = 0 then 1 else 0 := by
  classical
  by_cases he : word = [] ∧ n = 0
  · rcases he with ⟨rfl, rfl⟩
    have hr : Represents [] [] := ⟨[], rfl, rfl⟩
    simp [nilCodeContribution, height, hr]
  · have hp : 0 < height (decodeWord word)+n := by
      rw [height_decodeWord]
      have hn : word.length ≠ 0 ∨ n ≠ 0 := by
        by_cases hw : word = []
        · exact Or.inr (by intro hn; exact he ⟨hw, hn⟩)
        · exact Or.inl (by intro hl; exact hw (List.length_eq_zero_iff.mp hl))
      omega
    rw [nilCodeContribution_of_positive _ _ hp]
    simp [he]

/-- Explicit recurrence hypothesis for an independently defined candidate.
This is not an assumption about the actual machine count. -/
def CountRecurrence (f : Word → Nat → R) : Prop :=
  ∀ word n, Valid (decodeWord word) →
    f word n = nilWordContribution word n +
      eval (fun next => f next n) (heldDelete word) +
      ((List.range' 1 n).map (fun batch => f (appendWord word (batch-1)) (n-batch))).sum

/-- Both kinds of successors have exactly one fewer unit of total supply. -/
theorem record_measure_decreases (word : Word) (n batch : Nat)
    (hm : batch ∈ List.range' 1 n) :
    (appendWord word (batch-1)).length + (n-batch) + 1 = word.length+n := by
  have hb := List.mem_range'_1.mp hm
  rw [appendWord_length]
  omega

/-- Strong induction on held height plus unread supply proves uniqueness on
all valid words, without any finite-height cutoff or integrality assumption. -/
theorem countRecurrence_unique (f g : Word → Nat → R)
    (hf : CountRecurrence f) (hg : CountRecurrence g)
    (word : Word) (n : Nat) (hv : Valid (decodeWord word)) : f word n = g word n := by
  have all : ∀ size : Nat, ∀ word n, word.length+n = size →
      Valid (decodeWord word) → f word n = g word n := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
      intro word n he hv
      rw [hf word n hv, hg word n hv]
      have hh : eval (fun next => f next n) (heldDelete word) =
          eval (fun next => g next n) (heldDelete word) := by
        apply eval_congr_on_support
        intro term hm
        have hl := heldDelete_length word term hm
        exact ih (term.2.length+n) (by omega) term.2 n rfl (heldDelete_valid hv term hm)
      have hr : ((List.range' 1 n).map (fun batch => f (appendWord word (batch-1)) (n-batch))) =
          ((List.range' 1 n).map (fun batch => g (appendWord word (batch-1)) (n-batch))) := by
        apply List.map_congr_left
        intro batch hm
        have hl := record_measure_decreases word n batch hm
        exact ih _ (by omega) _ _ rfl (appendWord_valid hv (batch-1))
      rw [hh, hr]
  exact all (word.length+n) word n rfl hv

/-- A candidate recurrence already forces the unique empty boundary. -/
theorem countRecurrence_empty_zero (f : Word → Nat → R) (hf : CountRecurrence f) :
    f [] 0 = 1 := by
  have h := hf [] 0 empty_valid
  change f [] 0 = (1:R) + 0 + 0 at h
  grind

/-- Negative control as a theorem: deleting the boundary coefficient cannot
satisfy the stated recurrence, even though the all-zero family is rational. -/
theorem zero_not_CountRecurrence : ¬ CountRecurrence (fun _ _ => (0 : Rat)) := by
  intro h
  have bad := countRecurrence_empty_zero (fun _ _ => (0 : Rat)) h
  exact (by decide : (0 : Rat) ≠ 1) bad

/-- List sums commute with the ordinary embedding of integers into rationals. -/
theorem ratCast_sum_map (xs : List α) (f : α → Int) :
    ((((xs.map f).sum) : Int) : Rat) = (xs.map (fun x => (f x : Rat))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Rat.intCast_add, ih]

/-- The same embedding commutes termwise with the signed evaluator, retaining
negative coefficients and repeated words exactly. -/
theorem ratCast_eval (f : Word → Int) (poly : Poly) :
    ((eval f poly : Int) : Rat) = eval (fun word => (f word : Rat)) poly := by
  induction poly with
  | nil => rfl
  | cons term poly ih =>
    change (((term.1 * f term.2 + eval f poly : Int) : Rat)) =
      (term.1 : Rat) * (f term.2 : Rat) + eval (fun word => (f word : Rat)) poly
    rw [Rat.intCast_add, Rat.intCast_mul, ih]

noncomputable def actualCountRat (word : Word) (n : Nat) : Rat :=
  (completionCount (decodeWord word) n : Rat)

/-- The unconditional integer counting theorem lifts to a rational recurrence;
there is no candidate recurrence or candidate integrality premise here. -/
theorem actualCountRat_recurrence : CountRecurrence actualCountRat := by
  intro word n hv
  have hc := congrArg (fun value : Int => (value : Rat))
    (completionCount_signed_recurrence word n hv)
  have hnil : ((nilCodeContribution (decodeWord word) n : Int) : Rat) =
      (nilWordContribution word n : Rat) := by
    rw [nilCodeContribution_decodeWord]
    unfold nilWordContribution
    split <;> rfl
  have hheld : ((evalCount [] n (heldDelete word) : Int) : Rat) =
      eval (fun next => actualCountRat next n) (heldDelete word) := by
    unfold evalCount
    rw [ratCast_eval]
    rfl
  simp only [Rat.intCast_add, Rat.intCast_natCast, ratCast_sum_map] at hc
  change actualCountRat word n = _ at hc
  rw [show (nilCodeContribution (decodeWord word) n : Rat) =
      nilWordContribution word n from hnil, hheld] at hc
  simpa only [actualCountRat, decodeWord_appendWord, Rat.intCast_natCast] using hc

/-- Discharge this explicit candidate recurrence separately from its graph
certificate; uniqueness then identifies its coefficients with actual counts. -/
theorem candidate_equals_actual (candidate : Word → Nat → Rat)
    (candidate_recurrence : CountRecurrence candidate)
    (word : Word) (n : Nat) (hv : Valid (decodeWord word)) :
    candidate word n = (completionCount (decodeWord word) n : Rat) :=
  countRecurrence_unique candidate actualCountRat candidate_recurrence actualCountRat_recurrence word n hv

#print axioms decodeWord_appendWord
#print axioms valid_decodeWord_iff
#print axioms nilCodeContribution_decodeWord
#print axioms countRecurrence_unique
#print axioms ratCast_eval
#print axioms actualCountRat_recurrence
#print axioms candidate_equals_actual
end SignedCompletion
end StackSorting.Generalized.Decorated
