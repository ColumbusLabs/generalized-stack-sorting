import GeneralizedCompletionCounting
import GeneralizedRecordBatches

/-! Literal finite-cardinality first-letter partition of the complete canonical
code language. The source list contains each admitted output's unique code
once; physical orders and histories are existential witnesses only. -/
namespace StackSorting.Generalized.Decorated
open LazyCode

private theorem sum_map_add (xs : List α) (f g : α → Nat) :
    (xs.map (fun a => f a + g a)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_map_zero (xs : List α) : (xs.map (fun _ => (0 : Nat))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

private theorem sum_indicator [DecidableEq α] (xs : List α) (a : α) :
    (xs.map (fun b => if a = b then 1 else 0)).sum = xs.count a := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    by_cases he : a = b
    · subst b; simp [ih, Nat.add_comm]
    · simp [he, Ne.symm he, ih]

/-- An exact finite partition into disjoint tags. The keys are distinct and
every source item has exactly one key. No recurrence hypothesis is used. -/
private theorem length_eq_sum_fibers [DecidableEq β]
    (keys : List β) (xs : List α) (tag : α → β)
    (hk : keys.Nodup) (covered : ∀ x ∈ xs, tag x ∈ keys) :
    xs.length = (keys.map (fun key =>
      (xs.filter (fun x => decide (tag x = key))).length)).sum := by
  induction xs with
  | nil => simp [sum_map_zero]
  | cons a xs ih =>
    have ht : ∀ x ∈ xs, tag x ∈ keys := fun x hx => covered x (by simp [hx])
    have hm : tag a ∈ keys := covered a (by simp)
    have hs : (keys.map (fun key =>
        ((a :: xs).filter (fun x => decide (tag x = key))).length)) =
        keys.map (fun key => (if tag a = key then 1 else 0) +
          (xs.filter (fun x => decide (tag x = key))).length) := by
      apply List.map_congr_left
      intro key _
      by_cases he : tag a = key <;> simp [he, Nat.add_comm]
    rw [hs, sum_map_add, sum_indicator, hk.count_of_mem hm, ← ih ht]
    simp [Nat.add_comm]

/-- One nil class, one distinct class for each held rank, and one for each
positive record batch allowed by the actual remaining input supply. -/
def firstCodeKeys (h n : Nat) : List (Option Letter) :=
  none :: ((List.range' 1 h).map (fun k => some (Letter.H k)) ++
    (List.range' 1 n).map (fun b => some (Letter.N b)))

theorem firstCodeKeys_nodup (h n : Nat) : (firstCodeKeys h n).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · simp [List.mem_append, List.mem_map]
  · apply List.nodup_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      simpa [List.Nodup] using (List.nodup_range' (s := 1) (n := h))
    · apply List.pairwise_map.mpr
      simpa [List.Nodup] using (List.nodup_range' (s := 1) (n := n))
    · intro a ha b hb
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
      simp

theorem CodeCompletion.first_key {state : State} {n : Nat} {code : List Letter}
    (hc : CodeCompletion state n code) : code.head? ∈ firstCodeKeys (height state) n := by
  cases code with
  | nil => simp [firstCodeKeys]
  | cons letter code =>
    cases letter with
    | H k =>
      have h := (codeCompletion_held state n k code).mp hc
      have hm : k ∈ List.range' 1 (height state) := List.mem_range'_1.mpr (by omega)
      exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨k, hm, rfl⟩)))
    | N b =>
      have h := (codeCompletion_record state n b code).mp hc
      have hm : b ∈ List.range' 1 n := List.mem_range'_1.mpr (by omega)
      exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨b, hm, rfl⟩)))

/-- A literal subset of the distinct complete code list, selected by its first
letter (or by the nil tag). -/
noncomputable def firstCodeFiber (state : State) (n : Nat) (key : Option Letter) :
    List (List Letter) := by
  classical
  exact (completionCodes state n).filter (fun code => decide (code.head? = key))

theorem mem_firstCodeFiber (state : State) (n : Nat) (key : Option Letter) (code : List Letter) :
    code ∈ firstCodeFiber state n key ↔ CodeCompletion state n code ∧ code.head? = key := by
  classical
  simp [firstCodeFiber, mem_completionCodes]

theorem firstCodeFiber_nodup (state : State) (n : Nat) (key : Option Letter) :
    (firstCodeFiber state n key).Nodup := by
  classical
  exact (completionCodes_nodup state n).filter _

/-- Distinct tail codes of one fixed first-letter class. Prefixing this fixed
letter is injective; equality of successor languages never merges ranks. -/
noncomputable def firstCodeTails (state : State) (n : Nat) (letter : Letter) :
    List (List Letter) := (firstCodeFiber state n (some letter)).map List.tail

theorem mem_firstCodeTails (state : State) (n : Nat) (letter : Letter) (code : List Letter) :
    code ∈ firstCodeTails state n letter ↔ CodeCompletion state n (letter :: code) := by
  simp only [firstCodeTails, List.mem_map, mem_firstCodeFiber]
  constructor
  · rintro ⟨whole, ⟨hc, hh⟩, ht⟩
    obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp hh
    simp only [List.tail_cons] at ht
    subst tail
    exact hc
  · intro hc
    exact ⟨letter :: code, ⟨hc, rfl⟩, rfl⟩

theorem firstCodeTails_nodup (state : State) (n : Nat) (letter : Letter) :
    (firstCodeTails state n letter).Nodup := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := firstCodeFiber_nodup state n (some letter))
  intro a b ha hb hne he
  have ha' := (mem_firstCodeFiber state n (some letter) a).mp ha
  have hb' := (mem_firstCodeFiber state n (some letter) b).mp hb
  obtain ⟨ta, rfl⟩ := List.head?_eq_some_iff.mp ha'.2
  obtain ⟨tb, rfl⟩ := List.head?_eq_some_iff.mp hb'.2
  exact hne (congrArg (List.cons letter) he)

theorem firstCodeTails_length (state : State) (n : Nat) (letter : Letter) :
    (firstCodeTails state n letter).length = (firstCodeFiber state n (some letter)).length := by
  simp [firstCodeTails]

/-- Semantic form of each held-rank fiber. The existential physical image
is used only to decide membership, never as a multiplicity. -/
theorem mem_firstCodeTails_held (state : State) (n k : Nat) (code : List Letter) :
    code ∈ firstCodeTails state n (.H k) ↔
      0 < k ∧ k ≤ height state ∧ Budget (height state-1) n code ∧
      ∃ after, PhysicalPopImage state (k-1) after ∧
        [] ∈ rankCodeOrders 3 3 (height state-1) code after := by
  rw [mem_firstCodeTails, codeCompletion_held]

/-- Any separately proved literal successor-language equality transports to
finite cardinality. This adapter assumes no counting identity. -/
theorem firstCodeTails_perm_of_target (state target : State) (n m : Nat) (letter : Letter)
    (semantics : ∀ code, CodeCompletion state n (letter :: code) ↔ CodeCompletion target m code) :
    (firstCodeTails state n letter).Perm (completionCodes target m) := by
  apply (List.perm_ext_iff_of_nodup (firstCodeTails_nodup state n letter)
    (completionCodes_nodup target m)).mpr
  intro code
  rw [mem_firstCodeTails, mem_completionCodes]
  exact semantics code

theorem firstCodeTails_length_of_target (state target : State) (n m : Nat) (letter : Letter)
    (semantics : ∀ code, CodeCompletion state n (letter :: code) ↔ CodeCompletion target m code) :
    (firstCodeTails state n letter).length = completionCount target m := by
  rw [completionCount_eq_codes]
  exact (firstCodeTails_perm_of_target state target n m letter semantics).length_eq

/-- The sole possible empty code contributes one exactly when the represented
empty stack is admitted and both held and future supplies are exhausted. -/
noncomputable def nilCodeContribution (state : State) (n : Nat) : Nat := by
  classical
  exact if height state = 0 ∧ n = 0 ∧ Represents state [] then 1 else 0

theorem firstCodeFiber_nil_length (state : State) (n : Nat) :
    (firstCodeFiber state n none).length = nilCodeContribution state n := by
  classical
  have h := (completionCodes_nodup state n).count (a := ([] : List Letter))
  simpa only [firstCodeFiber, List.count_eq_length_filter, Bool.beq_eq_decide_eq, List.head?_eq_none_iff,
    nilCodeContribution, mem_completionCodes, codeCompletion_nil] using h

theorem nilCodeContribution_of_positive (state : State) (n : Nat)
    (positive : 0 < height state+n) : nilCodeContribution state n = 0 := by
  classical
  have hn : ¬ (height state = 0 ∧ n = 0 ∧ Represents state []) := by omega
  simp [nilCodeContribution, hn]

/-- The first record-batch fiber is in bijection with the actual successor's
complete canonical-code language for every positive, available batch size. -/
theorem firstCodeTails_record_perm (state : State) (n b : Nat)
    (positive : 0 < b) (available : b ≤ n) :
    (firstCodeTails state n (.N b)).Perm (completionCodes (appendHeld state (b-1)) (n-b)) := by
  apply (List.perm_ext_iff_of_nodup (firstCodeTails_nodup state n (.N b))
    (completionCodes_nodup _ _)).mpr
  intro code
  simp [mem_firstCodeTails, mem_completionCodes, codeCompletion_record_target, positive, available]

theorem firstCodeTails_record_length (state : State) (n b : Nat)
    (positive : 0 < b) (available : b ≤ n) :
    (firstCodeTails state n (.N b)).length = completionCount (appendHeld state (b-1)) (n-b) := by
  rw [completionCount_eq_codes]
  exact (firstCodeTails_record_perm state n b positive available).length_eq

/-- Exact first-letter finite-cardinality recurrence. Each held value rank
retains its own disjoint code fiber, and each record batch contributes the
actual distinct completion-output count of its literal successor state. -/
theorem completionCount_first_letter (state : State) (n : Nat) :
    completionCount state n = nilCodeContribution state n +
      ((List.range' 1 (height state)).map (fun k => (firstCodeTails state n (.H k)).length)).sum +
      ((List.range' 1 n).map (fun b => completionCount (appendHeld state (b-1)) (n-b))).sum := by
  classical
  have partition := length_eq_sum_fibers (firstCodeKeys (height state) n)
    (completionCodes state n) List.head? (firstCodeKeys_nodup _ _)
    (fun code hc => ((mem_completionCodes state n code).mp hc).first_key)
  have records : ((List.range' 1 n).map (fun b => (firstCodeTails state n (.N b)).length)) =
      (List.range' 1 n).map (fun b => completionCount (appendHeld state (b-1)) (n-b)) := by
    apply List.map_congr_left
    intro b hb
    have hr := List.mem_range'_1.mp hb
    exact firstCodeTails_record_length state n b (by omega) (by omega)
  rw [completionCount_eq_codes]
  simp only [firstCodeKeys, List.map_cons, List.map_append, List.map_map,
    List.sum_cons, List.sum_append, Function.comp_def] at partition
  change (completionCodes state n).length =
    (firstCodeFiber state n none).length +
      (((List.range' 1 (height state)).map (fun k =>
        (firstCodeFiber state n (some (.H k))).length)).sum +
       ((List.range' 1 n).map (fun b =>
        (firstCodeFiber state n (some (.N b))).length)).sum) at partition
  simp only [← firstCodeTails_length, firstCodeFiber_nil_length] at partition
  rw [records] at partition
  omega

/-- Positive total size has no empty-code summand. -/
theorem completionCount_first_letter_positive (state : State) (n : Nat)
    (positive : 0 < height state+n) :
    completionCount state n =
      ((List.range' 1 (height state)).map (fun k => (firstCodeTails state n (.H k)).length)).sum +
      ((List.range' 1 n).map (fun b => completionCount (appendHeld state (b-1)) (n-b))).sum := by
  rw [completionCount_first_letter, nilCodeContribution_of_positive state n positive]
  simp

#print axioms firstCodeTails_nodup
#print axioms firstCodeTails_record_perm
#print axioms completionCount_first_letter
#print axioms completionCount_first_letter_positive
end StackSorting.Generalized.Decorated
