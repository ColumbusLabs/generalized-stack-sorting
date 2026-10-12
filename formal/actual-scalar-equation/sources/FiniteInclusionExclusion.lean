import Std

/-! Finite inclusion-exclusion over a named list of events. Nonempty subsets
are explicit sublists; for a duplicate-free index list each appears once. All
identities count event membership, never existential witnesses. -/
namespace StackSorting.FiniteInclusionExclusion

noncomputable def indicator (p : Prop) : Int :=
  @ite Int p (Classical.propDecidable p) 1 0

def nonemptySubsets : List Nat → List (List Nat)
  | [] => []
  | i :: indices => [i] :: (nonemptySubsets indices ++
      (nonemptySubsets indices).map (i :: ·))

def sign : List Nat → Int
  | [] => -1
  | _ :: rest => - sign rest

def valuation : List Nat → (List Nat → Int) → Int
  | [], _ => 0
  | i :: indices, f => f [i] + valuation indices f - valuation indices (fun J => f (i :: J))

theorem valuation_zero (indices : List Nat) : valuation indices (fun _ => 0) = 0 := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp [valuation, ih]

theorem valuation_add (indices : List Nat) (f g : List Nat → Int) :
    valuation indices (fun J => f J + g J) = valuation indices f + valuation indices g := by
  induction indices generalizing f g with
  | nil => rfl
  | cons i indices ih =>
    simp only [valuation, ih]
    omega

theorem valuation_congr (indices : List Nat) (f g : List Nat → Int)
    (h : ∀ J, J ≠ [] → J ⊆ indices → f J = g J) :
    valuation indices f = valuation indices g := by
  induction indices generalizing f g with
  | nil => rfl
  | cons i indices ih =>
    simp only [valuation]
    rw [h [i] (by simp) (by simp)]
    have htail : valuation indices f = valuation indices g := by
      apply ih
      intro J hne hsub
      exact h J hne (fun _ hj => List.mem_cons.mpr (Or.inr (hsub hj)))
    have hhead : valuation indices (fun J => f (i::J)) =
        valuation indices (fun J => g (i::J)) := by
      apply ih
      intro J _ hsub
      exact h (i::J) (by simp) (by
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · simp
        · exact List.mem_cons.mpr (Or.inr (hsub hk)))
    rw [htail,hhead]

theorem valuation_sum {α : Type} (indices : List Nat) (xs : List α)
    (f : List Nat → α → Int) :
    valuation indices (fun J => (xs.map (f J)).sum) =
      (xs.map (fun x => valuation indices (fun J => f J x))).sum := by
  induction xs with
  | nil => simp [valuation_zero]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [valuation_add, ih]

/-- The finite inclusion-exclusion identity at one outcome. -/
theorem indicator_union (indices : List Nat) (event : Nat → Prop) :
    indicator (∃ i ∈ indices, event i) =
      valuation indices (fun J => indicator (∀ i ∈ J, event i)) := by
  classical
  induction indices with
  | nil => simp [indicator, valuation]
  | cons i indices ih =>
    simp only [valuation]
    by_cases hi : event i
    · have hf : (fun J => indicator (∀ j ∈ i :: J, event j)) =
          (fun J => indicator (∀ j ∈ J, event j)) := by
        funext J
        simp [hi]
      rw [hf]
      simp [indicator, hi]
    · have hf : (fun J => indicator (∀ j ∈ i :: J, event j)) = (fun _ => 0) := by
        funext J
        simp [indicator, hi]
      rw [hf, valuation_zero, ← ih]
      simp [indicator, hi]

theorem sign_eq_power (J : List Nat) : sign J = (-1 : Int) ^ (J.length+1) := by
  induction J with
  | nil => simp [sign]
  | cons i J ih =>
    simp only [sign, List.length_cons]
    rw [ih]
    simpa using (Int.pow_succ (-1 : Int) (J.length+1)).symm

theorem sum_neg_map {α : Type} (xs : List α) (f : α → Int) :
    (xs.map (fun x => -f x)).sum = -(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem valuation_eq_signed_sum (indices : List Nat) (f : List Nat → Int) :
    valuation indices f = ((nonemptySubsets indices).map (fun J => sign J * f J)).sum := by
  induction indices generalizing f with
  | nil => simp [valuation, nonemptySubsets]
  | cons i indices ih =>
    simp only [valuation, nonemptySubsets, List.map_cons, List.sum_cons,
      List.map_append, List.sum_append, List.map_map, Function.comp_def, sign]
    rw [ih f, ih (fun J => f (i::J))]
    have he : ((nonemptySubsets indices).map (fun J => - sign J * f (i::J))).sum =
        - ((nonemptySubsets indices).map (fun J => sign J * f (i::J))).sum := by
      simpa only [Int.neg_mul] using sum_neg_map (nonemptySubsets indices)
        (fun J => sign J * f (i::J))
    rw [he]
    simp
    all_goals omega

theorem nonemptySubsets_spec {indices J : List Nat} (h : J ∈ nonemptySubsets indices) :
    J ≠ [] ∧ J ⊆ indices := by
  induction indices generalizing J with
  | nil => simp [nonemptySubsets] at h
  | cons i indices ih =>
    simp only [nonemptySubsets, List.mem_cons, List.mem_append, List.mem_map] at h
    rcases h with rfl | h | ⟨K,hK,rfl⟩
    · exact ⟨by simp, by simp⟩
    · obtain ⟨hne,hsub⟩ := ih h
      exact ⟨hne,fun _ hj => List.mem_cons.mpr (Or.inr (hsub hj))⟩
    · obtain ⟨_,hsub⟩ := ih hK
      refine ⟨by simp,?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · simp
      · exact List.mem_cons.mpr (Or.inr (hsub hj))

/-- The subset family has no repeated members when the original coordinate
names are distinct. In particular this holds for every `List.range m`. -/
theorem nonemptySubsets_nodup {indices : List Nat} (hn : indices.Nodup) :
    (nonemptySubsets indices).Nodup := by
  induction indices with
  | nil => simp [nonemptySubsets]
  | cons i indices ih =>
    have hn' := List.nodup_cons.mp hn
    have ht := ih hn'.2
    have hm : ((nonemptySubsets indices).map (i :: ·)).Nodup := by
      apply List.pairwise_map.mpr
      apply List.Pairwise.imp_of_mem (p := ht)
      intro a b _ _ hne he
      exact hne (List.cons.inj he).2
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append.mpr ⟨ht,hm,?_⟩⟩
    · intro hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hn'.1 ((nonemptySubsets_spec hmem).2 (by simp))
      · obtain ⟨K,hK,he⟩ := List.mem_map.mp hmem
        have hnil : K = [] := (List.cons.inj he).2
        exact (nonemptySubsets_spec hK).1 hnil
    · intro a ha b hb he
      obtain ⟨K,_,rfl⟩ := List.mem_map.mp hb
      have hi : i ∈ a := by rw [he]; simp
      exact hn'.1 ((nonemptySubsets_spec ha).2 hi)

noncomputable def countIn {α : Type} (ambient : List α) (event : α → Prop) : Int :=
  (ambient.map (fun x => indicator (event x))).sum

theorem countIn_congr {α : Type} (ambient : List α) (p q : α → Prop)
    (h : ∀ x, p x ↔ q x) : countIn ambient p = countIn ambient q := by
  unfold countIn
  congr 1
  apply List.map_congr_left
  intro x _
  exact congrArg indicator (propext (h x))

theorem countIn_eq_filter_length {α : Type} (ambient : List α) (event : α → Prop) :
    countIn ambient event = ((ambient.filter (fun x => @decide (event x)
      (Classical.propDecidable (event x)))).length : Int) := by
  classical
  induction ambient with
  | nil => simp [countIn]
  | cons x xs ih =>
    by_cases hx : event x <;> simp [countIn, indicator, hx] at * <;> omega

/-- Finite distinct-outcome inclusion-exclusion; the supplied ambient can be
any list, and duplicate-freeness gives the intended distinct-count reading. -/
theorem countIn_union {α : Type} (ambient : List α) (indices : List Nat)
    (event : Nat → α → Prop) :
    countIn ambient (fun x => ∃ i ∈ indices, event i x) =
      valuation indices (fun J => countIn ambient (fun x => ∀ i ∈ J, event i x)) := by
  unfold countIn
  rw [valuation_sum]
  congr 1
  apply List.map_congr_left
  intro x _
  exact indicator_union indices (fun i => event i x)

#print axioms indicator_union
#print axioms valuation_eq_signed_sum
#print axioms countIn_union
end StackSorting.FiniteInclusionExclusion
