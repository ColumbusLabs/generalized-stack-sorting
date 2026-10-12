import GeneralizedUnaryBounds

/-! Exact physical rank constraints for an ordinary unary prefix followed by a
binary zero-face. This is the terminal-clause application required by the
unrestricted signed recurrence, without unrelated clause-bearing contexts. -/
namespace StackSorting.Generalized.Decorated
open Coordinates StackSorting.MonotoneElimination

def terminalBaseBounds (P : State) (m : Nat) : List (Nat × Nat) :=
  boundsAt P 1 ++ (List.range m).map (fun j => (P.length + 1 + j, 1))

def selectedLabels (P : State) (selected : List Nat) : List Nat :=
  selected.map (fun j => P.length + 1 + j)

def terminalFaceBounds (P : State) (m : Nat) (selected : List Nat) : List (Nat × Nat) :=
  terminalBaseBounds P m ++ (selectedLabels P selected).map (fun v => (v, 0))

theorem denotes_append_fixed (P Q : State) (a b : List Nat)
    (ha : a.length = height P) :
    denotes (P ++ Q) (a ++ b) ↔ denotes P a ∧ denotes Q b := by
  rw [denotes_append]
  constructor
  · rintro ⟨front, back, hf, hb, he⟩
    have hl : a.length = front.length := ha.trans (denotes_length hf).symm
    obtain ⟨hfront, hback⟩ := List.append_inj he hl
    simpa [← hfront, ← hback] using And.intro hf hb
  · rintro ⟨hp, hq⟩
    exact ⟨a, b, hp, hq, rfl⟩

theorem faceDigits_map_iff (selected indices : List Nat) (f : Nat → Nat) :
    FaceDigits selected indices (indices.map f) ↔
      ∀ i ∈ indices, f i ≤ 1 ∧ (i ∈ selected → f i = 0) := by
  induction indices with
  | nil => constructor <;> intro h <;> simp_all [FaceDigits.nil]
  | cons i indices ih =>
    constructor
    · intro h
      cases h with
      | cons hb hf ht =>
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact ⟨hb, hf⟩
        · exact ih.mp ht j hj
    · intro h
      have hh := h i (by simp)
      exact .cons hh.1 hh.2 (ih.mpr (fun j hj => h j (by simp [hj])))

theorem denotes_face_rankWord (m : Nat) (selected : List Nat)
    (physical : List Nat) (next : Nat) :
    denotes (zeroFace m selected) (rankWord physical next m) ↔
      ∀ j ∈ List.range m, rankSlot physical (next+j) ≤ 1 ∧
        (j ∈ selected → rankSlot physical (next+j) = 0) := by
  rw [show zeroFace m selected = faceOn (List.range m) selected from rfl,
    denotes_faceOn]
  simpa only [rankWord, List.range'_eq_map_range, List.map_map, Function.comp_def] using
    faceDigits_map_iff selected (List.range m) (fun j => rankSlot physical (next+j))

theorem rankBounds_terminalFace (P : State) (m : Nat) (selected : List Nat)
    (hsub : selected ⊆ List.range m) (physical : List Nat) :
    RankBounds (terminalFaceBounds P m selected) physical ↔
      RankBounds (boundsAt P 1) physical ∧
      ∀ j ∈ List.range m, rankSlot physical (P.length+1+j) ≤ 1 ∧
        (j ∈ selected → rankSlot physical (P.length+1+j) = 0) := by
  constructor
  · intro hb
    refine ⟨?_, ?_⟩
    · intro v b hm
      exact hb v b (by simp [terminalFaceBounds, terminalBaseBounds, hm])
    · intro j hj
      refine ⟨hb _ 1 ?_, ?_⟩
      · simp only [terminalFaceBounds, terminalBaseBounds, List.mem_append]
        exact Or.inl (Or.inr (List.mem_map.mpr ⟨j, hj, rfl⟩))
      · intro hjs
        have h := hb (P.length+1+j) 0 (by
          simp only [terminalFaceBounds, List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨P.length+1+j,
            List.mem_map.mpr ⟨j, hjs, rfl⟩, rfl⟩))
        omega
  · rintro ⟨hp, hf⟩ v b hm
    simp only [terminalFaceBounds, terminalBaseBounds, List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · exact hp v b hm
    · obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
      have hvb := Prod.mk.inj he
      rcases hvb with ⟨rfl, rfl⟩
      exact (hf j hj).1
    · obtain ⟨label, hl, he⟩ := List.mem_map.mp hm
      have hvb := Prod.mk.inj he
      rcases hvb with ⟨rfl, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
      exact Nat.le_of_eq ((hf j (hsub hj)).2 hj)

/-- Actual represented physical orders, not an abstract constraint interface. -/
theorem represents_terminal_face_iff {P : State} (hu : Unary P)
    (m : Nat) (selected : List Nat) (hsub : selected ⊆ List.range m)
    (physical : List Nat) :
    Represents (P ++ zeroFace m selected) physical ↔
      physical.Perm (List.range' 1 (P.length+m)) ∧
      RankBounds (terminalFaceBounds P m selected) physical := by
  rw [represents_iff_rankWord]
  have hh : height (P ++ zeroFace m selected) = P.length + m := by
    rw [height_append, unary_height hu, height_zeroFace]
  rw [hh, rankWord_append]
  have hl : (rankWord physical 1 P.length).length = height P := by
    simp [rankWord, unary_height hu]
  rw [denotes_append_fixed _ _ _ _ hl, denotes_unary_rankWord hu,
    denotes_face_rankWord]
  rw [rankBounds_terminalFace P m selected hsub]
  simp [Nat.add_comm]

theorem boundEligible_terminalFace (P : State) (m : Nat) (selected : List Nat)
    (U : List Nat) (v : Nat) :
    BoundEligible (terminalFaceBounds P m selected) U v ↔
      WithZeros (BoundEligible (terminalBaseBounds P m)) (selectedLabels P selected) U v := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro label bound hm he
      exact h label bound (List.mem_append_left _ hm) he
    · intro i hi he
      have hb := h i 0 (List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, rfl⟩)) he
      omega
  · rintro ⟨hb, hz⟩ label bound hm he
    rcases List.mem_append.mp hm with hm | hm
    · exact hb label bound hm he
    · obtain ⟨i, hi, hi'⟩ := List.mem_map.mp hm
      have hpair := Prod.mk.inj hi'
      rcases hpair with ⟨rfl, rfl⟩
      exact Nat.le_of_eq (hz i hi he)

theorem terminal_base_selected_bound (P : State) (m : Nat) (selected : List Nat)
    (hsub : selected ⊆ List.range m) (U : List Nat) (v : Nat)
    (hv : v ∈ selectedLabels P selected)
    (hb : BoundEligible (terminalBaseBounds P m) U v) : smallerCount U v ≤ 1 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
  apply hb _ 1 _ rfl
  exact List.mem_append_right _ (List.mem_map.mpr ⟨j, hsub hj, rfl⟩)

theorem boundsAt_label_bounds {P : State} {next label bound : Nat}
    (h : (label,bound) ∈ boundsAt P next) :
    next ≤ label ∧ label < next + P.length := by
  induction P generalizing next with
  | nil => simp [boundsAt] at h
  | cons factor rest ih =>
    simp only [boundsAt, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · have hh := ih h
      simp only [List.length_cons]
      omega

theorem terminalFaceBounds_labels (P : State) (m : Nat) (selected : List Nat)
    (hsub : selected ⊆ List.range m) :
    ∀ label bound, (label,bound) ∈ terminalFaceBounds P m selected →
      label ∈ List.range' 1 (P.length+m) := by
  intro label bound hm
  simp only [terminalFaceBounds, terminalBaseBounds, List.mem_append] at hm
  simp only [List.mem_range'_1]
  rcases hm with (hm | hm) | hm
  · have hh := boundsAt_label_bounds hm
    omega
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
    have hh := Prod.mk.inj he
    have hjm := List.mem_range.mp hj
    omega
  · obtain ⟨v, hv, he⟩ := List.mem_map.mp hm
    obtain ⟨j, hj, he'⟩ := List.mem_map.mp hv
    have hh := Prod.mk.inj he
    have hjm := List.mem_range.mp (hsub hj)
    omega

#print axioms represents_terminal_face_iff
#print axioms boundEligible_terminalFace
end StackSorting.Generalized.Decorated
