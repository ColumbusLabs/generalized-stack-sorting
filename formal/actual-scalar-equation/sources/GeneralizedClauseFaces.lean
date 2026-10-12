import GeneralizedDecoratedSemantics

/-! Exact zero-face languages and their literal machine completion union.
These results do not assume or assert that existential machine completion
preserves intersections. The simultaneous-feasibility bridge is separate. -/
namespace StackSorting.Generalized.Decorated

/-- The coordinate-indexed binary face, over any list of coordinate names. -/
def faceOn (indices selected : List Nat) : State :=
  indices.map (fun index => if index ∈ selected then Factor.Z else Factor.B)

/-- Pointwise face semantics, keeping coordinate names explicit. -/
inductive FaceDigits (selected : List Nat) : List Nat → List Nat → Prop where
  | nil : FaceDigits selected [] []
  | cons {i d : Nat} {indices digits : List Nat}
      (binary : d ≤ 1) (forced : i ∈ selected → d = 0)
      (rest : FaceDigits selected indices digits) :
      FaceDigits selected (i :: indices) (d :: digits)

theorem denotes_faceOn (indices selected digits : List Nat) :
    denotes (faceOn indices selected) digits ↔ FaceDigits selected indices digits := by
  induction indices generalizing digits with
  | nil =>
    constructor
    · intro h
      have he : digits = [] := h
      subst digits
      exact .nil
    · intro h
      cases h
      rfl
  | cons i indices ih =>
    constructor
    · rintro ⟨left, right, hf, hr, rfl⟩
      have ht := (ih right).mp hr
      by_cases hi : i ∈ selected
      · have he : left = [0] := by simpa [faceOn, hi, Factor.denotes] using hf
        subst left
        exact .cons (by omega) (fun _ => rfl) ht
      · have he : left = [0] ∨ left = [1] := by
          simpa [faceOn, hi, Factor.denotes] using hf
        rcases he with rfl | rfl
        · exact .cons (by omega) (fun h => (hi h).elim) ht
        · exact .cons (by omega) (fun h => (hi h).elim) ht
    · intro h
      cases h with
      | cons binary forced rest =>
        refine ⟨[_], _, ?_, (ih _).mpr rest, rfl⟩
        by_cases hi : i ∈ selected
        · simpa [faceOn, hi, Factor.denotes] using forced hi
        · simp only [hi, ite_false, Factor.denotes, List.cons.injEq,
            and_true]
          omega

theorem FaceDigits.length {selected indices digits : List Nat}
    (h : FaceDigits selected indices digits) : digits.length = indices.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simpa using ih

theorem FaceDigits.binary {selected indices digits : List Nat}
    (h : FaceDigits selected indices digits) : ∀ d ∈ digits, d ≤ 1 := by
  induction h with
  | nil => simp
  | cons hb _ _ ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hb
    · exact ih d hd

theorem FaceDigits.mono {selected weaker indices digits : List Nat}
    (h : FaceDigits selected indices digits) (hsub : weaker ⊆ selected) :
    FaceDigits weaker indices digits := by
  induction h with
  | nil => exact .nil
  | cons hb hf _ ih => exact .cons hb (fun hm => hf (hsub hm)) ih

theorem FaceDigits.change_selection {selected weaker indices digits : List Nat}
    (h : FaceDigits selected indices digits)
    (himp : ∀ i ∈ indices, i ∈ weaker → i ∈ selected) :
    FaceDigits weaker indices digits := by
  induction h with
  | nil => exact .nil
  | @cons i d indices digits hb hf ht ih =>
    exact .cons hb (fun hi => hf (himp i (by simp) hi))
      (ih (fun j hj => himp j (by simp [hj])))

theorem FaceDigits.exists_zero {selected indices digits : List Nat}
    (h : FaceDigits selected indices digits) {j : Nat}
    (hj : j ∈ indices) (hs : j ∈ selected) : 0 ∈ digits := by
  induction h with
  | nil => simp at hj
  | @cons i d indices digits hb hf ht ih =>
    rcases List.mem_cons.mp hj with rfl | hj
    · simp [hf hs]
    · exact List.mem_cons.mpr (Or.inr (ih hj))

theorem faceDigits_empty_iff (indices digits : List Nat) :
    FaceDigits [] indices digits ↔
      digits.length = indices.length ∧ ∀ d ∈ digits, d ≤ 1 := by
  constructor
  · exact fun h => ⟨h.length, h.binary⟩
  · intro h
    induction indices generalizing digits with
    | nil =>
      have he : digits = [] := List.length_eq_zero_iff.mp h.1
      subst digits
      exact .nil
    | cons i indices ih =>
      cases digits with
      | nil => simp at h
      | cons d digits =>
        refine .cons (h.2 d (by simp)) (by simp) ?_
        apply ih
        exact ⟨by simpa using h.1, fun x hx => h.2 x (by simp [hx])⟩

/-- A binary word containing zero belongs to one of the singleton faces.
Duplicate coordinate names are excluded: each face forces exactly its position. -/
theorem binary_zero_singleton {indices digits : List Nat}
    (hn : indices.Nodup) (hlen : digits.length = indices.length)
    (hb : ∀ d ∈ digits, d ≤ 1) (hz : 0 ∈ digits) :
    ∃ j ∈ indices, FaceDigits [j] indices digits := by
  induction indices generalizing digits with
  | nil =>
    have he : digits = [] := List.length_eq_zero_iff.mp hlen
    simp [he] at hz
  | cons i indices ih =>
    cases digits with
    | nil => simp at hlen
    | cons d digits =>
      have hnt := List.nodup_cons.mp hn
      have hdt : digits.length = indices.length := by simpa using hlen
      have hbt : ∀ x ∈ digits, x ≤ 1 := fun x hx => hb x (by simp [hx])
      rcases List.mem_cons.mp hz with hd | hz
      · subst d
        refine ⟨i, by simp, .cons (by omega) (fun _ => rfl) ?_⟩
        have ht := (faceDigits_empty_iff indices digits).mpr ⟨hdt, hbt⟩
        apply ht.change_selection
        intro j hj hji
        have he : j = i := by simpa using hji
        exact False.elim (hnt.1 (he ▸ hj))
      · obtain ⟨j, hj, ht⟩ := ih hnt.2 hdt hbt hz
        refine ⟨j, by simp [hj], .cons (hb d (by simp)) ?_ ht⟩
        intro hs
        have he : i = j := by simpa using hs
        exact False.elim (hnt.1 (he ▸ hj))

theorem clause_denotes_iff_singleton_face (m : Nat) (digits : List Nat) :
    Factor.denotes (.C m) digits ↔
      ∃ j ∈ List.range m, denotes (zeroFace m [j]) digits := by
  constructor
  · rintro ⟨hlen, hb, hz⟩
    obtain ⟨j, hj, hf⟩ := binary_zero_singleton List.nodup_range
      (by simpa using hlen) hb hz
    exact ⟨j, hj, (denotes_faceOn _ _ _).mpr hf⟩
  · rintro ⟨j, hj, hf⟩
    have hd := (denotes_faceOn _ _ _).mp hf
    exact ⟨by simpa using hd.length, hd.binary, hd.exists_zero hj (by simp)⟩

theorem height_append (left right : State) :
    height (left ++ right) = height left + height right := by
  simp [height]

theorem height_faceOn (indices selected : List Nat) :
    height (faceOn indices selected) = indices.length := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    by_cases hi : i ∈ selected <;> simp [height, faceOn, hi, Factor.height] at * <;> omega

theorem height_zeroFace (m : Nat) (selected : List Nat) :
    height (zeroFace m selected) = m := by
  simpa [faceOn, zeroFace] using height_faceOn (List.range m) selected

/-- The actual represented coordinate language is exactly the finite union.
No validity, O-freeness, or minimum block length is needed for this union. -/
theorem denotes_clause_iff_singleton_face (P Q : State) (m : Nat) (digits : List Nat) :
    denotes (P ++ [.C m] ++ Q) digits ↔
      ∃ j ∈ List.range m, denotes (P ++ zeroFace m [j] ++ Q) digits := by
  simp only [denotes_append]
  constructor
  · rintro ⟨front, back, ⟨pre, block, hp, hb, rfl⟩, hq, rfl⟩
    obtain ⟨chunk, empty, hc, he, hblock⟩ := hb
    have he' : empty = [] := he
    subst empty
    simp only [List.append_nil] at hblock
    subst block
    obtain ⟨j, hj, hf⟩ := (clause_denotes_iff_singleton_face m chunk).mp hc
    exact ⟨j, hj, pre ++ chunk, back, ⟨pre, chunk, hp, hf, rfl⟩, hq, rfl⟩
  · rintro ⟨j, hj, front, back, ⟨pre, block, hp, hb, rfl⟩, hq, rfl⟩
    have hc := (clause_denotes_iff_singleton_face m block).mpr ⟨j, hj, hb⟩
    exact ⟨pre ++ block, back,
      ⟨pre, block, hp, ⟨block, [], hc, rfl, by simp⟩, rfl⟩, hq, rfl⟩

theorem represents_clause_iff_singleton_face (P Q : State) (m : Nat)
    (physical : List Nat) :
    Represents (P ++ [.C m] ++ Q) physical ↔
      ∃ j ∈ List.range m, Represents (P ++ zeroFace m [j] ++ Q) physical := by
  constructor
  · rintro ⟨digits, hd, hp⟩
    obtain ⟨j, hj, hf⟩ := (denotes_clause_iff_singleton_face P Q m digits).mp hd
    exact ⟨j, hj, digits, hf, hp⟩
  · rintro ⟨j, hj, digits, hd, hp⟩
    exact ⟨digits, (denotes_clause_iff_singleton_face P Q m digits).mpr ⟨j, hj, hd⟩, hp⟩

/-- Literal admitted output languages commute with this union. Histories and
initial stacks remain existential witnesses; neither receives multiplicity. -/
theorem completion_clause_iff_singleton_face (P Q : State) (m n : Nat)
    (output : List Nat) :
    Completion (P ++ [.C m] ++ Q) n output ↔
      ∃ j ∈ List.range m, Completion (P ++ zeroFace m [j] ++ Q) n output := by
  have he (j : Nat) : height (P ++ [.C m] ++ Q) =
      height (P ++ zeroFace m [j] ++ Q) := by
    simp only [height_append, height_zeroFace]
    rfl
  constructor
  · rintro ⟨physical, hp, hr⟩
    obtain ⟨j, hj, hf⟩ := (represents_clause_iff_singleton_face P Q m physical).mp hp
    exact ⟨j, hj, physical, hf, by simpa only [he j] using hr⟩
  · rintro ⟨j, hj, physical, hp, hr⟩
    exact ⟨physical, (represents_clause_iff_singleton_face P Q m physical).mpr ⟨j, hj, hp⟩,
      by simpa only [he j] using hr⟩

#print axioms clause_denotes_iff_singleton_face
#print axioms completion_clause_iff_singleton_face
end StackSorting.Generalized.Decorated
