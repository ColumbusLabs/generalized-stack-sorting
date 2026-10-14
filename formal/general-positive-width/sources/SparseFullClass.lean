import SparseCanonicalForward

namespace StackSorting.SparseEndpointMSO
open Generalized

def emptySentence : Formula 0 0 := .allFO 1 (.neg .truth)

theorem satisfies_emptySentence (D : Model) : Satisfies D emptySentence ↔ D.domain = [] := by
  simp only [Satisfies, emptySentence, eval_all_one, Eval]
  constructor
  · intro h
    cases he : D.domain with
    | nil => rfl
    | cons x xs => exact False.elim (h x (by simp [he]) True.intro)
  · intro h x hx
    simp [h] at hx

theorem Isomorphism.empty_domain_iff {D E : Model} (iso : Isomorphism D E) :
    D.domain = [] ↔ E.domain = [] := by
  constructor
  · intro h
    cases he : E.domain with
    | nil => rfl
    | cons x xs =>
      have hx := iso.inv_mem x (by simp [he])
      simp [h] at hx
  · intro h
    cases hd : D.domain with
    | nil => rfl
    | cons x xs =>
      have hx := iso.to_mem x (by simp [hd])
      simp [h] at hx

def emptyIsomorphism (D : Model) (h : D.domain = []) :
    Isomorphism D (canonicalDiagram []) where
  toFun := id
  invFun := id
  to_mem _ hx := by simp [h] at hx
  inv_mem _ hx := by simp [canonicalDiagram, eventDiagram, canonicalEvents] at hx
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  insert_iff _ hx := by simp [h] at hx
  remove_iff _ hx := by simp [h] at hx
  successor_iff _ hx _ _ := by simp [h] at hx
  matching_iff _ hx _ _ := by simp [h] at hx

/-- The empty model contributes its one empty permutation explicitly. -/
def fullAcceptedSentence (r s : Nat) : Formula 0 0 :=
  disjunction emptySentence (acceptedSentence r s)

/-- Complete arbitrary-model characterization, including the empty case.
The formula is finite sparse MSO for each pair of natural slot widths. -/
theorem fullAcceptedSentence_iff_generated (D : Model) (r s : Nat) :
    Satisfies D (fullAcceptedSentence r s) ↔
      ∃ n output, output.Perm (List.range n) ∧ Generalized.Run r s [] (List.range n) output [] ∧
        Nonempty (Isomorphism D (canonicalDiagram output)) := by
  change Eval D (disjunction emptySentence (acceptedSentence r s)) Fin.elim0 Fin.elim0 ↔ _
  rw [eval_disjunction]
  change (Satisfies D emptySentence ∨ Satisfies D (acceptedSentence r s)) ↔ _
  rw [satisfies_emptySentence, acceptedSentence_iff_generated]
  constructor
  · rintro (he | ⟨n, output, _, hp, hg, hi⟩)
    · exact ⟨0, [], List.Perm.refl [], Generalized.Run.nil [], ⟨emptyIsomorphism D he⟩⟩
    · exact ⟨n, output, hp, hg, hi⟩
  · rintro ⟨n, output, hp, hg, ⟨iso⟩⟩
    cases n with
    | zero =>
      have ho : output = [] := List.perm_nil.mp hp
      subst output
      exact Or.inl (iso.empty_domain_iff.mpr rfl)
    | succ n => exact Or.inr ⟨n + 1, output, by omega, hp, hg, ⟨iso⟩⟩

/-- The complete accepted class has exactly one underlying generated
permutation per isomorphism class, including the empty permutation. -/
theorem fullAcceptedSentence_exists_unique_generated {D : Model} {r s : Nat}
    (hs : Satisfies D (fullAcceptedSentence r s)) :
    ∃ n output, output.Perm (List.range n) ∧ Generalized.Run r s [] (List.range n) output [] ∧
      Nonempty (Isomorphism D (canonicalDiagram output)) ∧
      ∀ m other, other.Perm (List.range m) →
        Nonempty (Isomorphism D (canonicalDiagram other)) → other = output := by
  obtain ⟨n, output, hp, hg, ⟨iso⟩⟩ := (fullAcceptedSentence_iff_generated D r s).mp hs
  refine ⟨n, output, hp, hg, ⟨iso⟩, ?_⟩
  rintro m other ho ⟨otherIso⟩
  exact canonicalDiagram_isomorphic_injective ho hp (otherIso.symm.trans iso)

theorem Isomorphism.domain_length {D E : Model} (iso : Isomorphism D E)
    (hd : D.domain.Nodup) (he : E.domain.Nodup) : D.domain.length = E.domain.length := by
  have hm : (D.domain.map iso.toFun).Nodup := nodup_map_on hd iso.toFun (by
    intro x hx y hy hh; exact iso.injective hx hy hh)
  have hp : (D.domain.map iso.toFun).Perm E.domain := by
    apply (List.perm_ext_iff_of_nodup hm he).mpr
    intro y
    constructor
    · rintro hym
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hym
      exact iso.to_mem x hx
    · intro hy
      exact List.mem_map.mpr ⟨iso.invFun y, iso.inv_mem y hy, iso.right_inv y hy⟩
  simpa only [List.length_map] using hp.length_eq

/-- A duplicate-free named-domain presentation has exactly twice as many
event vertices as its represented permutation has tokens. -/
theorem canonical_isomorphism_domain_size {D : Model} {n : Nat} {output : List Nat}
    (hd : D.domain.Nodup) (hp : output.Perm (List.range n))
    (iso : Isomorphism D (canonicalDiagram output)) : D.domain.length = 2 * n := by
  have hn : (canonicalDiagram output).domain.Nodup := List.nodup_range
  exact (iso.domain_length hd hn).trans (canonical_domain_size hp)

#print axioms fullAcceptedSentence_iff_generated
#print axioms fullAcceptedSentence_exists_unique_generated
#print axioms canonical_isomorphism_domain_size
end StackSorting.SparseEndpointMSO
