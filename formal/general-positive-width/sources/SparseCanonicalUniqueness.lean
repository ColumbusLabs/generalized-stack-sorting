import SparseStructuralSentence

namespace StackSorting.SparseEndpointMSO
open Generalized

/-- A directed finite time path admits no nontrivial time-index permutation,
even when the two presentations initially have different lengths. -/
theorem Isomorphism.time_index_eq {D E : Model} {n m : Nat}
    (iso : Isomorphism D E) (hd : TimePath D n) (he : TimePath E m)
    {x : Nat} (hx : x ∈ D.domain) : iso.toFun x = x := by
  induction x with
  | zero =>
    have hf := iso.to_mem 0 hx
    by_cases hz : iso.toFun 0 = 0
    · exact hz
    · have hb : iso.toFun 0 < m := by simpa [he.1] using hf
      have hp : iso.toFun 0 - 1 ∈ E.domain := by rw [he.1, List.mem_range]; omega
      have hs := (he.2 _ hp _ hf).mpr (by omega : iso.toFun 0 - 1 + 1 = iso.toFun 0)
      have ht := (iso.symm.successor_iff _ hp _ hf).mp hs
      change D.S (iso.invFun (iso.toFun 0 - 1)) (iso.invFun (iso.toFun 0)) at ht
      rw [iso.left_inv 0 hx] at ht
      have bad := (hd.2 _ (iso.inv_mem _ hp) _ hx).mp ht
      omega
  | succ x ih =>
    have hxb : x + 1 < n := by simpa [hd.1] using hx
    have hp : x ∈ D.domain := by rw [hd.1, List.mem_range]; omega
    have hs := (hd.2 x hp (x + 1) hx).mpr rfl
    have ht := (iso.successor_iff x hp (x + 1) hx).mp hs
    have hv := (he.2 _ (iso.to_mem x hp) _ (iso.to_mem (x + 1) hx)).mp ht
    rw [ih hp] at hv
    exact hv.symm

theorem Isomorphism.time_length_eq {D E : Model} {n m : Nat}
    (iso : Isomorphism D E) (hd : TimePath D n) (he : TimePath E m) : n = m := by
  have hn : n ≤ m := by
    apply Nat.le_of_not_lt
    intro h
    have hm : m ∈ D.domain := by rw [hd.1, List.mem_range]; omega
    have ht := iso.to_mem m hm
    rw [iso.time_index_eq hd he hm, he.1, List.mem_range] at ht
    omega
  have hm : m ≤ n := by
    apply Nat.le_of_not_lt
    intro h
    have hn : n ∈ E.domain := by rw [he.1, List.mem_range]; omega
    have ht := iso.symm.to_mem n hn
    rw [iso.symm.time_index_eq he hd hn, hd.1, List.mem_range] at ht
    omega
  omega

theorem Isomorphism.time_supported_eq {D E : Model} {n m : Nat}
    (iso : Isomorphism D E) (hd : TimePath D n) (he : TimePath E m) :
    supported D = supported E := by
  have hnm := iso.time_length_eq hd he
  have hdom : D.domain = E.domain := hd.1.trans ((congrArg List.range hnm).trans he.1.symm)
  apply model_extensionality
  · exact hdom
  · funext x
    apply propext
    change (x ∈ D.domain ∧ D.I x) ↔ x ∈ E.domain ∧ E.I x
    by_cases hx : x ∈ D.domain
    · have hh := iso.insert_iff x hx
      rw [iso.time_index_eq hd he hx] at hh
      simpa only [← hdom, hx, true_and] using hh
    · simp [← hdom, hx]
  · funext x
    apply propext
    change (x ∈ D.domain ∧ D.R x) ↔ x ∈ E.domain ∧ E.R x
    by_cases hx : x ∈ D.domain
    · have hh := iso.remove_iff x hx
      rw [iso.time_index_eq hd he hx] at hh
      simpa only [← hdom, hx, true_and] using hh
    · simp [← hdom, hx]
  · funext x y
    apply propext
    change (x ∈ D.domain ∧ y ∈ D.domain ∧ D.S x y) ↔
      x ∈ E.domain ∧ y ∈ E.domain ∧ E.S x y
    by_cases hx : x ∈ D.domain <;> by_cases hy : y ∈ D.domain
    · have hh := iso.successor_iff x hx y hy
      rw [iso.time_index_eq hd he hx, iso.time_index_eq hd he hy] at hh
      simpa only [← hdom, hx, hy, true_and] using hh
    all_goals simp [← hdom, hx, hy]
  · funext x y
    apply propext
    change (x ∈ D.domain ∧ y ∈ D.domain ∧ D.M x y) ↔
      x ∈ E.domain ∧ y ∈ E.domain ∧ E.M x y
    by_cases hx : x ∈ D.domain <;> by_cases hy : y ∈ D.domain
    · have hh := iso.matching_iff x hx y hy
      rw [iso.time_index_eq hd he hx, iso.time_index_eq hd he hy] at hh
      simpa only [← hdom, hx, hy, true_and] using hh
    all_goals simp [← hdom, hx, hy]

theorem supported_canonicalDiagram {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) : supported (canonicalDiagram output) = canonicalDiagram output := by
  have hin := (permutation_canonical_validity hp).2.1
  change supported (eventDiagram (canonicalEvents 0 output)) = eventDiagram (canonicalEvents 0 output)
  rw [supported_eq_eventDiagram (eventDiagram_path _) (canonicalMatchingAxioms hp),
    modelEvents_eventDiagram hin (canonicalMatchingAxioms hp)]

/-- Isomorphism of canonical diagrams already forces the permutations equal;
no choice of vertex renaming can identify different outputs. -/
theorem canonicalDiagram_isomorphic_injective {n m : Nat} {a b : List Nat}
    (ha : a.Perm (List.range n)) (hb : b.Perm (List.range m))
    (iso : Isomorphism (canonicalDiagram a) (canonicalDiagram b)) : a = b := by
  have he := iso.time_supported_eq (eventDiagram_path _) (eventDiagram_path _)
  rw [supported_canonicalDiagram ha, supported_canonicalDiagram hb] at he
  exact canonicalDiagram_injective ha hb he

/-- Uniqueness holds for the arbitrary-label model up to genuine isomorphism,
independently of all choices in extracting its Hamiltonian enumeration. -/
theorem structuralSentence_exists_unique_permutation {D : Model}
    (hs : Satisfies D structuralSentence) :
    ∃ n output, output.Perm (List.range n) ∧
      Nonempty (Isomorphism D (canonicalDiagram output)) ∧
      ∀ m other, other.Perm (List.range m) →
        Nonempty (Isomorphism D (canonicalDiagram other)) → other = output := by
  obtain ⟨n, output, hp, ⟨iso⟩⟩ := structuralSentence_canonical_converse hs
  refine ⟨n, output, hp, ⟨iso⟩, ?_⟩
  rintro m other ho ⟨otherIso⟩
  exact canonicalDiagram_isomorphic_injective ho hp (otherIso.symm.trans iso)

#print axioms Isomorphism.time_index_eq
#print axioms Isomorphism.time_supported_eq
#print axioms canonicalDiagram_isomorphic_injective
#print axioms structuralSentence_exists_unique_permutation
end StackSorting.SparseEndpointMSO
