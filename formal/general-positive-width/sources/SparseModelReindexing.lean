import SparseModelIsomorphism

namespace StackSorting.SparseEndpointMSO
open Generalized

/-- A chronological enumeration of the original named vertices. The original
domain list may be in any order; repeated representation entries do not count
as extra vertices. Deriving this witness from the path sentence is separate. -/
structure ChronologicalEnumeration (D : Model) (order : List Nat) : Prop where
  nodup : order.Nodup
  covers : ∀ x, x ∈ order ↔ x ∈ D.domain
  successor : ∀ i (hi : i < order.length), ∀ j (hj : j < order.length),
    D.S order[i] order[j] ↔ i + 1 = j

def atTime (order : List Nat) (i : Nat) : Nat := order[i]?.getD 0

theorem atTime_eq_get {order : List Nat} {i : Nat} (hi : i < order.length) :
    atTime order i = order[i] := by simp [atTime, List.getElem?_eq_getElem hi]

theorem atTime_idxOf {order : List Nat} {x : Nat} (hx : x ∈ order) :
    atTime order (order.idxOf x) = x := by
  rw [atTime_eq_get (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]

def reindexed (D : Model) (order : List Nat) : Model where
  domain := List.range order.length
  I i := D.I (atTime order i)
  R i := D.R (atTime order i)
  S i j := D.S (atTime order i) (atTime order j)
  M i j := D.M (atTime order i) (atTime order j)

def chronologicalIsomorphism {D : Model} {order : List Nat}
    (he : ChronologicalEnumeration D order) : Isomorphism D (reindexed D order) where
  toFun := order.idxOf
  invFun := atTime order
  to_mem x hx := List.mem_range.mpr (List.idxOf_lt_length_of_mem ((he.covers x).mpr hx))
  inv_mem i hi := by
    have hb : i < order.length := List.mem_range.mp hi
    exact (he.covers _).mp (by rw [atTime_eq_get hb]; exact List.getElem_mem hb)
  left_inv x hx := atTime_idxOf ((he.covers x).mpr hx)
  right_inv i hi := by
    have hb : i < order.length := List.mem_range.mp hi
    rw [atTime_eq_get hb, he.nodup.idxOf_getElem i hb]
  insert_iff x hx := by
    change D.I x ↔ D.I (atTime order (order.idxOf x))
    rw [atTime_idxOf ((he.covers x).mpr hx)]
  remove_iff x hx := by
    change D.R x ↔ D.R (atTime order (order.idxOf x))
    rw [atTime_idxOf ((he.covers x).mpr hx)]
  successor_iff x hx y hy := by
    change D.S x y ↔ D.S (atTime order (order.idxOf x)) (atTime order (order.idxOf y))
    rw [atTime_idxOf ((he.covers x).mpr hx), atTime_idxOf ((he.covers y).mpr hy)]
  matching_iff x hx y hy := by
    change D.M x y ↔ D.M (atTime order (order.idxOf x)) (atTime order (order.idxOf y))
    rw [atTime_idxOf ((he.covers x).mpr hx), atTime_idxOf ((he.covers y).mpr hy)]

theorem reindexed_timePath {D : Model} {order : List Nat}
    (he : ChronologicalEnumeration D order) : TimePath (reindexed D order) order.length := by
  refine ⟨rfl, ?_⟩
  intro x hx y hy
  have hxb : x < order.length := List.mem_range.mp hx
  have hyb : y < order.length := List.mem_range.mp hy
  change D.S (atTime order x) (atTime order y) ↔ x + 1 = y
  rw [atTime_eq_get hxb, atTime_eq_get hyb]
  exact he.successor x hxb y hyb

/-- Intrinsic forwardness uses the actual successor reachability relation,
not comparison of the arbitrary natural numbers used as vertex names. -/
structure PathMatchingAxioms (D : Model) : Prop where
  partition : ∀ x ∈ D.domain, (D.I x ∨ D.R x) ∧ ¬ (D.I x ∧ D.R x)
  symmetric : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.M x y → D.M y x
  perfect : ∀ x ∈ D.domain, ∃ y ∈ D.domain, D.M x y ∧
    ∀ z ∈ D.domain, D.M x z → z = y
  opposite : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.M x y → (D.I x ↔ D.R y)
  forward : ∀ x ∈ D.domain, ∀ y ∈ D.domain, D.I x → D.M x y →
    x ≠ y ∧ ClosedReach D x y

theorem PathMatchingAxioms.to_indexed {D E : Model} {length : Nat}
    (h : PathMatchingAxioms D) (iso : Isomorphism D E) (hp : TimePath E length) :
    MatchingAxioms E where
  partition x hx := by
    have hh := h.partition _ (iso.inv_mem x hx)
    have hi : E.I x ↔ D.I (iso.invFun x) := iso.symm.insert_iff x hx
    have hr : E.R x ↔ D.R (iso.invFun x) := iso.symm.remove_iff x hx
    rw [← hi, ← hr] at hh
    exact hh
  symmetric x hx y hy hm := by
    apply (iso.symm.matching_iff y hy x hx).mpr
    exact h.symmetric _ (iso.inv_mem x hx) _ (iso.inv_mem y hy)
      ((iso.symm.matching_iff x hx y hy).mp hm)
  perfect x hx := by
    obtain ⟨y, hy, hm, hu⟩ := h.perfect _ (iso.inv_mem x hx)
    refine ⟨iso.toFun y, iso.to_mem y hy, ?_, ?_⟩
    · have hh := (iso.matching_iff _ (iso.inv_mem x hx) y hy).mp hm
      simpa only [iso.right_inv x hx] using hh
    · intro z hz hmatch
      have hh := (iso.symm.matching_iff x hx z hz).mp hmatch
      have he := hu _ (iso.inv_mem z hz) hh
      have hf := congrArg iso.toFun he
      simpa only [iso.right_inv z hz] using hf
  opposite x hx y hy hm := by
    have hh := h.opposite _ (iso.inv_mem x hx) _ (iso.inv_mem y hy)
      ((iso.symm.matching_iff x hx y hy).mp hm)
    exact (iso.symm.insert_iff x hx).trans (hh.trans (iso.symm.remove_iff y hy).symm)
  forward x hx y hy hi hm := by
    obtain ⟨hne, hreach⟩ := h.forward _ (iso.inv_mem x hx) _ (iso.inv_mem y hy)
      ((iso.symm.insert_iff x hx).mp hi) ((iso.symm.matching_iff x hx y hy).mp hm)
    have hr := (iso.closedReach (iso.inv_mem x hx) (iso.inv_mem y hy)).mp hreach
    rw [iso.right_inv x hx, iso.right_inv y hy,
      closedReach_iff_walk E hx, walk_iff_le E length hp hx hy] at hr
    have hxy : x ≠ y := fun he => hne (congrArg iso.invFun he)
    omega

theorem LazyBoundary.transport {D E : Model} (h : LazyBoundary D)
    (iso : Isomorphism D E) : LazyBoundary E := by
  intro x hx y hy hi hr hs
  apply (iso.symm.matching_iff x hx y hy).mpr
  exact h _ (iso.inv_mem x hx) _ (iso.inv_mem y hy)
    ((iso.symm.insert_iff x hx).mp hi) ((iso.symm.remove_iff y hy).mp hr)
    ((iso.symm.successor_iff x hx y hy).mp hs)

/-- Arbitrary vertex names are supported by an explicit finite-domain
isomorphism to the decoded canonical permutation diagram. -/
theorem enumeratedModel_exists_canonical {D : Model} {order : List Nat}
    (he : ChronologicalEnumeration D order) (h : PathMatchingAxioms D)
    (hl : LazyBoundary D) :
    ∃ output, output.Perm (List.range (insertionTokens (reindexed D order)).length) ∧
      Nonempty (Isomorphism D (canonicalDiagram output)) := by
  let iso := chronologicalIsomorphism he
  have hp := reindexed_timePath he
  have hm := h.to_indexed iso hp
  have hb := hl.transport iso
  refine ⟨decodedPermutation (reindexed D order), decodedPermutation_perm hp hm, ?_⟩
  have hh : supported (reindexed D order) = canonicalDiagram (decodedPermutation (reindexed D order)) :=
    supported_eq_canonicalDiagram hp hm hb
  exact ⟨hh ▸ iso.trans (supportIsomorphism _)⟩

/-- Recognition is invariant under arbitrary chronological renaming, for all
widths and including the empty domain when an empty enumeration is supplied. -/
theorem enumeratedModel_generated_iff {D : Model} {order : List Nat} {r s : Nat}
    (he : ChronologicalEnumeration D order) (h : PathMatchingAxioms D)
    (hl : LazyBoundary D) :
    Generalized.Run r s [] (List.range (insertionTokens (reindexed D order)).length)
      (decodedPermutation (reindexed D order)) [] ↔ Satisfies D (eligibilitySentence r s) := by
  let iso := chronologicalIsomorphism he
  have hp := reindexed_timePath he
  exact (sparseModel_generated_iff hp (h.to_indexed iso hp) (hl.transport iso)).trans
    (iso.satisfies _).symm

#print axioms chronologicalIsomorphism
#print axioms reindexed_timePath
#print axioms enumeratedModel_exists_canonical
#print axioms enumeratedModel_generated_iff
end StackSorting.SparseEndpointMSO
