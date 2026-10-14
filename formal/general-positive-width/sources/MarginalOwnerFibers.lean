import MarginalAtomRealization

namespace StackSorting.GraphWidth.MarginalA2.Actual
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open FinitePort Nested CapturedLinkExtraction
variable {A : Model} {n t : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)

/-- Actual margin ownership is functional on the literal original vertex. -/
theorem margin_functional {x y z : Base (A := A) (t := t)}
    (hx : Margin D names x z) (hy : Margin D names y z) : x=y := by
  cases x with
  | inl x => exact hx.elim
  | inr x => cases y with
    | inl y => exact hy.elim
    | inr y => cases z with
      | inr z => exact hx.elim
      | inl z =>
        obtain ⟨u,hu,hux⟩ := hx
        obtain ⟨v,hv,hvy⟩ := hy
        have huv := namedVertex_injective names (hu.symm.trans hv)
        subst v
        exact congrArg Sum.inr (hux.symm.trans hvy)

theorem margin_not_edge {x z : Base (A := A) (t := t)} (hx : Margin D names x z) :
    ¬OriginalEdge D names z := by
  cases x with
  | inl x => exact hx.elim
  | inr x => cases z with
    | inr z => exact hx.elim
    | inl z =>
      obtain ⟨u,rfl,_⟩ := hx
      simp [OriginalEdge,outerAtoms,namedVertex,IsEdge]

theorem incidence_base {u e : Base (A := A) (t := t)}
    (h : OriginalIncidence D names u e) : ∃ a, u=Sum.inl a := by
  cases u with
  | inl u => exact ⟨u,rfl⟩
  | inr u => cases e <;> exact h.elim

/-- Edge endpoint rigidity is inherited from original simple incidence IDs. -/
theorem original_pair_rigid {e u v a b : Base (A := A) (t := t)}
    (he : OriginalEdge D names e) (hne : u≠v) (hab : a≠b)
    (hu : OriginalIncidence D names u e) (hv : OriginalIncidence D names v e)
    (ha : OriginalIncidence D names a e) (hb : OriginalIncidence D names b e) :
    (u=a ∧ v=b) ∨ (u=b ∧ v=a) := by
  obtain ⟨u,rfl⟩ := incidence_base D names hu
  obtain ⟨v,rfl⟩ := incidence_base D names hv
  obtain ⟨a,rfl⟩ := incidence_base D names ha
  obtain ⟨b,rfl⟩ := incidence_base D names hb
  cases e with
  | inr e => exact he.elim
  | inl e =>
    have hne' : u≠v := fun h => hne (congrArg Sum.inl h)
    have hab' : a≠b := fun h => hab (congrArg Sum.inl h)
    rcases incident_pair_rigid he hne' hab' hu.2 hv.2 ha.2 hb.2 with h | h
    · exact Or.inl ⟨congrArg Sum.inl h.1,congrArg Sum.inl h.2⟩
    · exact Or.inr ⟨congrArg Sum.inl h.1,congrArg Sum.inl h.2⟩

theorem oldEdgeOwner_functional {e x y : Base (A := A) (t := t)}
    (hx : OldEdgeOwner D names e x) (hy : OldEdgeOwner D names e y) : x=y := by
  obtain ⟨he,u,v,hne,hu,hv,hxu,hxv⟩ := hx
  obtain ⟨_,a,b,hab,ha,hb,hya,hyb⟩ := hy
  rcases original_pair_rigid D names he hne hab hu hv ha hb with h | h
  · exact margin_functional D names hxu (by simpa only [h.1] using hya)
  · exact margin_functional D names hxu (by simpa only [h.1] using hyb)

theorem oldOwner_functional {z x y : Base (A := A) (t := t)}
    (hx : OldOwner D names z x) (hy : OldOwner D names z y) : x=y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact margin_functional D names hx hy
  · exact ((margin_not_edge D names hx) hy.1).elim
  · exact ((margin_not_edge D names hy) hx.1).elim
  · exact oldEdgeOwner_functional D names hx hy

/-- Fiber ownership in the actual ambient output is unique. -/
theorem owner_functional {z x y : Carrier.Actual (A := A) D}
    (hx : outputAtoms D names .owner (Fin.cases z (fun _ => x)))
    (hy : outputAtoms D names .owner (Fin.cases z (fun _ => y))) : x=y := by
  cases z with
  | inl z => cases x with
    | inr x => exact hx.elim
    | inl x => cases y with
      | inr y => exact hy.elim
      | inl y => exact congrArg Sum.inl (oldOwner_functional D names hx hy)
  | inr e => cases x with
    | inr x => exact hx.elim
    | inl x => cases y with
      | inr y => exact hy.elim
      | inl y => exact congrArg Sum.inl (hx.trans hy.symm)

/-- The exact local universe is cut out by the proved owner relation. Auxiliary
outer nodes and crossing original edges belong to no such fiber. -/
abbrev LocalCarrier (x : Fin t) :=
  {z : Carrier.Actual (A := A) D //
    outputAtoms D names .owner (Fin.cases z (fun _ => .inl (node x)))}

theorem localCarriers_disjoint {x y : Fin t} (hne : x≠y)
    (u : LocalCarrier D names x) (v : LocalCarrier D names y) : u.val≠v.val := by
  intro he
  have h := owner_functional D names u.property (by simpa only [he] using v.property)
  exact hne (Sum.inr.inj (Sum.inl.inj h))

#print axioms oldOwner_functional
#print axioms owner_functional
#print axioms localCarriers_disjoint
end StackSorting.GraphWidth.MarginalA2.Actual
