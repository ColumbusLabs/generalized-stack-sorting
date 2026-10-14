import ReplacementExteriorBag

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}

namespace ReplacementFrame

theorem old_removed_touch_of_new_reach (R : ReplacementFrame old inserted s t removed)
    (x y : V) (hx : x ∈ R.oldVertices) (hy : y ∈ R.newVertices)
    (hxy : SameCutedgeComponent (ReplacementIncidence old inserted removed) s t x y) :
    ComponentTouches (inc := old) (s := s) (t := t) x (.cut removed) := by
  classical
  by_contra hn
  have avoids : ∀ z, SameCutedgeComponent old s t x z → ¬ old z removed :=
    fun z hxz hz => hn ⟨z,hz,hxz⟩
  have hold := unaffected_component_replacement_subset removed R.oldVertices R.newVertices R.anchor
    R.anchor_incident R.old_support R.new_support R.overlap R.source_old R.sink_old x hx avoids hxy
  have hyold := old_component_supported R.oldVertices R.old_support hx hold
  exact hn ⟨y,R.overlap y hyold hy,hold⟩

/-- Any old boundary touched by a new component meeting K was adjacent to the
removed edge in the old network. The first step constructs the two old touches. -/
theorem old_joint_touch_from_new_boundary (R : ReplacementFrame old inserted s t removed)
    (x : V) (hx : x ∈ R.newVertices) (b : CutBoundary E) (hne : b ≠ .cut removed)
    (hxb : ComponentTouches (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) x (survivingBoundary (F := F) b hne)) :
    ∃ y, ComponentTouches (inc := old) (s := s) (t := t) y (.cut removed) ∧
      ComponentTouches (inc := old) (s := s) (t := t) y b := by
  cases b with
  | source =>
    have hsx := sameCutedgeComponent_symm (ReplacementIncidence old inserted removed) s t hxb
    exact ⟨s,R.old_removed_touch_of_new_reach s x R.source_old hx hsx,
      sameCutedgeComponent_refl old s t s⟩
  | sink =>
    have htx := sameCutedgeComponent_symm (ReplacementIncidence old inserted removed) s t hxb
    exact ⟨t,R.old_removed_touch_of_new_reach t x R.sink_old hx htx,
      sameCutedgeComponent_refl old s t t⟩
  | cut e =>
    obtain ⟨y,hy,hxy⟩ := hxb
    have hyx := sameCutedgeComponent_symm (ReplacementIncidence old inserted removed) s t hxy
    exact ⟨y,R.old_removed_touch_of_new_reach y x (R.old_support y e hy) hx hyx,
      y,hy,sameCutedgeComponent_refl old s t y⟩

end ReplacementFrame

/-- Two distinct touched boundary indices are neighbors, with no selected
component label or classification existence premise needed. -/
theorem touched_boundary_indices_neighbor [DecidableEq E] (p : Path old s t)
    (x : V) (i j : Fin (boundaryTrace p).length) (hne : i ≠ j)
    (hi : ComponentTouches (inc := old) (s := s) (t := t) x ((boundaryTrace p).get i))
    (hj : ComponentTouches (inc := old) (s := s) (t := t) x ((boundaryTrace p).get j)) :
    i.val+1=j.val ∨ j.val+1=i.val := by
  have valid : ∀ a : Fin (boundaryTrace p).length,
      BoundaryValid (inc := old) (s := s) (t := t) ((boundaryTrace p).get a) :=
    fun a => (mem_boundaryTrace p _).mp (List.get_mem _ a)
  have ordered : ∀ a b : Fin (boundaryTrace p).length, a < b →
      ComponentTouches (inc := old) (s := s) (t := t) x ((boundaryTrace p).get a) →
      ComponentTouches (inc := old) (s := s) (t := t) x ((boundaryTrace p).get b) →
      a.val+1=b.val := by
    intro a b hab hxa hxb
    apply (boundaryAdjacent_get_iff p a b).mp
    refine ⟨(boundaryTrace_get_before p a b).mpr hab,?_⟩
    rintro ⟨c,hc,hac,hcb⟩
    exact component_boundaries_no_gap p x (valid a) hc (valid b) hac hcb hxa hxb
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact Or.inl (ordered i j hij hi hj)
  · exact Or.inr (ordered j i hji hj hi)

/-- Distinct old neighbors of the removed boundary cannot themselves have an
old bridge. This handles the merged two-old-boundary replacement case without
assuming a precomputed insertion order for all new cutedges. -/
theorem distinct_boundary_neighbors_have_no_joint_component [DecidableEq E]
    (p : Path old s t) (r i j : Fin (boundaryTrace p).length) (hij : i ≠ j)
    (hri : r.val+1=i.val ∨ i.val+1=r.val)
    (hrj : r.val+1=j.val ∨ j.val+1=r.val) (x : V)
    (hi : ComponentTouches (inc := old) (s := s) (t := t) x ((boundaryTrace p).get i))
    (hj : ComponentTouches (inc := old) (s := s) (t := t) x ((boundaryTrace p).get j)) : False := by
  have hnext := touched_boundary_indices_neighbor p x i j hij hi hj
  have hneval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases hri with hri | hri <;> rcases hrj with hrj | hrj <;>
    rcases hnext with hnext | hnext <;> omega

end FiniteFlow.Hypergraph
