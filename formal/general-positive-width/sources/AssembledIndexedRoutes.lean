import SplicedWalkContainment
import SelectedAssemblyTransport

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}
namespace ChildRoutingSolutions
variable {G : Graph n} {O : RankedOrder n} {r : Fin n} {D : IncomingDemands G O r}
    {k : Nat} {Z : Finset (Fin n)} {hp : RelativePrefix O r Z}
    {F : PrefixRoutingFamily G O r D Z} (C : ChildRoutingSolutions G O r D k Z hp F)

noncomputable def assembledSelection : RootedSelection O r :=
  assembleSelection O r Z hp (fun z hz => (C.child z hz).selected)

theorem nonroot_child {a : Fin n} (ha : a ∈ C.assembledSelection.nodes) (har : a ≠ r) :
    ∃ z hz, a ∈ (C.child z hz).selected.nodes := by
  exact ((assembled_mem O r Z hp (fun z hz => (C.child z hz).selected) a).mp ha).resolve_left har

noncomputable def outgoing (a : Fin n) (ha : a ∈ C.assembledSelection.nodes)
    (v : Fin n) (hv : v ∈ regionAdhesionSet G O a) :
    (AdhesionGuidance.originalGraph G).Walk a v := by
  classical
  by_cases har : a = r
  · subst a
    exact C.splicedWalk (.inr ⟨v,hv⟩)
  · let z := Classical.choose (C.nonroot_child ha har)
    let hz := Classical.choose (Classical.choose_spec (C.nonroot_child ha har))
    exact (C.child z hz).routes.outgoing a
      (Classical.choose_spec (Classical.choose_spec (C.nonroot_child ha har))) v hv

theorem outgoing_inside (a : Fin n) (ha : a ∈ C.assembledSelection.nodes)
    (v : Fin n) (hv : v ∈ regionAdhesionSet G O a) (x : Fin n)
    (hx : x ∈ (C.outgoing a ha v hv).support) (hxv : x ≠ v) : Cone O a x := by
  classical
  by_cases har : a = r
  · subst a
    simp [outgoing] at hx
    by_cases hxr : x = r
    · exact Or.inr hxr.symm
    · exact C.spliced_inside (.inr ⟨v,hv⟩) x hx hxr hxv
  · simp only [outgoing,dite_eq_right har] at hx
    exact (C.child _ _).routes.outgoing_inside a _ v hv x hx hxv

noncomputable def assembledRoutes : IndexedRoutes G O r D C.assembledSelection where
  incoming i hi := C.splicedWalk (.inl ⟨i,hi⟩)
  outgoing := C.outgoing
  incoming_inside i hi x hx hs ht := C.spliced_inside (.inl ⟨i,hi⟩) x hx hs ht
  outgoing_inside := C.outgoing_inside

/-- Child routes are inherited literally; the chosen witness of the frontier
cone cannot change them because distinct frontier cones are disjoint. -/
theorem outgoing_child (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (a : Fin n) (ha : a ∈ (C.child z hz).selected.nodes)
    (hglobal : a ∈ C.assembledSelection.nodes) (v : Fin n)
    (hv : v ∈ regionAdhesionSet G O a) :
    C.outgoing a hglobal v hv = (C.child z hz).routes.outgoing a ha v hv := by
  classical
  have hza := (C.child z hz).selected.inside a ha
  have hra := cone_trans O (Or.inl (relative_frontier_cone O r Z hp z hz).1) hza
  have har : a ≠ r := by
    intro he
    rcases hra with hr | hr
    · exact O.irrefl r (by simpa only [he] using hr)
    · have hzr : Cone O z r := by simpa only [he] using hza
      rcases hzr with h | h
      · exact O.irrefl r (O.trans (relative_frontier_cone O r Z hp z hz).1 h)
      · exact O.irrefl r (by simpa only [h] using (relative_frontier_cone O r Z hp z hz).1)
  simp only [outgoing,dite_eq_right har]
  let w := Classical.choose (C.nonroot_child hglobal har)
  let hw := Classical.choose (Classical.choose_spec (C.nonroot_child hglobal har))
  have ha' := Classical.choose_spec (Classical.choose_spec (C.nonroot_child hglobal har))
  have he : w = z := frontier_cones_disjoint O r Z hp hw hz
    ((C.child w hw).selected.inside a ha') hza
  subst z
  rfl

end ChildRoutingSolutions
end StackSorting.LowPathwidthParts
