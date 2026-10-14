import SubtreeRoutingSolution
import InitialDemandCases
import OriginalWalkSupport
import FrontierRoutingSupport

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

theorem original_edge_endpoint_walk (G : Graph n) {u v a b : Fin n}
    (he : G.Adj u v) (ha : a = u ∨ a = v) (hb : b = u ∨ b = v) :
    GraphWidth.Walk G.Adj (fun x => x = a ∨ x = b) a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact .refl (Or.inl rfl)
  · exact .step (Or.inl rfl) he (.refl (Or.inr rfl))
  · exact .step (Or.inl rfl) (G.symm he) (.refl (Or.inr rfl))
  · exact .refl (Or.inl rfl)

namespace ChildRoutingSolutions
variable {G : Graph n} {O : RankedOrder n} {r : Fin n} {D : IncomingDemands G O r}
    {k : Nat} {Z : Finset (Fin n)} {hp : RelativePrefix O r Z}
    {F : PrefixRoutingFamily G O r D Z} (C : ChildRoutingSolutions G O r D k Z hp F)

def childSupport (z : Fin n) (hz : Frontier (clippedParent O r) Z z) (i : DemandTag n) (x : Fin n) : Prop :=
  ∃ hi : i ∈ (F.childDemands z (relative_frontier_cone O r Z hp z hz).1).indices,
    x ∈ ((C.child z hz).routes.incoming i hi).support

def insideEdge (c : InitialDemand D) (e : ActiveEdge (CanonicalPrefixInc G O r Z)) (x : Fin n) : Prop :=
  ∃ z hz, e.val = Sum.inr z ∧ Cone O z x ∧ C.childSupport z hz c.tag x

/-- Every actual traversal is replaced either by its original graph edge, or
by the same-index recursively constructed child walk with the exact endpoints. -/
theorem traversal_segment (c : InitialDemand D) (a b : Fin n)
    (e : ActiveEdge (CanonicalPrefixInc G O r Z))
    (htr : (a,e,b) ∈ (c.path F).walk.traversals) :
    GraphWidth.Walk G.Adj (fun x => x = a ∨ x = b ∨ C.insideEdge c e x) a b := by
  have hinc := (c.path F).walk.traversal_incident htr
  have ha := hinc.1.1
  have hb := hinc.2.1
  change PrefixHypertorsoInc G O r Z a e.val at ha
  change PrefixHypertorsoInc G O r Z b e.val at hb
  cases he : e.val with
  | inl uv =>
    rw [he] at ha hb
    exact (original_edge_endpoint_walk G ha.1 ha.2.2.2 hb.2.2.2).mono
      (fun _ h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))
  | inr z =>
    rw [he] at ha hb
    have hz := ha.1
    have hrz := (relative_frontier_cone O r Z hp z hz).1
    have hedge : e ∈ (c.path F).walk.edges := by
      rw [← HWalk.traversal_edges]
      exact List.mem_map.mpr ⟨(a,e,b),htr,rfl⟩
    have hraw : Sum.inr z ∈ (c.path F).walk.edges.map Subtype.val := List.mem_map.mpr ⟨e,hedge,he⟩
    have hi := c.child_mem F z hraw
    have hend := c.child_endpoints F z hrz e he htr
    let R := (C.child z hz).routes
    let w := R.incoming c.tag hi
    have hw : GraphWidth.Walk G.Adj (fun x => x = a ∨ x = b ∨ C.insideEdge c e x)
        ((F.childDemands z hrz).source c.tag) ((F.childDemands z hrz).target c.tag) := by
      apply original_walk_of_support (AdhesionGuidance.originalGraph G) w
      intro x hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      by_cases hxb : x = b
      · exact Or.inr (Or.inl hxb)
      refine Or.inr (Or.inr ⟨z,hz,he,?_,hi,hx⟩)
      exact R.incoming_inside c.tag hi x hx
        (by simpa only [hend.1] using hxa) (by simpa only [hend.2] using hxb)
    simpa only [hend.1,hend.2] using hw

/-- An actual original-edge walk is constructed for each initial demand.
Hidden support is assigned to the unique same-index child route. -/
theorem exists_spliced_walk (c : InitialDemand D) :
    ∃ w : (AdhesionGuidance.originalGraph G).Walk c.source c.target,
      ∀ x ∈ w.support, x ∈ (c.path F).walk.vertices ∨
        ∃ z hz, Cone O z x ∧ C.childSupport z hz c.tag x := by
  have hw := (c.path F).walk.splice_original_walk G.Adj (C.insideEdge c)
    (fun a e b h => C.traversal_segment c a b e h)
  have hmono : GraphWidth.Walk G.Adj
      (fun x => x ∈ (c.path F).walk.vertices ∨ ∃ z hz, Cone O z x ∧ C.childSupport z hz c.tag x)
      c.source c.target := hw.mono (fun x hx => by
    rcases hx with hx | ⟨e,_he,z,hz,_heid,hzx,hroute⟩
    · exact Or.inl hx
    · exact Or.inr ⟨z,hz,hzx,hroute⟩)
  exact exists_simple_walk (AdhesionGuidance.originalGraph G) hmono

noncomputable def splicedWalk (c : InitialDemand D) :
    (AdhesionGuidance.originalGraph G).Walk c.source c.target :=
  Classical.choose (C.exists_spliced_walk c)

theorem spliced_support (c : InitialDemand D) (x : Fin n)
    (hx : x ∈ (C.splicedWalk c).support) :
    x ∈ (c.path F).walk.vertices ∨ ∃ z hz, Cone O z x ∧ C.childSupport z hz c.tag x :=
  Classical.choose_spec (C.exists_spliced_walk c) x hx

end ChildRoutingSolutions
end StackSorting.LowPathwidthParts
