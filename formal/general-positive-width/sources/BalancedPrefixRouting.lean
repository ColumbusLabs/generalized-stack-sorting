import PrefixRoutingFamily

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}
namespace PrefixRoutingFamily
variable {G : Graph n} {O : RankedOrder n} {r : Fin n} {D : IncomingDemands G O r}
    {Z : Finset (Fin n)} (F : PrefixRoutingFamily G O r D Z)

noncomputable def withSplit (s t : Fin n)
    (p q : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t)
    (hp : ∀ x ∈ p.walk.vertices, rootAllowed G O r s t x)
    (hq : ∀ x ∈ q.walk.vertices, rootAllowed G O r s t x)
    (L R : Finset (DemandTag n))
    (ends : ∀ i ∈ L ∪ R, D.source i = s ∧ D.target i = t) : PrefixRoutingFamily G O r D Z := by
  classical
  let routes := fun i (hi : i ∈ D.indices) =>
    if hL : i ∈ L then p.changeEndpoints (ends i (Finset.mem_union_left _ hL)).1.symm
      (ends i (Finset.mem_union_left _ hL)).2.symm
    else if hR : i ∈ R then q.changeEndpoints (ends i (Finset.mem_union_right _ hR)).1.symm
      (ends i (Finset.mem_union_right _ hR)).2.symm
    else F.pending i hi
  refine ⟨routes,F.fresh,?_,F.fresh_allowed⟩
  intro i hi x hx
  by_cases hL : i ∈ L
  · have he := ends i (Finset.mem_union_left _ hL)
    have hx' : x ∈ p.walk.vertices := by simpa [routes,hL] using hx
    simpa only [he.1,he.2] using hp x hx'
  · by_cases hR : i ∈ R
    · have he := ends i (Finset.mem_union_right _ hR)
      have hx' : x ∈ q.walk.vertices := by simpa [routes,hL,hR] using hx
      simpa only [he.1,he.2] using hq x hx'
    · exact F.pending_allowed i hi x (by simpa [routes,hL,hR] using hx)

/-- The initial family has an actual uniform boundary-traffic bound obtained
by replacing the constructed fiber halves, with no assumed child cap. -/
theorem withSplit_bounded (s t : Fin n)
    (p q : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t)
    (hp : ∀ x ∈ p.walk.vertices, rootAllowed G O r s t x)
    (hq : ∀ x ∈ q.walk.vertices, rootAllowed G O r s t x)
    (shared : ∀ e, e ∈ p.walk.edges → e ∈ q.walk.edges → IsOriginal e.val)
    (S L R : Finset (DemandTag n))
    (ends : ∀ i ∈ L ∪ R, D.source i = s ∧ D.target i = t)
    (hSI : S ⊆ D.indices) (hLS : L ⊆ S) (hRS : R ⊆ S)
    (hdis : Disjoint L R) (hL : L.card = S.card/2) (hR : S.card/2 ≤ R.card)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (hcap : D.indices.card ≤ 2*k^3) (hfiber : D.indices.card ≤ k*k*S.card) :
    (F.withSplit s t p q hp hq L R ends).Bounded k := by
  classical
  let F' := F.withSplit s t p q hp hq L R ends
  let edges := fun i => if hi : i ∈ D.indices then (F'.pending i hi).walk.edges.map Subtype.val else []
  have first : ∀ i ∈ L, edges i = p.walk.edges.map Subtype.val := by
    intro i hi
    have hI := hSI (hLS hi)
    simp [edges,F',withSplit,hI,hi]
  have second : ∀ i ∈ R, edges i = q.walk.edges.map Subtype.val := by
    intro i hi
    have hI := hSI (hRS hi)
    have hn : i ∉ L := fun h => Finset.disjoint_left.mp hdis h hi
    simp [edges,F',withSplit,hI,hn,hi]
  intro z
  have uses : F'.pendingUses z = D.indices.filter (fun i => Sum.inr z ∈ edges i) := by
    ext i
    simp only [pendingUses,Finset.mem_filter]
    constructor
    · rintro ⟨hi,huse⟩
      obtain ⟨hi',huse⟩ := huse
      exact ⟨hi,by simpa [edges,hi] using huse⟩
    · rintro ⟨hi,huse⟩
      exact ⟨hi,hi,by simpa [edges,hi] using huse⟩
  change (F'.pendingUses z).card + (F'.freshUses z).card ≤ 2*k^3
  rw [uses,Nat.add_comm]
  convert actual_boundary_traffic_bound D.indices S L R edges
    (p.walk.edges.map Subtype.val) (q.walk.edges.map Subtype.val) (.inr z) k
    (F'.freshUses z).card hSI hLS hRS hL hR hcap hfiber (F'.freshUses_bound k width z)
    first second (raw_boundary_separate p q shared z) using 1
  congr 2
  ext i
  simp

end PrefixRoutingFamily
end StackSorting.LowPathwidthParts
