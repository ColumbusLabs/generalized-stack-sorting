import IndexedRoutingDemands
import IndexedEndpointLoad

namespace StackSorting.LowPathwidthParts
open FiniteFlow.Hypergraph PrefixGrowth

variable {ι V E : Type} [DecidableEq ι] [DecidableEq E]

omit [DecidableEq ι] in
/-- A boundary edge cannot be used by both distinguished paths, so the actual
indexed use set misses one of the two assigned halves. -/
theorem actual_use_avoids_half (I L R : Finset ι) (edges : ι → List E)
    (first second : List E) (e : E)
    (hfirst : ∀ i ∈ L, edges i = first) (hsecond : ∀ i ∈ R, edges i = second)
    (hseparate : ¬ (e ∈ first ∧ e ∈ second)) :
    Disjoint (I.filter (fun i => e ∈ edges i)) L ∨
      Disjoint (I.filter (fun i => e ∈ edges i)) R := by
  by_cases he : e ∈ first
  · right
    apply Finset.disjoint_left.mpr
    intro i hi hiR
    have hi' := (Finset.mem_filter.mp hi).2
    rw [hsecond i hiR] at hi'
    exact hseparate ⟨he,hi'⟩
  · left
    apply Finset.disjoint_left.mpr
    intro i hi hiL
    have hi' := (Finset.mem_filter.mp hi).2
    rw [hfirst i hiL] at hi'
    exact he hi'

/-- The path-level separation premise is derived for each actual boundary ID
from the original-edge-only overlap guaranteed by 5.2. -/
theorem canonical_boundary_separate {n : Nat} {G : GraphWidth.Graph n}
    {O : SameVertexForest.RankedOrder n} {r s t z : Fin n} {Z : Finset (Fin n)}
    (p q : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t)
    (hshared : ∀ e, e ∈ p.walk.edges → e ∈ q.walk.edges → IsOriginal e.val)
    (e : ActiveEdge (CanonicalPrefixInc G O r Z)) (he : e.val = .inr z) :
    ¬ (e ∈ p.walk.edges ∧ e ∈ q.walk.edges) := by
  rintro ⟨hp,hq⟩
  obtain ⟨a,b,hab⟩ := hshared e hp hq
  rw [he] at hab
  cases hab

/-- The actual indexed edge-use count plus the new root demand count satisfies
the cubic cap. It follows from path incidence and constructed balanced fiber
data, rather than assuming the child load bound. -/
theorem actual_boundary_traffic_bound
    (I S L R : Finset ι) (edges : ι → List E) (first second : List E)
    (e : E) (k newCount : Nat)
    (hSI : S ⊆ I) (hLS : L ⊆ S) (hRS : R ⊆ S)
    (hL : L.card = S.card / 2) (hR : S.card / 2 ≤ R.card)
    (hcap : I.card ≤ 2*k^3) (hfiber : I.card ≤ k*k*S.card)
    (hnew : newCount ≤ k)
    (hfirst : ∀ i ∈ L, edges i = first) (hsecond : ∀ i ∈ R, edges i = second)
    (hseparate : ¬ (e ∈ first ∧ e ∈ second)) :
    newCount + (I.filter (fun i => e ∈ edges i)).card ≤ 2*k^3 := by
  have havoid := actual_use_avoids_half I L R edges first second e hfirst hsecond hseparate
  exact (IndexedEndpointLoad.child_load_of_avoids_half I S L R
    (I.filter (fun i => e ∈ edges i)) k newCount hSI hLS hRS hL hR
    (Finset.filter_subset _ _) havoid hnew).trans
    (IndexedEndpointLoad.cubic_load_bound k I.card S.card hcap hfiber)

end StackSorting.LowPathwidthParts
