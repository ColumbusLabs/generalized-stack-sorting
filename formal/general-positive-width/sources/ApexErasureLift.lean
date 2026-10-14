import InheritedBranchLift
import BoundedSourceTree

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort PlaneGrid

/-- Erase the apex after decoding the actual source-tree numbering. -/
def eraseApexLabels {n m} (R : FiniteCode (Fin (n+1)) (n+1))
    (labels : Fin m → List (Fin (n+1))) (q : Fin m) : List (Fin n) :=
  (labels q).filterMap (fun a => SourceApex.decode (R.decode a))

theorem mem_eraseApexLabels {n m} (R : FiniteCode (Fin (n+1)) (n+1))
    (labels : Fin m → List (Fin (n+1))) (q : Fin m) (v : Fin n) :
    v ∈ eraseApexLabels R labels q ↔ R.encode v.succ ∈ labels q := by
  simp only [eraseApexLabels,List.mem_filterMap,SourceApex.decode_eq_some_iff]
  constructor
  · rintro ⟨a,ha,he⟩
    have h : a=R.encode v.succ := (R.encode_decode a).symm.trans (congrArg R.encode he)
    exact h ▸ ha
  · intro h
    exact ⟨R.encode v.succ,h,R.decode_encode _⟩

/-- Dropping the unlabeled apex preserves coverage, all source edges, and
connected fibers. It does not assume that an arbitrary minor projection works. -/
def eraseApexLift {n m} (G : Graph n) (anchor : Fin n → Prop) (H : Graph m)
    (R : FiniteCode (Fin (n+1)) (n+1))
    (L : ConnectedLift H (reindexGraph (SourceApex.graph G anchor) R)) : ConnectedLift H G where
  labels := eraseApexLabels R L.labels
  vertex := by
    intro v
    obtain ⟨q,hq⟩ := L.vertex (R.encode v.succ)
    exact ⟨q,(mem_eraseApexLabels R L.labels q v).mpr hq⟩
  edge := by
    intro u v huv
    have he : (reindexGraph (SourceApex.graph G anchor) R).Adj (R.encode u.succ) (R.encode v.succ) := by
      change (SourceApex.graph G anchor).Adj (R.decode (R.encode u.succ)) (R.decode (R.encode v.succ))
      rw [R.decode_encode,R.decode_encode]
      exact huv
    obtain ⟨q,hu,hv⟩ | ⟨q,r,hqr,hu,hv⟩ := L.edge he
    · exact Or.inl ⟨q,(mem_eraseApexLabels R L.labels q u).mpr hu,
        (mem_eraseApexLabels R L.labels q v).mpr hv⟩
    · exact Or.inr ⟨q,r,hqr,(mem_eraseApexLabels R L.labels q u).mpr hu,
        (mem_eraseApexLabels R L.labels r v).mpr hv⟩
  fiber := by
    intro v q r hq hr
    have w := L.fiber ((mem_eraseApexLabels R L.labels q v).mp hq)
      ((mem_eraseApexLabels R L.labels r v).mp hr)
    exact w.mono (fun z hz => (mem_eraseApexLabels R L.labels z v).mpr hz)

noncomputable def sourceTreeCode {n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : SourceApex.Radius G anchor k) : FiniteCode (Fin (n+1)) (n+1) :=
  let N := (SourceApex.reachable G anchor radius).numbered
  ⟨N.index,N.label,N.label_index,N.index_label⟩

end StackSorting.GraphWidth.UCurve.SubdivisionTree
