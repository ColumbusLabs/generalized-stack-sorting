import ApexErasureLift

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree
open FinitePort PlaneGrid

/-- Distinct original-source labels on a full extension root path inherit the
actual shortest-source-tree bound. The apex contributes no label. -/
theorem inherited_source_root_bound {m n k} (G : Graph n) (anchor : Fin n → Prop)
    (radius : SourceApex.Radius G anchor k) (hk : 0<k) {H : Graph m} {root : Fin m}
    (P : PrescribedPrefix H.Adj root) (E : PreservingSpanningTree P)
    (old : Fin P.vertices.length → Fin (n+1))
    (hparent : ∀ i, Ancestor (SourceApex.reachable G anchor radius).numbered.tree
      (old (P.tree.parent i)) (old i)) (i : Fin m) :
    (rootPathLabels E.spanning.tree
      (eraseApexLabels (sourceTreeCode G anchor radius) (fun z => [inheritedBranch P E old z])) i).length≤k := by
  let R := SourceApex.reachable G anchor radius
  let ls : Fin (n+1) → List (Fin n) := fun a => (SourceApex.decode (R.numbered.label a)).toList
  have hlabels : eraseApexLabels (sourceTreeCode G anchor radius) (fun z => [inheritedBranch P E old z])=
      (fun z => ls (inheritedBranch P E old z)) := by
    funext z
    simp only [eraseApexLabels,List.filterMap_cons,List.filterMap_nil]
    cases SourceApex.decode (R.numbered.label (inheritedBranch P E old z)) <;> rfl
  rw [hlabels]
  apply SourceApex.source_ancestor_bound G anchor radius hk (inheritedBranch P E old i)
    _ (uniqueList_nodup _)
  intro v hv
  obtain ⟨a,ha,hv⟩ := inherited_root_label_ancestor P E old R.numbered.tree hparent ls i v hv
  have hd : SourceApex.decode (R.numbered.label a)=some v := Option.mem_toList.mp hv
  have he : R.numbered.label a=v.succ := (SourceApex.decode_eq_some_iff _ _).mp hd
  have hai : a=R.numbered.index v.succ := by rw [← he,R.numbered.index_label]
  exact hai ▸ ha

end StackSorting.GraphWidth.UCurve.SubdivisionTree
