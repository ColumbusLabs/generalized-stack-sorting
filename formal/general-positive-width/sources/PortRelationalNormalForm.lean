import PortNormalForm
import Init.Data.List.Perm
import Init.Data.List.Nat.Pairwise

namespace StackSorting.FinitePort

/-- Relational clauses that use only finitely many slots, endpoint predicates,
and the independent vertex order. No list-index equality is assumed. -/
structure RelationalPortNormalForm {n colors relations} (T : RootedTree n)
    (O : FixedOrder n) (G : Diagram n colors relations) (C : Code n colors relations) : Prop where
  color : ∀ v, (C v).color = G.color v
  valid : ∀ v i, i < (C v).ports.length → ∃ u, readPort T C n v (i+1) = some u
  frontier : ∀ v u, Inherited T G v u ↔
    ∃ i, i < (C v).ports.length ∧ readPort T C n v (i+1) = some u
  ordered : ∀ v i j, i < j → j < (C v).ports.length → ∀ u w,
    readPort T C n v (i+1) = some u → readPort T C n v (j+1) = some w →
    O.vertices.idxOf u < O.vertices.idxOf w
  bits : ∀ v i e, (C v).ports[i]? = some e → ∀ u,
    readPort T C n v (i+1) = some u → ∀ r forward,
      e.bit r forward = if forward then G.rel r v u else G.rel r u v

def readTargets {n colors relations} (T : RootedTree n) (C : Code n colors relations)
    (v : Vertex n) : List (Vertex n) :=
  (List.range (C v).ports.length).map (fun i => (readPort T C n v (i+1)).getD v)

@[simp] theorem length_readTargets {n colors relations} (T : RootedTree n)
    (C : Code n colors relations) (v : Vertex n) :
    (readTargets T C v).length = (C v).ports.length := by simp [readTargets]

theorem RelationalPortNormalForm.readTargets_eq {n colors relations} {T : RootedTree n}
    {O : FixedOrder n} {G : Diagram n colors relations} {C : Code n colors relations}
    (h : RelationalPortNormalForm T O G C) (v : Vertex n) :
    readTargets T C v = inherited T O G v := by
  classical
  have memT (u : Vertex n) : u ∈ readTargets T C v ↔ Inherited T G v u := by
    simp only [readTargets,List.mem_map,List.mem_range]
    constructor
    · rintro ⟨i,hi,he⟩
      obtain ⟨w,hw⟩ := h.valid v i hi
      have hwu : w=u := by simpa only [hw,Option.getD_some] using he
      subst w
      exact (h.frontier v u).mpr ⟨i,hi,hw⟩
    · intro hu
      obtain ⟨i,hi,hr⟩ := (h.frontier v u).mp hu
      exact ⟨i,hi,by simp only [hr,Option.getD_some]⟩
  have sortedT : (readTargets T C v).Pairwise
      (fun u w => O.vertices.idxOf u < O.vertices.idxOf w) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' : i < (C v).ports.length := by simpa using hi
    have hj' : j < (C v).ports.length := by simpa using hj
    obtain ⟨u,hu⟩ := h.valid v i hi'
    obtain ⟨w,hw⟩ := h.valid v j hj'
    simpa only [readTargets,List.getElem_map,List.getElem_range,hu,hw,Option.getD_some] using
      h.ordered v i j hij hj' u w hu hw
  have sortedO : O.vertices.Pairwise (fun u w => O.vertices.idxOf u < O.vertices.idxOf w) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [O.nodup.idxOf_getElem i hi,O.nodup.idxOf_getElem j hj] using hij
  have sortedI : (inherited T O G v).Pairwise
      (fun u w => O.vertices.idxOf u < O.vertices.idxOf w) :=
    sortedO.filter _
  have nodupT : (readTargets T C v).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact sortedT.imp (fun hh he => by subst he; exact Nat.lt_irrefl _ hh)
  have nodupI : (inherited T O G v).Nodup := (bag_nodup T O G v).tail
  have perm : (readTargets T C v).Perm (inherited T O G v) :=
    (List.perm_ext_iff_of_nodup nodupT nodupI).mpr (fun u => by rw [memT,mem_inherited])
  exact perm.eq_of_pairwise (fun _ _ _ _ hab hba => False.elim (Nat.lt_asymm hab hba)) sortedT sortedI

/-- Concrete relational normality forces the exact actual port encoding. -/
theorem RelationalPortNormalForm.to_normalForm {n colors relations} {T : RootedTree n}
    {O : FixedOrder n} {G : Diagram n colors relations} {C : Code n colors relations}
    (h : RelationalPortNormalForm T O G C) : PortNormalForm T O G C := by
  refine ⟨h.color,?_,?_,h.bits⟩
  · intro v
    simpa using congrArg List.length (h.readTargets_eq v)
  · intro v i hi hj
    obtain ⟨u,hu⟩ := h.valid v i hi
    have he := congrArg (fun l : List (Vertex n) => l[i]?) (h.readTargets_eq v)
    have hh : i < (readTargets T C v).length := by simpa using hi
    rw [List.getElem?_eq_getElem hh,List.getElem?_eq_getElem hj] at he
    have hu' : u=(inherited T O G v)[i] := by
      apply Option.some.inj
      simpa only [readTargets,List.getElem_map,List.getElem_range,hu,Option.getD_some] using he
    simpa only [hu'] using hu

theorem RelationalPortNormalForm.eq_encode {n colors relations} {T : RootedTree n}
    {O : FixedOrder n} {G : Diagram n colors relations} {C : Code n colors relations}
    (h : RelationalPortNormalForm T O G C) : C=encode T O G := h.to_normalForm.eq_encode

#print axioms RelationalPortNormalForm.readTargets_eq
#print axioms RelationalPortNormalForm.eq_encode
end StackSorting.FinitePort
