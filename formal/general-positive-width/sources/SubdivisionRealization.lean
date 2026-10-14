import SubdivisionParent

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree

/-- Ordinary finite subdivision data, with actual target graph edges and
vertex-disjoint simple route interiors. No tree or label conclusion occurs. -/
structure Realization {n m} (G : Graph n) (H : Graph m) extends RouteLengths G where
  point : Fin n → Fin m
  point_injective : Function.Injective point
  pointAt : (e : OrderedEdge G) → Fin (length e+1) → Fin m
  first : ∀ e, pointAt e ⟨0,by omega⟩=point e.low
  last : ∀ e, pointAt e ⟨length e,by omega⟩=point e.high
  path_injective : ∀ e, Function.Injective (pointAt e)
  step : ∀ e (i : Fin (length e)), H.Adj (pointAt e ⟨i.val,by omega⟩) (pointAt e ⟨i.val+1,by omega⟩)
  avoids : ∀ e (i : Fin (length e+1)), 0<i.val → i.val<length e → ∀ v, pointAt e i≠point v
  disjoint : ∀ e f (i : Fin (length e+1)) (j : Fin (length f+1)),
    0<i.val → i.val<length e → 0<j.val → j.val<length f → pointAt e i=pointAt f j → e=f

def Realization.embed {n m} {G : Graph n} {H : Graph m} (S : Realization G H) :
    Vertex S.toRouteLengths → Fin m
  | .original v => S.point v
  | .interior e a => S.pointAt e ⟨a.val+1,by have := a.isLt; omega⟩

theorem Realization.embed_injective {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) : Function.Injective S.embed := by
  intro x y he
  cases x with
  | original v =>
    cases y with
    | original w => exact congrArg Vertex.original (S.point_injective he)
    | interior e a =>
      exact False.elim (S.avoids e ⟨a.val+1,by have := a.isLt; omega⟩
        (by dsimp; omega) (by dsimp; have := a.isLt; omega) v he.symm)
  | interior e a =>
    cases y with
    | original v =>
      exact False.elim (S.avoids e ⟨a.val+1,by have := a.isLt; omega⟩
        (by dsimp; omega) (by dsimp; have := a.isLt; omega) v he)
    | interior f b =>
      have hef : e=f := S.disjoint e f ⟨a.val+1,by have := a.isLt; omega⟩
        ⟨b.val+1,by have := b.isLt; omega⟩ (by dsimp; omega) (by dsimp; have := a.isLt; omega)
        (by dsimp; omega) (by dsimp; have := b.isLt; omega) he
      subst f
      have hab : a=b := by
        apply Fin.ext
        have hh := congrArg Fin.val (S.path_injective e he)
        change a.val+1=b.val+1 at hh
        omega
      subst b
      rfl

theorem Realization.length_bound {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (e : OrderedEdge G) : S.length e<m := by
  have hn : ((List.finRange (S.length e+1)).map (S.pointAt e)).Nodup :=
    (List.nodup_finRange _).map (S.pointAt e) (fun _ _ hn he => hn (S.path_injective e he))
  have h := hn.length_le_of_subset (l₂ := List.finRange m) (fun x _ => List.mem_finRange x)
  simp only [List.length_map,List.length_finRange] at h
  omega


theorem Realization.parent_original_adj {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : FinitePort.RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (v : Fin n) (hv : v.val≠0) :
    H.Adj (S.embed (.original v)) (S.embed (parent S.toRouteLengths T he (.original v))) := by
  classical
  let e := parentEdge T he v hv
  have hl := S.positive e
  have hs := S.step e ⟨S.length e-1,by omega⟩
  have hend : (⟨S.length e-1+1,by omega⟩ : Fin (S.length e+1))=⟨S.length e,by omega⟩ := by
    apply Fin.ext; dsimp; omega
  rw [hend,S.last] at hs
  change H.Adj (S.pointAt e ⟨S.length e-1,by omega⟩) (S.point v) at hs
  have hp : S.embed (parent S.toRouteLengths T he (.original v))=S.pointAt e ⟨S.length e-1,by omega⟩ := by
    simp only [parent,dite_eq_right hv]
    split
    · rename_i hl'
      change 1<S.length e at hl'
      change S.pointAt e ⟨S.length e-2+1,_⟩=S.pointAt e ⟨S.length e-1,_⟩
      congr 1
      apply Fin.ext; dsimp; omega
    · rename_i hl'
      change S.point (T.parent v)=S.pointAt e ⟨S.length e-1,_⟩
      have hz : (⟨S.length e-1,by omega⟩ : Fin (S.length e+1))=⟨0,by omega⟩ := by
        apply Fin.ext; dsimp; change ¬1<S.length e at hl'; omega
      rw [hz,S.first]
      rfl
  rw [hp]
  exact H.symm hs

theorem Realization.parent_interior_adj {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (T : FinitePort.RootedTree n)
    (he : ∀ v, v.val≠0 → G.Adj (T.parent v) v) (e : OrderedEdge G)
    (a : Fin (S.length e-1)) :
    H.Adj (S.embed (.interior e a)) (S.embed (parent S.toRouteLengths T he (.interior e a))) := by
  classical
  have ha := a.isLt
  by_cases ht : IsTreeEdge T e
  · have hp : S.embed (parent S.toRouteLengths T he (.interior e a))=S.pointAt e ⟨a.val,by omega⟩ := by
      simp only [parent,ite_eq_left ht]
      split
      · rename_i hz
        change S.point e.low=S.pointAt e ⟨a.val,_⟩
        have hi : (⟨a.val,by omega⟩ : Fin (S.length e+1))=⟨0,by omega⟩ := Fin.ext hz
        rw [hi,S.first]
      · rename_i hz
        change S.pointAt e ⟨a.val-1+1,_⟩=S.pointAt e ⟨a.val,_⟩
        congr 1
        apply Fin.ext; dsimp; omega
    rw [hp]
    exact H.symm (S.step e ⟨a.val,by omega⟩)
  · have hp : S.embed (parent S.toRouteLengths T he (.interior e a))=S.pointAt e ⟨a.val+2,by omega⟩ := by
      simp only [parent,ite_eq_right ht]
      split
      · rename_i hz
        change S.point e.high=S.pointAt e ⟨a.val+2,_⟩
        have hi : (⟨a.val+2,by omega⟩ : Fin (S.length e+1))=⟨S.length e,by omega⟩ := by
          apply Fin.ext; dsimp; omega
        rw [hi,S.last]
      · rfl
    rw [hp]
    exact S.step e ⟨a.val+1,by omega⟩

end StackSorting.GraphWidth.UCurve.SubdivisionTree
