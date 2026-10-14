import ActualDualCotree
import RootPathBags

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

def incidenceGraph {α V F} (I : IncidenceMap α V F)
    (hl : ∀ d, I.tail d≠I.tail (I.reverse d)) : Graph V where
  Adj := fun x y => ∃ d, I.tail d=x ∧ I.tail (I.reverse d)=y
  symm := by
    rintro x y ⟨d,rfl,rfl⟩
    exact ⟨I.reverse d,rfl,by rw [I.reverse_reverse]⟩
  loopless := by
    rintro x ⟨d,hd,he⟩
    exact hl d (hd.trans he.symm)

theorem walk_map_predicate {α β : Type} {adj : α → α → Prop} {adj' : β → β → Prop}
    {P : α → Prop} {Q : β → Prop} (f : α → β)
    (hm : ∀ {a b}, adj a b → adj' (f a) (f b)) (hp : ∀ a, P a → Q (f a))
    {a b} (h : Walk adj P a b) : Walk adj' Q (f a) (f b) := by
  induction h with
  | refl h => exact .refl (hp _ h)
  | step h he _ ih => exact .step (hp _ h) (hm he) ih

/-- The genuine three-root-path tree decomposition. Local rotation, vertex
orbits, actual primal parent edges, and a constructed cotree prove all three
decomposition axioms, including running intersection. -/
noncomputable def threeRootPathDecomposition {α V F} (I : IncidenceMap α V F)
    (hl : ∀ d, I.tail d≠I.tail (I.reverse d)) (C : TriangularIncidences I)
    (T : RootedTree V) (D : ActualCotree I T)
    (hc : CutContinues I) (rot : α → α) (ht : ∀ d, I.tail (rot d)=I.tail d)
    (hf : ∀ d, I.face (rot d)=I.face (I.reverse d))
    (hv : ∀ d e, I.tail d=I.tail e → Walk (OrbitStep rot) (fun _ => True) d e)
    (hsurj : ∀ x, ∃ d, I.tail d=x)
    (hedge : ∀ x, x.val≠0 → ∃ d, I.tail d=x ∧ I.tail (I.reverse d)=T.parent x) :
    Decomposition (incidenceGraph I hl) D.tree where
  bag := fun i => threeRootBag I C T (D.code.decode i)
  nodup := fun i => threeRootBag_nodup I C T (D.code.decode i)
  vertex := by
    intro v
    obtain ⟨d,hd⟩ := hsurj v
    refine ⟨D.code.encode (I.face d),?_⟩
    apply (mem_threeRootBag I C T _ v).mpr
    rw [D.code.decode_encode]
    exact ⟨d,rfl,by rw [hd]; exact Ancestor.refl v⟩
  edge := by
    rintro u v ⟨d,hd,he⟩
    refine ⟨D.code.encode (I.face d),?_,?_⟩
    · apply (mem_threeRootBag I C T _ u).mpr
      rw [D.code.decode_encode]
      exact ⟨d,rfl,by rw [hd]; exact Ancestor.refl u⟩
    · apply (mem_threeRootBag I C T _ v).mpr
      rw [D.code.decode_encode]
      refine ⟨rot (I.reverse d),?_,?_⟩
      · rw [hf,I.reverse_reverse]
      · rw [ht,he]
        exact Ancestor.refl v
  running := by
    intro v i j hi hj
    have hi' := (mem_threeRootBag I C T _ v).mp hi
    have hj' := (mem_threeRootBag I C T _ v).mp hj
    have hwalk := subtree_faces_cotree_connected I T hc rot ht hf hv hsurj hedge v hi' hj'
    have hmap := walk_map_predicate (Q := fun k => v ∈ threeRootBag I C T (D.code.decode k)) D.code.encode (fun he => D.edge he)
      (fun a ha => by
        apply (mem_threeRootBag I C T _ v).mpr
        simpa only [D.code.decode_encode] using ha) hwalk
    simpa only [D.code.encode_decode] using hmap

theorem threeRootPathDecomposition_bound {α V F} (I : IncidenceMap α V F)
    (hl : ∀ d, I.tail d≠I.tail (I.reverse d)) (C : TriangularIncidences I)
    (T : RootedTree V) (D : ActualCotree I T)
    (hc : CutContinues I) (rot : α → α) (ht : ∀ d, I.tail (rot d)=I.tail d)
    (hf : ∀ d, I.face (rot d)=I.face (I.reverse d))
    (hv : ∀ d e, I.tail d=I.tail e → Walk (OrbitStep rot) (fun _ => True) d e)
    (hsurj : ∀ x, ∃ d, I.tail d=x)
    (hedge : ∀ x, x.val≠0 → ∃ d, I.tail d=x ∧ I.tail (I.reverse d)=T.parent x)
    (k : Nat) (hdepth : ∀ v, (rootPath T v).length≤k) :
    (threeRootPathDecomposition I hl C T D hc rot ht hf hv hsurj hedge).BagBound (3*k) := by
  intro i
  exact threeRootBag_bound I C T k hdepth (D.code.decode i)

end StackSorting.GraphWidth.UCurve.PlaneGrid
