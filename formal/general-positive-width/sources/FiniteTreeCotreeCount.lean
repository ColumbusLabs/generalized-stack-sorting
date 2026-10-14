import SubtreeFaceConnectivity
import RectangleCotreeConnectivity

namespace StackSorting.GraphWidth.UCurve.PlaneGrid
open FinitePort

def finIdentityCode (n : Nat) : FiniteCode (Fin n) n where
  encode := id
  decode := id
  decode_encode := fun _ => rfl
  encode_decode := fun _ => rfl

/-- An injection between two explicitly encoded finite sets of the same size
is onto. The proof uses the checked finite-permutation period theorem. -/
theorem finiteCode_surjective_of_injective {α β n} (A : FiniteCode α n)
    (B : FiniteCode β n) (f : α → β) (hf : Function.Injective f) :
    ∀ b, ∃ a, f a=b := by
  let g : Fin n → Fin n := fun i => B.encode (f (A.decode i))
  have hg : Function.Injective g := by
    intro i j h
    have he := hf (B.injective h)
    have he' := congrArg A.encode he
    simpa only [A.encode_decode] using he'
  intro b
  obtain ⟨p,hp,_,hret⟩ := (finIdentityCode n).positive_rotation_period g hg (B.encode b)
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
  refine ⟨A.decode (rotationIter g q (B.encode b)),B.injective ?_⟩
  exact hret

def treeChild {n} (i : Fin (n-1)) : Fin n := ⟨i.val+1,by have := i.isLt; omega⟩

theorem treeChild_ne_zero {n} (i : Fin (n-1)) : (treeChild i).val≠0 := by
  change i.val+1≠0
  omega

theorem treeChild_injective {n} : Function.Injective (@treeChild n) := by
  intro i j he
  apply Fin.ext
  have h := congrArg Fin.val he
  change i.val+1=j.val+1 at h
  omega

theorem reverse_walk_two {α V F} (I : IncidenceMap α V F) {d e}
    (h : Walk (OrbitStep I.reverse) (fun _ => True) d e) : d=e ∨ d=I.reverse e := by
  induction h with
  | refl => exact Or.inl rfl
  | @step a b c _ hs _ ih =>
    have hab : a=I.reverse b := by
      obtain hs | hs := hs
      · exact (I.reverse_reverse a).symm.trans (congrArg I.reverse hs)
      · exact hs.symm
    obtain ih | ih := ih
    · exact Or.inr (hab.trans (congrArg I.reverse ih))
    · apply Or.inl
      rw [hab,ih,I.reverse_reverse]

theorem same_edge_two {α V F E} (I : IncidenceMap α V F)
    (C : OrbitCount I.reverse E) {d e} (he : C.label d=C.label e) :
    d=e ∨ d=I.reverse e := reverse_walk_two I ((C.exact_components d e).mpr he)

theorem edge_label_preserves_tree {α V F E} (I : IncidenceMap α V F)
    (T : RootedTree V) (C : OrbitCount I.reverse E) {d e} (he : C.label d=C.label e)
    (hd : TreeAdj T (I.tail d) (I.tail (I.reverse d))) :
    TreeAdj T (I.tail e) (I.tail (I.reverse e)) := by
  obtain h | h := same_edge_two I C he
  · simpa only [h] using hd
  · rw [h,I.reverse_reverse] at hd
    exact treeAdj_symm T hd

/-- Representatives of distinct downward parent edges have distinct edge
orbits. This applies both to primal and to relabeled dual parent trees. -/
theorem parent_representatives_injective {α V F E n} (I : IncidenceMap α V F)
    (C : OrbitCount I.reverse E) (T : RootedTree n) (vertex : α → Fin n)
    (ds : Fin (n-1) → α) (ht : ∀ i, vertex (ds i)=treeChild i)
    (hh : ∀ i, vertex (I.reverse (ds i))=T.parent (treeChild i)) :
    Function.Injective (fun i => C.label (ds i)) := by
  intro i j he
  obtain he | he := same_edge_two I C he
  · apply treeChild_injective
    exact (ht i).symm.trans ((congrArg vertex he).trans (ht j))
  · have h1 : treeChild i=T.parent (treeChild j) :=
      (ht i).symm.trans ((congrArg vertex he).trans (hh j))
    have h2 : T.parent (treeChild i)=treeChild j := by
      have he' := congrArg (fun d => vertex (I.reverse d)) he
      rw [I.reverse_reverse] at he'
      exact (hh i).symm.trans (he'.trans (ht j))
    have hi := T.parent_lt (treeChild i) (treeChild_ne_zero i)
    have hj := T.parent_lt (treeChild j) (treeChild_ne_zero j)
    rw [h2] at hi
    rw [← h1] at hj
    omega

/-- Euler plus the two genuinely realized spanning trees exhausts every edge.
No acyclicity or cotree-exhaustion certificate is assumed. -/
theorem tree_cotree_edge_exhaustion {α V F E} (I : IncidenceMap α V F)
    (C : OrbitCount I.reverse E) (T : RootedTree V) (U : RootedTree F)
    (R : FiniteCode (Fin F) F)
    (p : Fin (V-1) → α) (q : Fin (F-1) → α)
    (pt : ∀ i, I.tail (p i)=treeChild i)
    (ph : ∀ i, I.tail (I.reverse (p i))=T.parent (treeChild i))
    (qt : ∀ i, R.encode (I.face (q i))=treeChild i)
    (qh : ∀ i, R.encode (I.face (I.reverse (q i)))=U.parent (treeChild i))
    (qn : ∀ i, ¬TreeAdj T (I.tail (q i)) (I.tail (I.reverse (q i))))
    (heuler : (V-1)+(F-1)=E) :
    ∀ d, (∃ i, C.label d=C.label (p i)) ∨ ∃ j, C.label d=C.label (q j) := by
  let f : Sum (Fin (V-1)) (Fin (F-1)) → Fin E := fun s =>
    match s with | .inl i => C.label (p i) | .inr j => C.label (q j)
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (parent_representatives_injective I C T I.tail p pt ph hab)
      | inr j =>
        have hp : TreeAdj T (I.tail (p i)) (I.tail (I.reverse (p i))) := by
          rw [pt,ph]
          exact Or.inl ⟨treeChild_ne_zero i,rfl⟩
        exact False.elim (qn j (edge_label_preserves_tree I T C hab hp))
    | inr i =>
      cases b with
      | inl j =>
        have hp : TreeAdj T (I.tail (p j)) (I.tail (I.reverse (p j))) := by
          rw [pt,ph]
          exact Or.inl ⟨treeChild_ne_zero j,rfl⟩
        exact False.elim (qn i (edge_label_preserves_tree I T C hab.symm hp))
      | inr j => exact congrArg Sum.inr (parent_representatives_injective I C U (fun d => R.encode (I.face d)) q qt qh hab)
  have A : FiniteCode (Sum (Fin (V-1)) (Fin (F-1))) E := by
    rw [← heuler]
    exact sumCode (finIdentityCode (V-1)) (finIdentityCode (F-1))
  intro d
  obtain ⟨s,hs⟩ := finiteCode_surjective_of_injective A (finIdentityCode E) f hf (C.label d)
  cases s with
  | inl i => exact Or.inl ⟨i,hs.symm⟩
  | inr j => exact Or.inr ⟨j,hs.symm⟩


/-- The actual complementary dual has no edges beyond its constructed parent
spanning tree once Euler has exhausted the edge set. -/
theorem cotree_edge_is_parent_edge {α V F E} (I : IncidenceMap α V F)
    (C : OrbitCount I.reverse E) (T : RootedTree V) (U : RootedTree F)
    (R : FiniteCode (Fin F) F)
    (p : Fin (V-1) → α) (q : Fin (F-1) → α)
    (pt : ∀ i, I.tail (p i)=treeChild i)
    (ph : ∀ i, I.tail (I.reverse (p i))=T.parent (treeChild i))
    (qt : ∀ i, R.encode (I.face (q i))=treeChild i)
    (qh : ∀ i, R.encode (I.face (I.reverse (q i)))=U.parent (treeChild i))
    (qn : ∀ i, ¬TreeAdj T (I.tail (q i)) (I.tail (I.reverse (q i))))
    (heuler : (V-1)+(F-1)=E) {a b} (hab : CotreeAdj I T a b) :
    TreeAdj U (R.encode a) (R.encode b) := by
  obtain ⟨d,rfl,rfl,hd⟩ := hab
  obtain ⟨i,hi⟩ | ⟨j,hj⟩ := tree_cotree_edge_exhaustion I C T U R p q pt ph qt qh qn heuler d
  · have hp : TreeAdj T (I.tail (p i)) (I.tail (I.reverse (p i))) := by
      rw [pt,ph]
      exact Or.inl ⟨treeChild_ne_zero i,rfl⟩
    exact False.elim (hd (edge_label_preserves_tree I T C hi.symm hp))
  · obtain h | h := same_edge_two I C hj
    · rw [h,qt,qh]
      exact Or.inl ⟨treeChild_ne_zero j,rfl⟩
    · rw [h,I.reverse_reverse,qt,qh]
      exact Or.inr ⟨treeChild_ne_zero j,rfl⟩

end StackSorting.GraphWidth.UCurve.PlaneGrid
