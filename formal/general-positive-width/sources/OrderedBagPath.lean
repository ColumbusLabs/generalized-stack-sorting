import HypergraphBagPath
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Sigma.Order

namespace FiniteFlow.Hypergraph
variable {V E I : Type*} [DecidableEq V] [LinearOrder I]

/-- An intermediate presentation of a finite bag path on any finite linear
index order. The conversion below constructs the original natural-index object. -/
structure OrderedBagPath (I : Type*) [LinearOrder I] (region : Finset V) (bound : Nat) where
  bag : I → Finset V
  inside : ∀ i, bag i ⊆ region
  bounded : ∀ i, (bag i).card ≤ bound
  vertex : ∀ x ∈ region, ∃ i, x ∈ bag i
  interval : ∀ i j k, i ≤ j → j ≤ k → ∀ x,
    x ∈ bag i → x ∈ bag k → x ∈ bag j

namespace OrderedBagPath
variable {region : Finset V} {bound : Nat}

def Covers (D : OrderedBagPath I region bound) (inc : V → E → Prop) : Prop :=
  ∀ e, ∃ i, ∀ x ∈ region, inc x e → x ∈ D.bag i

/-- Enumerate the finite ordered index set in increasing order. Nothing about
existence of a decomposition is assumed in this change of presentation. -/
noncomputable def toBagPath [Fintype I] [Nonempty I]
    (D : OrderedBagPath I region bound) : BagPath region bound := by
  classical
  let e := monoEquivOfFin I rfl
  have hn : 0 < Fintype.card I := Fintype.card_pos
  exact {
    last := Fintype.card I - 1
    bag := fun i => if h : i < Fintype.card I then D.bag (e ⟨i,h⟩) else ∅
    inside := by
      intro i hi
      have h : i < Fintype.card I := by omega
      simp only [dite_eq_left h]
      exact D.inside _
    bounded := by
      intro i hi
      have h : i < Fintype.card I := by omega
      simp only [dite_eq_left h]
      exact D.bounded _
    vertex := by
      intro x hx
      obtain ⟨a,ha⟩ := D.vertex x hx
      let i := e.symm a
      refine ⟨i.val,by have := i.isLt; omega,?_⟩
      rw [dite_eq_left i.isLt]
      change x ∈ D.bag (e i)
      simpa only [i,OrderIso.apply_symm_apply] using ha
    interval := by
      intro i j k hij hjk hk x hxi hxk
      have hi : i < Fintype.card I := by omega
      have hj : j < Fintype.card I := by omega
      have hk' : k < Fintype.card I := by omega
      simp only [dite_eq_left hi] at hxi
      simp only [dite_eq_left hk'] at hxk
      simp only [dite_eq_left hj]
      exact D.interval _ _ _ (e.monotone hij) (e.monotone hjk) x hxi hxk
  }

omit [DecidableEq V] in
theorem toBagPath_covers [Fintype I] [Nonempty I]
    (D : OrderedBagPath I region bound) {inc : V → E → Prop}
    (hD : D.Covers inc) : D.toBagPath.Covers inc := by
  classical
  intro f
  obtain ⟨a,ha⟩ := hD f
  let e := monoEquivOfFin I rfl
  let i := e.symm a
  refine ⟨i.val,by change i.val ≤ Fintype.card I - 1; have := i.isLt; omega,?_⟩
  intro x hx hxf
  change x ∈ if h : i.val < Fintype.card I then D.bag (e ⟨i.val,h⟩) else ∅
  rw [dite_eq_left i.isLt]
  change x ∈ D.bag (e i)
  simpa only [i,OrderIso.apply_symm_apply] using ha x hx hxf

end OrderedBagPath
end FiniteFlow.Hypergraph
