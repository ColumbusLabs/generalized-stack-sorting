import OrderedColumns
import PathDecompositionFactorization

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord Simon Simon.FactorizationTree
variable {k : Nat}

/-- Replacing each nonempty consecutive block by its actual evaluated graph
preserves the whole quotient graph and every outer interface exactly. -/
noncomputable def evalFlattenIso (ws : List (List (Packed.{0} k)))
    (hne : ∀ w ∈ ws, w ≠ []) :
    Iso (Packed.eval ws.flatten).graph (Packed.eval (ws.map Packed.eval)).graph := by
  induction ws with
  | nil => exact identIso _
  | cons w ws ih =>
    have hw : w ≠ [] := hne w (by simp)
    have ht : ∀ v ∈ ws, v ≠ [] := fun v hv => hne v (by simp [hv])
    cases ws with
    | nil =>
      change Iso (Packed.eval (w ++ [])).graph (Packed.eval w).graph
      rw [List.append_nil]
      exact identIso _
    | cons v vs =>
      have hf : (v :: vs).flatten ≠ [] := by
        intro h
        exact ht v (by simp) ((List.flatten_eq_nil_iff.mp h) v (by simp))
      exact transIso (evalAppendIso w (v :: vs).flatten hw hf)
        ((identIso (Packed.eval w).graph).glue (ih ht))

/-- Semigroup-valid trees never encode empty words. -/
theorem semigroupValid_leaves_ne_nil {A S : Type*} [Semigroup S] {f : A → S}
    {t : FactorizationTree A} (h : SemigroupValid f t) : t.leaves ≠ [] := by
  induction h with
  | leaf a => simp [leaves]
  | node ts _hc ha _hb ih =>
    intro he
    have hts : ts ≠ [] := by intro hh; simp [hh] at ha
    obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil ts hts
    have hflat : (ts.map leaves).flatten = [] := by simpa [leaves,List.flatMap_def] using he
    exact ih r hr ((List.flatten_eq_nil_iff.mp hflat) r.leaves (List.mem_map.mpr ⟨r,hr,rfl⟩))

/-- The value annotation on a child word is its actual evaluated abstraction. -/
theorem abstraction_of_wordValue (ws : List (Packed.{0} k)) (hne : ws ≠ [])
    (e : Abstract k) (hv : SemigroupWordValue (fun P : Packed.{0} k => abstractGraph P.graph) ws e) :
    abstractGraph (Packed.eval ws).graph = e := by
  apply WithOne.coe_injective
  exact (abstraction_eval_product ws hne).symm.trans
    ((semigroupWordValue_iff_coe_product _ ws hne e).mp hv)
end StackSorting.BiInterface.RepeatedColumn
