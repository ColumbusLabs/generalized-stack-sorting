import FiniteAbstractionSemigroup
import NormalizePathWord

namespace StackSorting.BiInterface.PathWord
open Simon Simon.FactorizationTree
variable {k : ℕ}

/-- The semantic word product is exactly the abstraction of the actual quotient
product. The fresh adjoined identity is used only for the list notation. -/
theorem abstraction_eval_product (ws : List (Packed.{0} k)) (hne : ws ≠ []) :
    (ws.map (fun P => (abstractGraph P.graph : WithOne (Abstract k)))).prod =
      (abstractGraph (Packed.eval ws).graph : WithOne (Abstract k)) := by
  induction ws with
  | nil => exact (hne rfl).elim
  | cons P ps ih =>
    cases ps with
    | nil => simp
    | cons Q qs =>
      rw [List.map_cons,List.prod_cons,ih (by simp),Packed.eval_cons P (Q :: qs) (by simp)]
      change (abstractGraph P.graph : WithOne (Abstract k)) *
          (abstractGraph (Packed.eval (Q :: qs)).graph : WithOne (Abstract k)) =
        (abstractGraph (glue P.graph (Packed.eval (Q :: qs)).graph) : WithOne (Abstract k))
      rw [abstractGraph_glue,WithOne.coe_mul]

theorem abstraction_eval_wordValue (ws : List (Packed.{0} k)) (hne : ws ≠ []) :
    SemigroupWordValue (fun P : Packed.{0} k => abstractGraph P.graph) ws
      (abstractGraph (Packed.eval ws).graph) :=
  (semigroupWordValue_iff_coe_product _ ws hne _).mpr (abstraction_eval_product ws hne)

/-- The supplied path decomposition yields both a real small-piece word
reconstructing the original graph and a genuine bounded-height factorization
of that literal word. No guidance or reconstruction witness is assumed. -/
theorem exists_path_decomposition_factorization {V : Type*} [DecidableEq V]
    (G : Original V) (D : Decomposition G k) :
    ∃ ws : List (Packed.{0} k), ws ≠ [] ∧
      (∀ P ∈ ws, Nat.card P.Vertex ≤ k) ∧
      ws.length = D.bags.length + 1 ∧
      Nonempty (Reconstruction G (Packed.eval ws)) ∧
      ∃ t : FactorizationTree (Packed.{0} k), t.leaves = ws ∧
        SemigroupValid (fun P : Packed.{0} k => abstractGraph P.graph) t ∧
        t.height ≤ monoidForestBound (Fintype.card (Abstract k) + 1) := by
  obtain ⟨ws,hne,hsmall,hlen,hrecon⟩ := exists_normalized_small_word_reconstruction G D
  obtain ⟨t,ht,hv,hh⟩ := exists_finite_semigroup_factorization_tree
    (fun P : Packed.{0} k => abstractGraph P.graph) ws hne
  exact ⟨ws,hne,hsmall,hlen,hrecon,t,ht,hv,hh⟩

#print axioms exists_path_decomposition_factorization
end StackSorting.BiInterface.PathWord
