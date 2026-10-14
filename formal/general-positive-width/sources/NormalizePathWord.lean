import PathWordConstruction
import GluingIso

/-!
Optional finite-label normalization for the actual path word. Each arbitrary
finite carrier is transported bijectively to `Fin (Nat.card carrier)`.  A
pointwise graph isomorphism is lifted through the same actual quotient gluing.
This file is separate so it cannot obstruct checks of the core reconstruction.
-/

universe u v w
namespace StackSorting.BiInterface.PathWord

variable {k : ℕ} {U : Type u} {V : Type v} {W : Type w}

/-- Change only vertex names; preserve adjacency and both partial interfaces. -/
noncomputable def renameGraph (G : Graph k U) (e : U ≃ V) : Graph k V where
  Adj := fun v w => G.Adj (e.symm v) (e.symm w)
  symm := G.symm
  loopless := fun v => G.loopless (e.symm v)
  left := fun i => (G.left i).map e
  right := fun i => (G.right i).map e
  left_inj := by
    intro i j v hi hj
    obtain ⟨x,hxi,hxv⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y,hyj,hyv⟩ := Option.map_eq_some_iff.mp hj
    have he := e.injective (hxv.trans hyv.symm)
    subst y
    exact G.left_inj i j x hxi hyj
  right_inj := by
    intro i j v hi hj
    obtain ⟨x,hxi,hxv⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y,hyj,hyv⟩ := Option.map_eq_some_iff.mp hj
    have he := e.injective (hxv.trans hyv.symm)
    subst y
    exact G.right_inj i j x hxi hyj
  cross := by
    intro i j v hi hj
    obtain ⟨x,hxi,hxv⟩ := Option.map_eq_some_iff.mp hi
    obtain ⟨y,hyj,hyv⟩ := Option.map_eq_some_iff.mp hj
    have he := e.injective (hxv.trans hyv.symm)
    subst y
    exact G.cross i j x hxi hyj

noncomputable def renameIso (G : Graph k U) (e : U ≃ V) :
    Iso G (renameGraph G e) where
  vertex := e
  adj := by intro x y; simp [renameGraph]
  left := fun _ => rfl
  right := fun _ => rfl

namespace Packed

noncomputable def numbering (P : Packed.{u} k) : P.Vertex ≃ Fin (Nat.card P.Vertex) := by
  letI := Fintype.ofFinite P.Vertex
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

/-- The finite normalized graph has literally a `Fin size` carrier. -/
noncomputable def normalize (P : Packed.{u} k) : Packed.{0} k where
  Vertex := Fin (Nat.card P.Vertex)
  finite := inferInstance
  graph := renameGraph P.graph P.numbering

noncomputable def normalizeIso (P : Packed.{u} k) : Iso P.graph P.normalize.graph :=
  renameIso P.graph P.numbering

@[simp] theorem normalize_card (P : Packed.{u} k) :
    Nat.card P.normalize.Vertex = Nat.card P.Vertex := by
  simp [normalize, Nat.card_eq_fintype_card]

/-- The map of normalized letters preserves their entire product up to an
actual bi-interface graph isomorphism. No identity law for gluing is used. -/
noncomputable def normalizeEvalIso (ps : List (Packed.{u} k)) (h : ps ≠ []) :
    Iso (eval ps).graph (eval (ps.map normalize)).graph := by
  induction ps with
  | nil => exact (h rfl).elim
  | cons P ps ih =>
    cases ps with
    | nil => exact P.normalizeIso
    | cons Q qs =>
      exact Iso.glue P.normalizeIso (ih (by simp))

end Packed

variable [DecidableEq V]

/-- Reconstruction survives a genuine interface-preserving isomorphism. -/
noncomputable def Reconstruction.transport (G : Original V)
    {P : Packed.{u} k} {Q : Packed.{w} k}
    (R : Reconstruction G P) (e : Iso P.graph Q.graph) : Reconstruction G Q where
  vertex := e.vertex.symm.trans R.vertex
  adj := by
    intro x y
    have h := (e.adj (e.vertex.symm x) (e.vertex.symm y)).trans
      (R.adj (e.vertex.symm x) (e.vertex.symm y))
    simpa using h
  left := by
    intro i
    rw [← e.left i, R.left i]
    rfl
  right := by
    intro i
    rw [← e.right i, R.right i]
    rfl

/-- Universe-zero finite normalization is produced after reconstruction;
original vertex names may live in any universe. The normalized word has the
same length and each letter still has at most `k` actual vertices. -/
theorem exists_normalized_small_word_reconstruction (G : Original V)
    (D : Decomposition G k) :
    ∃ ws : List (Packed.{0} k), ws ≠ [] ∧
      (∀ P ∈ ws, Nat.card P.Vertex ≤ k) ∧
      ws.length = D.bags.length + 1 ∧ Nonempty (Reconstruction G (Packed.eval ws)) := by
  classical
  obtain ⟨ws,hne,hsmall,hlen,⟨R⟩⟩ := exists_small_word_reconstruction G D
  refine ⟨ws.map Packed.normalize,?_,?_,?_,?_⟩
  · simpa using hne
  · intro P hP
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hP
    simpa using hsmall Q hQ
  · simpa using hlen
  · exact ⟨Reconstruction.transport G R (Packed.normalizeEvalIso ws hne)⟩

#print axioms exists_normalized_small_word_reconstruction
end StackSorting.BiInterface.PathWord
