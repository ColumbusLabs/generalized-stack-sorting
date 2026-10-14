import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

namespace StackSorting.PrefixGrowth
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Actual finite prefixes are parent-closed node sets. -/
def IsPrefix (parent : N → N) (Z : Finset N) : Prop := ∀ x ∈ Z, parent x ∈ Z

def Frontier (parent : N → N) (Z : Finset N) (x : N) : Prop := x ∉ Z ∧ parent x ∈ Z

omit [Fintype N] [DecidableEq N] in
theorem root_prefix (parent : N → N) (r : N) (hr : parent r = r) : IsPrefix parent {r} := by
  intro x hx
  have he : x = r := Finset.mem_singleton.mp hx
  subst x
  simp [hr]

omit [Fintype N] in
theorem insert_frontier_prefix (parent : N → N) (Z : Finset N) (x : N)
    (hp : IsPrefix parent Z) (hx : Frontier parent Z x) : IsPrefix parent (insert x Z) := by
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact Finset.mem_insert_of_mem hx.2
  · exact Finset.mem_insert_of_mem (hp y hy)

/-- An actual strictly growing finite-node construction terminates with its
desired condition. This is the finite measure used by hypertorso saturation;
no bound on graph pathwidth or global decomposition is a premise. -/
theorem finite_invariant_saturation (Inv Done : Finset N → Prop)
    (step : ∀ Z, Inv Z → ¬ Done Z → ∃ x, x ∉ Z ∧ Inv (insert x Z))
    (Z : Finset N) (hZ : Inv Z) : ∃ W, Z ⊆ W ∧ Inv W ∧ Done W := by
  classical
  suffices aux : ∀ m, ∀ Z : Finset N, Fintype.card N - Z.card = m → Inv Z →
      ∃ W, Z ⊆ W ∧ Inv W ∧ Done W by
    exact aux _ Z rfl hZ
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro Z hm hZ
    by_cases hd : Done Z
    · exact ⟨Z,Finset.Subset.refl _,hZ,hd⟩
    obtain ⟨x,hx,hnext⟩ := step Z hZ hd
    have hins : (insert x Z).card = Z.card+1 := Finset.card_insert_of_notMem hx
    have hcard : (insert x Z).card ≤ Fintype.card N := by
      simpa using Finset.card_le_card (Finset.subset_univ (insert x Z))
    have hlt : Fintype.card N - (insert x Z).card < m := by omega
    obtain ⟨W,hsub,hW,hDone⟩ := ih _ hlt (insert x Z) rfl hnext
    exact ⟨W,(Finset.subset_insert x Z).trans hsub,hW,hDone⟩

/-- Saturation preserves the actual root-containing prefix while only adding
frontier nodes. Instantiating Inv with the thinness invariant supplies the
termination step of Lemma 5.2. -/
theorem exists_saturated_prefix (parent : N → N) (r : N) (hr : parent r = r)
    (Thin Done : Finset N → Prop) (base : Thin {r})
    (step : ∀ Z, IsPrefix parent Z → r ∈ Z → Thin Z → ¬ Done Z →
      ∃ x, Frontier parent Z x ∧ Thin (insert x Z)) :
    ∃ Z, IsPrefix parent Z ∧ r ∈ Z ∧ Thin Z ∧ Done Z := by
  let Inv := fun Z => IsPrefix parent Z ∧ r ∈ Z ∧ Thin Z
  have hbase : Inv {r} := ⟨root_prefix parent r hr,by simp,base⟩
  have hstep : ∀ Z, Inv Z → ¬ Done Z → ∃ x, x ∉ Z ∧ Inv (insert x Z) := by
    intro Z hZ hd
    obtain ⟨x,hx,hthin⟩ := step Z hZ.1 hZ.2.1 hZ.2.2 hd
    exact ⟨x,hx.1,insert_frontier_prefix parent Z x hZ.1 hx,
      Finset.mem_insert_of_mem hZ.2.1,hthin⟩
  obtain ⟨Z,_,hZ,hd⟩ := finite_invariant_saturation Inv Done hstep {r} hbase
  exact ⟨Z,hZ.1,hZ.2.1,hZ.2.2,hd⟩

end StackSorting.PrefixGrowth

namespace StackSorting.PrefixGrowth
variable {N : Type*} [DecidableEq N]
theorem frontier_insert_iff (parent : N → N) (Z : Finset N) (z c : N)
    (hp : IsPrefix parent Z) (hz : z ∉ Z) :
    Frontier parent (insert z Z) c ↔
      (Frontier parent Z c ∧ c ≠ z) ∨ (parent c = z ∧ c ≠ z) := by
  constructor
  · rintro ⟨hc,hpar⟩
    have hcz : c ≠ z := fun he => hc (Finset.mem_insert.mpr (Or.inl he))
    have hcZ : c ∉ Z := fun h => hc (Finset.mem_insert_of_mem h)
    rcases Finset.mem_insert.mp hpar with he | h
    · exact Or.inr ⟨he,hcz⟩
    · exact Or.inl ⟨⟨hcZ,h⟩,hcz⟩
  · rintro (⟨hc,hcz⟩ | ⟨hpar,hcz⟩)
    · exact ⟨fun h => (Finset.mem_insert.mp h).elim hcz hc.1,Finset.mem_insert_of_mem hc.2⟩
    · refine ⟨?_,Finset.mem_insert.mpr (Or.inl hpar)⟩
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hcz h
      · exact hz (hpar ▸ hp c h)
end StackSorting.PrefixGrowth
