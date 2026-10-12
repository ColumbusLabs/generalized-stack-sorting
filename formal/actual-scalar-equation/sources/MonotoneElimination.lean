import Std

/-! Generic finite monotone bottom elimination. This module contains no machine
semantics and is not itself a theorem about decorated completion languages. -/
namespace StackSorting.MonotoneElimination
open List

abbrev Eligibility := List Nat → Nat → Prop

def Monotone (E : Eligibility) : Prop :=
  ∀ {U V : List Nat} {v : Nat}, V.Nodup → V ⊆ U → E U v → E V v

def SelfIndependent (E : Eligibility) : Prop :=
  ∀ {U : List Nat} {v : Nat}, U.Nodup → v ∈ U → (E U v ↔ E (U.erase v) v)

inductive Peelable (E : Eligibility) : List Nat → Prop where
  | nil : Peelable E []
  | step {U : List Nat} (v : Nat) (mem : v ∈ U) (eligible : E U v)
      (rest : Peelable E (U.erase v)) : Peelable E U

def EverySubset (E : Eligibility) (U : List Nat) : Prop :=
  ∀ V : List Nat, V.Nodup → V ⊆ U → V ≠ [] → ∃ v ∈ V, E V v

theorem Peelable.everySubset {E : Eligibility} (hm : Monotone E)
    {U : List Nat} (h : Peelable E U) : EverySubset E U := by
  induction h with
  | nil =>
    intro V _ hsub hne
    have he : V = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun v hv => by simpa using hsub hv)
    exact (hne he).elim
  | @step U v hv he rest ih =>
    intro V hn hsub hne
    by_cases hmem : v ∈ V
    · exact ⟨v, hmem, hm hn hsub he⟩
    · apply ih V hn (fun w hw => ?_) hne
      apply (List.mem_erase_of_ne (by intro heq; subst w; exact hmem hw)).mpr
      exact hsub hw

theorem EverySubset.subset {E : Eligibility} {U V : List Nat}
    (h : EverySubset E U) (hsub : V ⊆ U) : EverySubset E V := by
  intro W hn hw hne
  exact h W hn (fun x hx => hsub (hw hx)) hne

theorem EverySubset.peelable {E : Eligibility} {U : List Nat}
    (hn : U.Nodup) (h : EverySubset E U) : Peelable E U := by
  have aux : ∀ m : Nat, ∀ W : List Nat, W.length = m → W.Nodup →
      EverySubset E W → Peelable E W := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro W hm hWn hW
      by_cases hnil : W = []
      · subst W
        exact .nil
      · obtain ⟨v, hv, he⟩ := hW W hWn (fun _ hm => hm) hnil
        have hlt : (W.erase v).length < m := by
          have hpos : 0 < W.length := List.length_pos_iff.mpr hnil
          rw [List.length_erase_of_mem hv]
          omega
        exact .step v hv he (ih _ hlt _ rfl (hWn.erase v)
          (hW.subset List.erase_subset))
  exact aux U.length U rfl hn h

theorem peelable_iff_everySubset {E : Eligibility} (hm : Monotone E)
    {U : List Nat} (hn : U.Nodup) : Peelable E U ↔ EverySubset E U :=
  ⟨fun h => Peelable.everySubset (E := E) hm h, fun h => h.peelable hn⟩

def FeasibleAbove (E : Eligibility) (above : List Nat) : List Nat → Prop
  | [] => True
  | v :: below => E above v ∧ FeasibleAbove E (above ++ [v]) below

def FeasibleOrder (E : Eligibility) (order : List Nat) : Prop :=
  FeasibleAbove E [] order

theorem feasibleAbove_append (E : Eligibility) (above xs ys : List Nat) :
    FeasibleAbove E above (xs ++ ys) ↔
      FeasibleAbove E above xs ∧ FeasibleAbove E (above ++ xs) ys := by
  induction xs generalizing above with
  | nil => simp [FeasibleAbove]
  | cons v xs ih => simp [FeasibleAbove, ih, List.append_assoc, and_assoc]

theorem feasibleOrder_snoc (E : Eligibility) (order : List Nat) (v : Nat) :
    FeasibleOrder E (order ++ [v]) ↔ FeasibleOrder E order ∧ E order v := by
  simp [FeasibleOrder, feasibleAbove_append, FeasibleAbove]

theorem feasibleOrder_iff_prefixes (E : Eligibility) (order : List Nat) :
    FeasibleOrder E order ↔
      ∀ above v below, order = above ++ v :: below → E above v := by
  have aux : ∀ xs above, FeasibleAbove E above xs ↔
      ∀ pre v post, xs = pre ++ v :: post → E (above ++ pre) v := by
    intro xs
    induction xs with
    | nil => intro above; simp [FeasibleAbove]
    | cons x xs ih =>
      intro above
      rw [FeasibleAbove, ih]
      constructor
      · rintro ⟨hx, ht⟩ pre v post heq
        cases pre with
        | nil => simp at heq; rcases heq with ⟨rfl, rfl⟩; simpa using hx
        | cons y pre =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rcases heq with ⟨rfl, heq⟩
          simpa [List.append_assoc] using ht pre v post heq
      · intro h
        refine ⟨?_, ?_⟩
        · simpa using h [] x xs rfl
        · intro pre v post heq
          simpa [List.append_assoc] using h (x :: pre) v post (by simp [heq])
  simpa [FeasibleOrder] using aux order []

theorem eligibility_perm {E : Eligibility} (hm : Monotone E)
    {U V : List Nat} {v : Nat} (hn : U.Nodup) (hp : U.Perm V) : E U v ↔ E V v :=
  ⟨fun h => hm (hp.nodup_iff.mp hn) (fun _ hv => hp.mem_iff.mpr hv) h,
   fun h => hm hn (fun _ hu => hp.mem_iff.mp hu) h⟩

theorem Peelable.feasibleOrder {E : Eligibility} (hm : Monotone E)
    {U : List Nat} (h : Peelable E U) (hn : U.Nodup) :
    ∃ order, order.Perm U ∧ FeasibleOrder E order := by
  revert hn
  induction h with
  | nil => intro _; exact ⟨[], .refl [], trivial⟩
  | @step U v hv he hrest ih =>
    intro hn
    obtain ⟨order, hp, hf⟩ := ih (hn.erase v)
    have her : E (U.erase v) v := hm (hn.erase v) List.erase_subset he
    have ho : E order v := (eligibility_perm (E := E) (v := v) hm (hn.erase v) hp.symm).mp her
    refine ⟨order ++ [v], ?_, (feasibleOrder_snoc E order v).mpr ⟨hf, ho⟩⟩
    have hrotate : (order ++ [v]).Perm (v :: order) := by simp
    exact hrotate.trans ((List.Perm.cons v hp).trans (List.perm_cons_erase hv).symm)

/-- Feasible orders imply the every-subset criterion directly, by looking at
its bottom remaining token. Self-independence restores that token in its own
eligibility test. -/
theorem feasibleOrder_peelable {E : Eligibility} (_hm : Monotone E)
    (hself : SelfIndependent E) {order : List Nat}
    (hn : order.Nodup) (hf : FeasibleOrder E order) : Peelable E order := by
  have aux : ∀ rev : List Nat, rev.reverse.Nodup →
      FeasibleOrder E rev.reverse → Peelable E rev.reverse := by
    intro rev
    induction rev with
    | nil => intro _ _; exact .nil
    | cons v rev ih =>
      intro hn hf
      simp only [List.reverse_cons] at hn hf ⊢
      have hn' := List.nodup_append.mp hn
      have hv : v ∉ rev.reverse := by
        intro hv
        exact hn'.2.2 v hv v (by simp) rfl
      obtain ⟨hf', he⟩ := (feasibleOrder_snoc E rev.reverse v).mp hf
      have he' : E (rev.reverse ++ [v]) v := by
        apply (hself hn (by simp)).mpr
        simpa [List.erase_append_right _ hv] using he
      apply Peelable.step v (by simp) he'
      simpa [List.erase_append_right _ hv] using ih hn'.1 hf'
  simpa using aux order.reverse (by simpa using hn) (by simpa using hf)

theorem feasibleOrder_iff_everySubset {E : Eligibility} (hm : Monotone E)
    (hself : SelfIndependent E) {U : List Nat} (hn : U.Nodup) :
    (∃ order, order.Perm U ∧ FeasibleOrder E order) ↔ EverySubset E U := by
  constructor
  · rintro ⟨order, hp, hf⟩
    have he := (feasibleOrder_peelable (E := E) hm hself (hp.nodup_iff.mpr hn) hf) |> Peelable.everySubset (E := E) hm
    exact he.subset (fun _ hu => hp.mem_iff.mpr hu)
  · intro h
    exact Peelable.feasibleOrder (E := E) hm (h.peelable hn) hn

/-- Abstract single-loss obstruction lemma. Each residual set has at most one
base-eligible token whose eligibility can be removed by any selected face.
Thus feasibility of every singleton restriction implies their joint feasibility.
This is a proved finite combinatorial statement; no completion intersection
appears in its hypotheses. -/
theorem everySubset_simultaneous
    (base : Eligibility) (restriction : Nat → Eligibility)
    (U selected : List Nat) (hne : selected ≠ [])
    (hloss : ∀ V, V.Nodup → V ⊆ U →
      ∀ a ∈ V, base V a → ∀ i ∈ selected, ¬ restriction i V a →
      ∀ b ∈ V, base V b → ∀ j ∈ selected, ¬ restriction j V b → a = b)
    (hsingle : ∀ i ∈ selected,
      EverySubset (fun V v => base V v ∧ restriction i V v) U) :
    EverySubset (fun V v => base V v ∧ ∀ i ∈ selected, restriction i V v) U := by
  classical
  intro V hn hsub hvne
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil selected hne
  obtain ⟨a, ha, hbase, hri⟩ := hsingle i hi V hn hsub hvne
  by_cases hall : ∀ j ∈ selected, restriction j V a
  · exact ⟨a, ha, hbase, hall⟩
  · obtain ⟨j, hj, hja⟩ : ∃ j ∈ selected, ¬ restriction j V a := by
      apply Classical.byContradiction
      intro hnone
      apply hall
      intro j hj
      apply Classical.byContradiction
      intro hn
      exact hnone ⟨j, hj, hn⟩
    obtain ⟨b, hb, hbbase, hbj⟩ := hsingle j hj V hn hsub hvne
    refine ⟨b, hb, hbbase, ?_⟩
    intro k hk
    apply Classical.byContradiction
    intro hkb
    have heq := hloss V hn hsub a ha hbase j hj hja b hb hbbase k hk hkb
    subst b
    exact hja hbj

#print axioms feasibleOrder_iff_everySubset
#print axioms everySubset_simultaneous
end StackSorting.MonotoneElimination
