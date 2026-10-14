import SparseModelReindexing

namespace StackSorting.SparseEndpointMSO

/-- Finite directed-path axioms stated without a chosen vertex enumeration.
Reachability supplies existence of an incoming edge at each nonroot vertex;
the two local uniqueness clauses exclude branching and merging. -/
structure RootedPathAxioms (D : Model) (root : Nat) : Prop where
  root_mem : root ∈ D.domain
  no_incoming : ∀ x ∈ D.domain, ¬ D.S x root
  reachable : ∀ x ∈ D.domain, ClosedReach D root x
  outgoing_unique : ∀ x ∈ D.domain, ∀ y ∈ D.domain, ∀ z ∈ D.domain,
    D.S x y → D.S x z → y = z
  incoming_unique : ∀ x ∈ D.domain, ∀ y ∈ D.domain, ∀ z ∈ D.domain,
    D.S y x → D.S z x → y = z

inductive CountedWalk (D : Model) (root : Nat) : Nat → Nat → Prop where
  | refl (hr : root ∈ D.domain) : CountedWalk D root 0 root
  | step {k x y : Nat} : CountedWalk D root k x → y ∈ D.domain → D.S x y →
      CountedWalk D root (k + 1) y

theorem CountedWalk.mem {D : Model} {root k x : Nat} (h : CountedWalk D root k x) :
    x ∈ D.domain := by
  cases h with
  | refl hr => exact hr
  | step _ hy _ => exact hy

theorem CountedWalk.of_walk {D : Model} {root x : Nat} (h : Walk D root x) :
    ∃ k, CountedWalk D root k x := by
  induction h with
  | refl hr => exact ⟨0, .refl hr⟩
  | step _ hy hs ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .step hk hy hs⟩

theorem CountedWalk.unique_length {D : Model} {root k l x : Nat}
    (hp : RootedPathAxioms D root) (a : CountedWalk D root k x)
    (b : CountedWalk D root l x) : k = l := by
  induction a generalizing l with
  | refl hr =>
    cases b with
    | refl => rfl
    | step hb _ hs => exact False.elim (hp.no_incoming _ hb.mem hs)
  | @step k p q ha hq hs ih =>
    cases b with
    | refl => exact False.elim (hp.no_incoming p ha.mem hs)
    | @step l p' q hb _ hs' =>
      have he := hp.incoming_unique q hq p ha.mem p' hb.mem hs hs'
      subst p'
      exact congrArg Nat.succ (ih hb)

theorem CountedWalk.unique_endpoint {D : Model} {root k x y : Nat}
    (hp : RootedPathAxioms D root) (a : CountedWalk D root k x)
    (b : CountedWalk D root k y) : x = y := by
  induction a generalizing y with
  | refl => cases b; rfl
  | @step k p q ha hq hs ih =>
    cases b with
    | @step _ p' q' hb hq' hs' =>
      have he := ih hb
      subst p'
      exact hp.outgoing_unique p ha.mem q hq _ hq' hs hs'

theorem CountedWalk.prefix {D : Model} {root k x i : Nat}
    (h : CountedWalk D root k x) (hi : i ≤ k) : ∃ y, CountedWalk D root i y := by
  induction h with
  | refl hr =>
    have he : i = 0 := by omega
    subst i
    exact ⟨root, .refl hr⟩
  | @step k x y h hy hs ih =>
    by_cases he : i = k + 1
    · subst i; exact ⟨y, .step h hy hs⟩
    · exact ih (by omega)

noncomputable def pathDistance (D : Model) (root x : Nat) : Nat := by
  classical
  exact if h : ∃ k, CountedWalk D root k x then Classical.choose h else 0

theorem pathDistance_spec {D : Model} {root x : Nat} (hp : RootedPathAxioms D root)
    (hx : x ∈ D.domain) : CountedWalk D root (pathDistance D root x) x := by
  classical
  have he := CountedWalk.of_walk ((closedReach_iff_walk D hp.root_mem).mp (hp.reachable x hx))
  simp only [pathDistance, dite_eq_left he]
  exact Classical.choose_spec he

/-- The finite rooted path axioms really yield a Hamiltonian chronological
enumeration, including exact absence of any additional successor edges. -/
theorem RootedPathAxioms.enumeration {D : Model} {root : Nat}
    (hp : RootedPathAxioms D root) : ∃ order, ChronologicalEnumeration D order := by
  classical
  let depths := D.domain.map (pathDistance D root)
  have hdmem : pathDistance D root root ∈ depths := List.mem_map.mpr ⟨root, hp.root_mem, rfl⟩
  have hdne : depths ≠ [] := List.ne_nil_of_mem hdmem
  cases hm : depths.max? with
  | none => exact False.elim (hdne (List.max?_eq_none_iff.mp hm))
  | some bound =>
    obtain ⟨hbmem, hbmax⟩ := List.max?_eq_some_iff.mp hm
    obtain ⟨last, hlast, hdepth⟩ := List.mem_map.mp hbmem
    have hlong : CountedWalk D root bound last := hdepth ▸ pathDistance_spec hp hlast
    have hex : ∀ i : Fin (bound + 1), ∃ x, CountedWalk D root i.val x :=
      fun i => hlong.prefix (by omega)
    let f : Fin (bound + 1) → Nat := fun i => Classical.choose (hex i)
    have hf : ∀ i, CountedWalk D root i.val (f i) := fun i => Classical.choose_spec (hex i)
    let order := List.ofFn f
    have hlen : order.length = bound + 1 := List.length_ofFn
    have hw : ∀ i (hi : i < order.length), CountedWalk D root i order[i] := by
      intro i hi
      simpa only [order, List.getElem_ofFn] using hf ⟨i, by omega⟩
    refine ⟨order, ?_, ?_, ?_⟩
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij he
      have heq : CountedWalk D root j order[i] := he.symm ▸ hw j hj
      have hh := (hw i hi).unique_length hp heq
      omega
    · intro x
      constructor
      · intro hx
        obtain ⟨i, hi, he⟩ := List.getElem_of_mem hx
        exact he ▸ (hw i hi).mem
      · intro hx
        have hb := hbmax _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
        have hi : pathDistance D root x < order.length := by omega
        have he := (hw _ hi).unique_endpoint hp (pathDistance_spec hp hx)
        exact he ▸ List.getElem_mem hi
    · intro i hi j hj
      constructor
      · intro hs
        exact ((hw i hi).step (hw j hj).mem hs).unique_length hp (hw j hj)
      · intro he
        subst j
        have hnext := hw (i + 1) hj
        cases hnext with
        | @step _ p _ hprev _ hs =>
          have he := (hw i hi).unique_endpoint hp hprev
          exact he.symm ▸ hs

#print axioms CountedWalk.unique_length
#print axioms CountedWalk.unique_endpoint
#print axioms RootedPathAxioms.enumeration
end StackSorting.SparseEndpointMSO
