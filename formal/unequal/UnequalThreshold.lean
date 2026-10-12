import UnequalFinite

/-! The sharp physical-capacity threshold.

`MinimalForbiddenH` and `SortMinimalH` are the capacity-`H` versions of
`MinimalForbidden` and `SortMinimal`. For unequal widths `r,s >= 2`:
- when `H <= max(r,s)+1`, every capacity-`H` basis element has length exactly
  `H+1`, and these are characterized explicitly: generated ones start with `H`,
  sortable ones end with `0`; and
- when `H >= max(r,s)+2`, both capacity-`H` classes have basis elements of
  unbounded length. -/
namespace StackSorting.Generalized
namespace Unequal
open BasisFamily (delete)

def MinimalForbiddenH (r s H n : Nat) (p : List Nat) : Prop :=
  p.Perm (List.range n) ∧ ¬ RunH r s H [] (List.range n) p [] ∧
    ∀ a, a < n → RunH r s H [] (delete a (List.range n)) (delete a p) []

def SortMinimalH (r s H n : Nat) (π : List Nat) : Prop :=
  π.Perm (List.range n) ∧ ¬ RunH r s H [] π (List.range n) [] ∧
    ∀ a, a < n → RunH r s H [] (delete a π) (delete a (List.range n)) []

/-! Standardization after deleting the value `a`. -/

def std (a x : Nat) : Nat := if a < x then x - 1 else x
def unstd (a y : Nat) : Nat := if a ≤ y then y + 1 else y

theorem unstd_std {a x : Nat} (h : x ≠ a) : unstd a (std a x) = x := by
  unfold std unstd; split <;> split <;> omega

theorem map_unstd_std {a : Nat} : ∀ (l : List Nat), (∀ x ∈ l, x ≠ a) →
    (l.map (std a)).map (unstd a) = l := by
  intro l h
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨unstd_std (h x (by simp)), ih (fun y hy => h y (by simp [hy]))⟩

theorem delete_range_split {a n : Nat} (ha : a < n) :
    delete a (List.range n) = List.range' 0 a ++ List.range' (a+1) (n-a-1) := by
  have h₁ : List.range n = List.range' 0 a ++ (a :: List.range' (a+1) (n-a-1)) := by
    rw [List.range_eq_range']
    have hz := List.range'_append (s := 0) (m := a) (n := n-a) (step := 1)
    rw [show a + (n-a) = n by omega, show n - a = (n-a-1)+1 by omega, List.range'_succ] at hz
    simpa using hz.symm
  rw [h₁, delete_append, delete_cons_self,
    delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
    delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega)]

theorem std_range {a n : Nat} (ha : a < n) :
    (delete a (List.range n)).map (std a) = List.range (n-1) := by
  rw [delete_range_split ha, List.map_append]
  have h₁ : (List.range' 0 a).map (std a) = List.range' 0 a := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.length_range'] at h₂
      simp [std] <;> omega
  have h₂ : (List.range' (a+1) (n-a-1)).map (std a) = List.range' a (n-a-1) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.length_range'] at h₂
      simp [std] <;> omega
  rw [h₁, h₂, List.range_eq_range']
  have hz := List.range'_append (s := 0) (m := a) (n := n-a-1) (step := 1)
  rw [show a + (n-a-1) = n - 1 by omega] at hz
  simpa using hz

theorem unstd_range {a n : Nat} (ha : a < n) :
    (List.range (n-1)).map (unstd a) = delete a (List.range n) := by
  rw [← std_range ha, map_unstd_std]
  intro x hx
  exact (mem_delete.mp hx).2

theorem std_perm {a n : Nat} {p : List Nat} (hp : p.Perm (List.range n)) (ha : a < n) :
    ((delete a p).map (std a)).Perm (List.range (n-1)) := by
  rw [← std_range ha]
  exact (hp.filter _).map _

theorem genH_delete_iff {r s H n a : Nat} {p : List Nat} (ha : a < n) :
    RunH r s H [] (delete a (List.range n)) (delete a p) [] ↔
      RunH r s H [] (List.range (n-1)) ((delete a p).map (std a)) [] := by
  constructor
  · intro h
    have hz := h.map (std a)
    simp only [List.map_nil] at hz
    rwa [std_range ha] at hz
  · intro h
    have hz := h.map (unstd a)
    simp only [List.map_nil] at hz
    rwa [unstd_range ha, map_unstd_std _ (fun x hx => (mem_delete.mp hx).2)] at hz

/-! Deleting a value never breaks `BoundedAt`. -/

theorem bounded_after {a : Nat} : ∀ (l : List Nat) (B : Nat),
    BoundedAt (B+1) l → a ∉ l → a + 1 ≤ B → BoundedAt B (l.map (std a)) := by
  intro l
  induction l with
  | nil => intro _ _ _ _; trivial
  | cons y l ih =>
    intro B hb ha hab
    have hya : y ≠ a := fun h => ha (by simp [h])
    refine ⟨?_, ih (B+1) hb.2 (fun h => ha (by simp [h])) (by omega)⟩
    have := hb.1
    unfold std; split <;> omega

theorem boundedAt_delete_std {a : Nat} : ∀ (l : List Nat) (B : Nat),
    BoundedAt B l → a ∈ l → l.Nodup → BoundedAt B ((delete a l).map (std a)) := by
  intro l
  induction l with
  | nil => intro _ _ h; simp at h
  | cons y l ih =>
    intro B hb ha hnd
    have hnd' := List.nodup_cons.mp hnd
    by_cases hy : y = a
    · subst hy
      rw [delete_cons_self, delete_eq_self (by intro x hx he; subst he; exact hnd'.1 hx)]
      exact bounded_after l B hb.2 hnd'.1 hb.1
    · rw [delete_cons_ne _ hy, List.map_cons]
      have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hy
        · exact h
      refine ⟨?_, ih (B+1) hb.2 ha' hnd'.2⟩
      have := hb.1
      unfold std; split <;> omega

/-! The combinatorics of the finite basis. -/

theorem not_boundedAt_iff {B : Nat} {l : List Nat} :
    ¬ BoundedAt B l ↔ ∃ i, ∃ h : i < l.length, B + i ≤ l[i] := by
  rw [boundedAt_iff_getElem]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    apply h
    intro i hi
    have : ¬ (B + i ≤ l[i]) := fun h' => hn ⟨i, hi, h'⟩
    omega
  · rintro ⟨i, hi, hv⟩ h
    have := h i hi
    omega

/-- A violation in a long permutation survives some single deletion. -/
theorem shrink {H n : Nat} {p : List Nat} (hp : p.Perm (List.range n)) (hn : H + 2 ≤ n)
    (hv : ¬ BoundedAt H p) : ∃ a, a < n ∧ ¬ BoundedAt H ((delete a p).map (std a)) := by
  obtain ⟨i, hi, hpi⟩ := not_boundedAt_iff.mp hv
  have hnd := perm_nodup hp
  have hl := perm_length hp
  cases p with
  | nil => simp at hl; omega
  | cons x tail =>
    have hnd' := List.nodup_cons.mp hnd
    have hx : x < n := perm_mem_lt hp (by simp)
    rcases i with _ | k
    · simp at hpi
      by_cases hxn : x = n - 1
      · refine ⟨0, by omega, ?_⟩
        rw [delete_cons_ne _ (by omega), List.map_cons]
        intro hb
        have := hb.1
        unfold std at this; split at this <;> omega
      · refine ⟨n - 1, by omega, ?_⟩
        rw [delete_cons_ne _ hxn, List.map_cons]
        intro hb
        have := hb.1
        unfold std at this; split at this <;> omega
    · refine ⟨x, hx, ?_⟩
      rw [delete_cons_self, delete_eq_self (by intro y hy he; subst he; exact hnd'.1 hy)]
      apply not_boundedAt_iff.mpr
      have hk : k < tail.length := by simp at hi; omega
      have hval : tail[k] < n := perm_mem_lt hp (by simp [List.getElem_mem hk])
      refine ⟨k, by simpa using hk, ?_⟩
      simp only [List.getElem_map]
      simp only [List.getElem_cons_succ] at hpi
      unfold std; split <;> omega

theorem exact_violation {H n : Nat} {p : List Nat} (hp : p.Perm (List.range n))
    (hn : n ≤ H + 1) (hv : ¬ BoundedAt H p) : n = H + 1 ∧ ∃ tail, p = H :: tail := by
  obtain ⟨i, hi, hpi⟩ := not_boundedAt_iff.mp hv
  have hval : p[i] < n := perm_mem_lt hp (List.getElem_mem hi)
  have hi0 : i = 0 := by omega
  subst hi0
  cases p with
  | nil => simp at hi
  | cons x tail =>
    simp at hpi hval
    exact ⟨by omega, tail, by simp; omega⟩

theorem bounded_short {H : Nat} {q : List Nat} (hq : q.Perm (List.range H)) : BoundedAt H q := by
  rw [boundedAt_iff_getElem]
  intro i hi
  have := perm_mem_lt hq (List.getElem_mem hi)
  omega

/-- Finite basis for generation: when `H <= max(r,s)+1`, the capacity-`H` basis
elements are exactly the permutations of length `H+1` that start with `H`. -/
theorem finite_basis_gen {r s H n : Nat} {p : List Nat} (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ max r s + 1) :
    MinimalForbiddenH r s H n p ↔
      p.Perm (List.range n) ∧ n = H + 1 ∧ ∃ tail, p = H :: tail := by
  constructor
  · rintro ⟨hp, hno, hdel⟩
    have hnb : ¬ BoundedAt H p := fun hb => hno ((finite_side hr hs hH hp).1.mpr hb)
    have hall : ∀ a, a < n → BoundedAt H ((delete a p).map (std a)) := by
      intro a ha
      exact (finite_side hr hs hH (std_perm hp ha)).1.mp ((genH_delete_iff ha).mp (hdel a ha))
    have hn : n ≤ H + 1 := by
      apply Classical.byContradiction
      intro hn
      obtain ⟨a, ha, hbad⟩ := shrink hp (by omega) hnb
      exact hbad (hall a ha)
    exact ⟨hp, exact_violation hp hn hnb⟩
  · rintro ⟨hp, rfl, tail, rfl⟩
    refine ⟨hp, fun h => ?_, fun a ha => ?_⟩
    · have hb := (finite_side hr hs hH hp).1.mp h
      have := hb.1
      omega
    · apply (genH_delete_iff ha).mpr
      apply (finite_side hr hs hH (std_perm hp ha)).1.mpr
      simpa using bounded_short (std_perm hp ha)

/-! Inversion and duality for capacity-`H` basis elements. -/

theorem MinimalForbiddenH.toSort {r s H n : Nat} {p : List Nat}
    (h : MinimalForbiddenH r s H n p) : SortMinimalH r s H n (inv p) := by
  obtain ⟨hp, hno, hdel⟩ := h
  refine ⟨inv_perm hp, fun hs => hno ((genH_iff_sortH_inv hp).mpr hs), ?_⟩
  intro a ha
  have hal : a < p.length := by rw [perm_length hp]; exact ha
  have hb : p[a] < n := perm_mem_lt hp (List.getElem_mem hal)
  have hz := (hdel p[a] hb).map (fun v => p.idxOf v)
  have hfa : p.idxOf p[a] = a := (perm_nodup hp).idxOf_getElem a hal
  simp only [List.map_nil] at hz
  rw [map_delete _ (fun x hx => idxOf_injOn hp x hx _ hb),
    map_delete _ (fun x hx => idxOf_injOn hp x (by simpa using perm_mem_lt hp hx) _ hb),
    hfa, map_idxOf_self hp] at hz
  simpa [inv, perm_length hp] using hz

theorem SortMinimalH.toGen {r s H n : Nat} {π : List Nat}
    (h : SortMinimalH r s H n π) : MinimalForbiddenH r s H n (inv π) := by
  obtain ⟨hp, hno, hdel⟩ := h
  refine ⟨inv_perm hp, fun hg => hno ((sortH_iff_genH_inv hp).mpr hg), ?_⟩
  intro b hb
  have hbl : b < π.length := by rw [perm_length hp]; exact hb
  have ha : π[b] < n := perm_mem_lt hp (List.getElem_mem hbl)
  have hz := (hdel π[b] ha).map (fun v => π.idxOf v)
  have hfb : π.idxOf π[b] = b := (perm_nodup hp).idxOf_getElem b hbl
  simp only [List.map_nil] at hz
  rw [map_delete _ (fun x hx => idxOf_injOn hp x (by simpa using perm_mem_lt hp hx) _ ha),
    map_delete _ (fun x hx => idxOf_injOn hp x hx _ ha),
    hfb, map_idxOf_self hp] at hz
  simpa [inv, perm_length hp] using hz

theorem MinimalForbiddenH.toDual {r s H n : Nat} {p : List Nat}
    (h : MinimalForbiddenH r s H n p) : SortMinimalH s r H n (rc p) := by
  obtain ⟨hp, hno, hdel⟩ := h
  have hpl := perm_length hp
  refine ⟨rc_perm hp, fun hs => hno ((genH_iff_sortH_rc hp).mpr hs), ?_⟩
  intro a ha
  have hb : n - 1 - a < n := by omega
  have hz := (hdel (n-1-a) hb).reverse.map (fun v => n - 1 - v)
  simp only [List.map_nil] at hz
  rw [delete_reverse, delete_reverse,
    map_delete _ (fun x hx => compl_injOn hb x (by simpa using perm_mem_lt hp (List.mem_reverse.mp hx))),
    map_delete _ (fun x hx => compl_injOn hb x (by simpa using hx)),
    range_reverse_map, show n - 1 - (n - 1 - a) = a by omega] at hz
  simpa [rc, hpl] using hz

theorem inv_inv {n : Nat} {π : List Nat} (hp : π.Perm (List.range n)) : inv (inv π) = π := by
  have hq := inv_perm hp
  apply List.ext_getElem
  · simp [inv, perm_length hp]
  · intro i h₁ h₂
    have hv : π[i] < n := perm_mem_lt hp (List.getElem_mem h₂)
    have hvl : π[i] < (inv π).length := by rw [perm_length hq]; exact hv
    have hqi : (inv π)[π[i]] = i := by
      simp only [inv, List.getElem_map, List.getElem_range]
      exact (perm_nodup hp).idxOf_getElem i h₂
    have key := (perm_nodup hq).idxOf_getElem π[i] hvl
    rw [hqi] at key
    simp only [inv, List.getElem_map, List.getElem_range]
    exact key

/-- Finite basis for sorting: when `H <= max(r,s)+1`, the capacity-`H` sortable
basis elements are exactly the permutations of length `H+1` that end with `0`. -/
theorem finite_basis_sort {r s H n : Nat} {π : List Nat} (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ max r s + 1) :
    SortMinimalH r s H n π ↔ π.Perm (List.range n) ∧ n = H + 1 ∧ π[H]? = some 0 := by
  constructor
  · intro h
    have hp := h.1
    obtain ⟨-, hn, tail, ht⟩ := (finite_basis_gen hr hs hH).mp h.toGen
    refine ⟨hp, hn, ?_⟩
    have h0 : (inv π)[0]'(by simp [inv, perm_length hp]; omega) = H := by simp [ht]
    simp only [inv, List.getElem_map, List.getElem_range] at h0
    have hm : (0 : Nat) ∈ π := perm_lt_mem hp (by omega)
    have hl := idxOf_lt hm
    rw [h0] at hl
    have := List.getElem_idxOf (idxOf_lt hm)
    simp only [h0] at this
    rw [List.getElem?_eq_getElem hl, this]
  · rintro ⟨hp, rfl, hlast⟩
    have hHl : H < π.length := by rw [perm_length hp]; omega
    rw [List.getElem?_eq_getElem hHl] at hlast
    have h0 : π[H] = 0 := by simpa using hlast
    have hg : MinimalForbiddenH r s H (H+1) (inv π) := by
      apply (finite_basis_gen hr hs hH).mpr
      refine ⟨inv_perm hp, rfl, (inv π).tail, ?_⟩
      have hlen : 0 < (inv π).length := by simp [inv, perm_length hp]
      have hhead : (inv π)[0] = H := by
        simp only [inv, List.getElem_map, List.getElem_range]
        rw [← h0]
        exact (perm_nodup hp).idxOf_getElem H hHl
      cases hq : inv π with
      | nil => simp [hq] at hlen
      | cons x xs => simp [hq] at hhead; simp [hhead]
    have := hg.toSort
    rwa [inv_inv hp] at this

/-! The infinite side: the family's deletions fit capacity `s+2`. -/

theorem lowSeg_bounded (s : Nat) : ∀ (c a B : Nat), s + 2 + 2*a ≤ B → BoundedAt B (lowSeg s a c) := by
  intro c
  induction c with
  | zero => intro _ _ _; simp [lowSeg, BoundedAt]
  | succ c ih =>
    intro a B h
    rw [lowSeg_succ, boundedAt_append]
    refine ⟨⟨by omega, by omega, trivial⟩, ih (a+1) _ (by simp; omega)⟩

theorem relaySeg_bounded (r s : Nat) (hr : 1 ≤ r) : ∀ (c a B : Nat), s + 2*r + 2*a ≤ B →
    BoundedAt B (relaySeg r s a c) := by
  intro c
  induction c with
  | zero => intro _ _ _; simp [relaySeg, BoundedAt]
  | succ c ih =>
    intro a B h
    rw [relaySeg_succ, boundedAt_append]
    refine ⟨⟨by omega, by omega, trivial⟩, ih (a+1) _ (by simp; omega)⟩

theorem all_bounded {B : Nat} : ∀ (l : List Nat), (∀ x ∈ l, x + 1 ≤ B) → BoundedAt B l := by
  intro l
  induction l generalizing B with
  | nil => intro _; trivial
  | cons x l ih =>
    intro h
    exact ⟨h x (by simp), ih (fun y hy => by have := h y (by simp [hy]); omega)⟩

theorem family_boundedAt {r s m : Nat} (hr : 2 ≤ r) (hrs : r < s) :
    BoundedAt (s+2) (family r s m) := by
  rw [family_segments, boundedAt_append, boundedAt_append, boundedAt_append]
  refine ⟨lowSeg_bounded s _ 0 _ (by omega), ?_, ?_, ?_⟩
  · exact all_bounded _ (fun x hx => by rw [List.mem_range'] at hx; omega)
  · exact relaySeg_bounded r s (by omega) _ 0 _ (by simp [length_lowSeg]; omega)
  · simp only [length_lowSeg, length_relaySeg, List.length_range']
    refine ⟨by omega, by omega, all_bounded _ (fun x hx => ?_)⟩
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := mem_lateSeg.mp hx; omega
    · have := mem_termSeg.mp hx; omega

/-- Every single deletion of the family is generated within capacity `s+2`. -/
theorem family_deletion_capacity {r s m : Nat} (hr : 2 ≤ r) (hrs : r < s) (a : Nat)
    (ha : a < 2*s+r+2*m) :
    RunH r s (s+2) [] (delete a (List.range (2*s+r+2*m))) (delete a (family r s m)) [] := by
  have hrun := all_deletions hr hrs a ha
  have hstd := hrun.map (std a)
  simp only [List.map_nil] at hstd
  rw [std_range ha] at hstd
  have hb := boundedAt_delete_std (a := a) (family r s m) (s+2) (family_boundedAt hr hrs)
    (perm_lt_mem (family_perm r s m hr hrs) ha) (family_nodup r s m hr hrs)
  exact (genH_delete_iff ha).mpr (Run.capacity hstd hb)

theorem family_minimalH {r s m H : Nat} (hr : 2 ≤ r) (hrs : r < s) (hH : s + 2 ≤ H) :
    MinimalForbiddenH r s H (2*s+r+2*m) (family r s m) :=
  ⟨family_perm r s m hr hrs, fun h => family_not_generated r s m hr hrs h.toRun,
    fun a ha => (family_deletion_capacity hr hrs a ha).mono hH⟩

/-- **Sharp threshold.** For unequal widths `r,s >= 2` and every capacity `H`:
- if `H <= max(r,s)+1`, every capacity-`H` basis element of either class has
  length exactly `H+1`, so both bases are finite;
- if `H >= max(r,s)+2`, both capacity-`H` classes have basis elements beyond
  every length bound. -/
theorem capacity_threshold (r s H : Nat) (hr : 2 ≤ r) (hs : 2 ≤ s) (hne : r ≠ s) :
    (H ≤ max r s + 1 →
      (∀ n p, MinimalForbiddenH r s H n p → n = H + 1) ∧
      (∀ n π, SortMinimalH r s H n π → n = H + 1)) ∧
    (max r s + 2 ≤ H →
      (∀ bound, ∃ p, bound < p.length ∧ MinimalForbiddenH r s H p.length p) ∧
      (∀ bound, ∃ π, bound < π.length ∧ SortMinimalH r s H π.length π)) := by
  refine ⟨fun hH => ⟨fun n p h => ((finite_basis_gen (by omega) (by omega) hH).mp h).2.1,
      fun n π h => ((finite_basis_sort (by omega) (by omega) hH).mp h).2.1⟩, fun hH => ?_⟩
  by_cases hlt : r < s
  · have hH' : s + 2 ≤ H := by simp [Nat.max_def] at hH; split at hH <;> omega
    refine ⟨fun bound => ?_, fun bound => ?_⟩
    · have hF := family_minimalH (m := bound) hr hlt hH'
      have hlen : (family r s bound).length = 2*s+r+2*bound :=
        family_length r s bound (by omega) (by omega)
      exact ⟨_, by rw [hlen]; omega, by rw [hlen]; exact hF⟩
    · have hS := (family_minimalH (m := bound) hr hlt hH').toSort
      have hlen : (inv (family r s bound)).length = 2*s+r+2*bound := by
        rw [length_inv, family_length r s bound (by omega) (by omega)]
      exact ⟨_, by rw [hlen]; omega, by rw [hlen]; exact hS⟩
  · have hsr : s < r := by omega
    have hH' : r + 2 ≤ H := by simp [Nat.max_def] at hH; split at hH <;> omega
    refine ⟨fun bound => ?_, fun bound => ?_⟩
    · have hG := (family_minimalH (m := bound) hs hsr hH').toDual.toGen
      have hlen : (inv (rc (family s r bound))).length = 2*r+s+2*bound := by
        rw [length_inv, length_rc, family_length s r bound (by omega) (by omega)]
      exact ⟨_, by rw [hlen]; omega, by rw [hlen]; exact hG⟩
    · have hS := (family_minimalH (m := bound) hs hsr hH').toDual
      have hlen : (rc (family s r bound)).length = 2*r+s+2*bound := by
        rw [length_rc, family_length s r bound (by omega) (by omega)]
      exact ⟨_, by rw [hlen]; omega, by rw [hlen]; exact hS⟩

#print axioms boundedAt_delete_std
#print axioms finite_basis_sort
#print axioms family_deletion_capacity
#print axioms capacity_threshold
#print axioms shrink
#print axioms finite_basis_gen
end Unequal
end StackSorting.Generalized
