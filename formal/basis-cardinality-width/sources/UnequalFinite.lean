import UnequalCapacity

/-! The finite side: for physical capacity `H <= max(r,s)+1` the generated
class is exactly `BoundedAt H`, and the sortable class is exactly the
maximum-drop class `DropOK H` (`i - pi_i <= H - 1` at every position). This
holds in both orientations and for all positive widths. -/
namespace StackSorting.Generalized
namespace Unequal
open BasisFamily (delete)

/-- The sortable-side condition: every entry drops by less than `H`. -/
def DropOK (H : Nat) (π : List Nat) : Prop :=
  ∀ i (h : i < π.length), i + 1 ≤ π[i] + H

/-- Finite side for generation when the pop width reaches `H-1`. -/
theorem gen_capacity_iff {r s H n : Nat} {p : List Nat} (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ s + 1) (hp : p.Perm (List.range n)) :
    RunH r s H [] (List.range n) p [] ↔ BoundedAt H p := by
  constructor
  · exact RunH.bounded
  · intro hb
    have hz := generate_bounded hr hs hH p [] 0 n (by simpa [List.range_eq_range'] using hp)
      (by simp) (Or.inl rfl) (by simpa using hb)
    simpa [List.range_eq_range'] using hz

/-- Exact minimum capacity, for any widths: once `p` is generated at all, it is
generated within capacity `H` exactly when `BoundedAt H p`. -/
theorem gen_capacity_exact {r s H n : Nat} {p : List Nat}
    (h : Run r s [] (List.range n) p []) :
    RunH r s H [] (List.range n) p [] ↔ BoundedAt H p :=
  ⟨RunH.bounded, Run.capacity h⟩

/-! Inversion and duality with capacity (`RunH.map`, `RunH.reverse`). -/

theorem genH_iff_sortH_inv {r s H n : Nat} {p : List Nat} (hp : p.Perm (List.range n)) :
    RunH r s H [] (List.range n) p [] ↔ RunH r s H [] (inv p) (List.range n) [] := by
  constructor
  · intro h
    have hz := h.map (fun v => p.idxOf v)
    simp only [List.map_nil] at hz
    rw [map_idxOf_self hp] at hz
    simpa [inv, perm_length hp] using hz
  · intro h
    have hz := h.map (fun i => p.getD i 0)
    simp only [List.map_nil] at hz
    rw [map_getD_inv hp, map_getD_range hp] at hz
    exact hz

theorem sortH_iff_genH_inv {r s H n : Nat} {π : List Nat} (hp : π.Perm (List.range n)) :
    RunH r s H [] π (List.range n) [] ↔ RunH r s H [] (List.range n) (inv π) [] := by
  constructor
  · intro h
    have hz := h.map (fun v => π.idxOf v)
    simp only [List.map_nil] at hz
    rw [map_idxOf_self hp] at hz
    simpa [inv, perm_length hp] using hz
  · intro h
    have hz := h.map (fun i => π.getD i 0)
    simp only [List.map_nil] at hz
    rw [map_getD_range hp, map_getD_inv hp] at hz
    exact hz

theorem genH_iff_sortH_rc {r s H n : Nat} {p : List Nat} (hp : p.Perm (List.range n)) :
    RunH r s H [] (List.range n) p [] ↔ RunH s r H [] (rc p) (List.range n) [] := by
  constructor
  · intro h
    have hz := h.reverse.map (fun v => n - 1 - v)
    simp only [List.map_nil] at hz
    rw [range_reverse_map] at hz
    simpa [rc, perm_length hp] using hz
  · intro h
    have hz := h.reverse.map (fun v => n - 1 - v)
    simp only [List.map_nil] at hz
    rw [range_reverse_map, rc_reverse_map hp] at hz
    exact hz

/-! The two statistics under inversion and reverse-complement. -/

theorem boundedAt_inv_iff {H n : Nat} {π : List Nat} (hp : π.Perm (List.range n)) :
    BoundedAt H (inv π) ↔ DropOK H π := by
  rw [boundedAt_iff_getElem]
  have hl := perm_length hp
  constructor
  · intro h i hi
    have hv : π[i] < n := perm_mem_lt hp (List.getElem_mem hi)
    have := h π[i] (by simp [inv]; omega)
    simp only [inv, List.getElem_map, List.getElem_range] at this
    rw [(perm_nodup hp).idxOf_getElem i hi] at this
    omega
  · intro h v hv
    have hv' : v < n := by simp [inv] at hv; omega
    have hm : v ∈ π := perm_lt_mem hp hv'
    have hil := idxOf_lt hm
    have := h (π.idxOf v) hil
    rw [List.getElem_idxOf hil] at this
    simp only [inv, List.getElem_map, List.getElem_range]
    omega

theorem rc_getElem {n : Nat} {p : List Nat} (hp : p.Perm (List.range n)) (i : Nat)
    (hi : i < (rc p).length) :
    (rc p)[i] = n - 1 - p[n - 1 - i]'(by simp [rc] at hi; rw [perm_length hp] at hi ⊢; omega) := by
  have hl := perm_length hp
  simp only [rc, List.getElem_map, List.getElem_reverse]
  simp only [hl]

theorem boundedAt_iff_dropOK_rc {H n : Nat} {p : List Nat} (hp : p.Perm (List.range n)) :
    BoundedAt H p ↔ DropOK H (rc p) := by
  rw [boundedAt_iff_getElem]
  have hl := perm_length hp
  constructor
  · intro h i hi
    have hi' : i < n := by simp [rc] at hi; omega
    have hj : n - 1 - i < p.length := by omega
    have hv : p[n-1-i] < n := perm_mem_lt hp (List.getElem_mem hj)
    have key := h (n-1-i) hj
    rw [rc_getElem hp i hi]
    omega
  · intro h j hj
    have hj' : j < n := by omega
    have hi : n - 1 - j < (rc p).length := by simp [rc]; omega
    have hv : p[j] < n := perm_mem_lt hp (List.getElem_mem hj)
    have key := h (n-1-j) hi
    rw [rc_getElem hp (n-1-j) hi] at key
    have he : n - 1 - (n - 1 - j) = j := by omega
    simp only [he] at key
    omega

/-- The finite side, for all positive widths and every `H <= max(r,s)+1`, in
both classes: capacity-`H` generation is `BoundedAt H`, and capacity-`H`
sorting is the maximum-drop condition `DropOK H`. -/
theorem finite_side {r s H n : Nat} {p : List Nat} (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ max r s + 1) (hp : p.Perm (List.range n)) :
    (RunH r s H [] (List.range n) p [] ↔ BoundedAt H p) ∧
      (RunH r s H [] p (List.range n) [] ↔ DropOK H p) := by
  by_cases hrs : r ≤ s
  · have hH' : H ≤ s + 1 := by simp [hrs] at hH; omega
    refine ⟨gen_capacity_iff hr hs hH' hp, ?_⟩
    rw [sortH_iff_genH_inv hp, gen_capacity_iff hr hs hH' (inv_perm hp), boundedAt_inv_iff hp]
  · have hH' : H ≤ r + 1 := by simp [Nat.max_def] at hH; split at hH <;> omega
    have hgen : ∀ q : List Nat, q.Perm (List.range n) →
        (RunH r s H [] (List.range n) q [] ↔ BoundedAt H q) := by
      intro q hq
      rw [genH_iff_sortH_rc hq, sortH_iff_genH_inv (rc_perm hq),
        gen_capacity_iff hs hr hH' (inv_perm (rc_perm hq)), boundedAt_inv_iff (rc_perm hq),
        boundedAt_iff_dropOK_rc hq]
    refine ⟨hgen p hp, ?_⟩
    rw [sortH_iff_genH_inv hp, hgen (inv p) (inv_perm hp), boundedAt_inv_iff hp]

#print axioms gen_capacity_iff
#print axioms gen_capacity_exact
#print axioms finite_side
end Unequal
end StackSorting.Generalized
