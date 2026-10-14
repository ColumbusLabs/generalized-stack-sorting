import UnequalBasis

/-! Inversion and reverse-complement duality, and infinite bases for both
classes and both orientations.

`SortMinimal r s n input` is the sorting analogue of the AI-reviewed
`MinimalForbidden`: `input` is a permutation of `range n` that no original
`(r,s)` history sorts to `range n`, while every single-token deletion (same
labels) is sorted. The machine is label-oblivious (`Run.map`), so relabelling
tokens by their input positions exchanges generation and sorting. Reversing a
history exchanges pushes and pops, and so the two widths. -/
namespace StackSorting.Generalized

/-- Reversal exchanges push and pop, hence the push and pop widths. -/
theorem Step.reverse {α : Type} {r s : Nat} {held input output final : List α}
    (h : Step r s held input output final) :
    Step s r final output.reverse input.reverse held := by
  cases h with
  | push pre post x allowed => simpa using Step.pop (r := s) (s := r) pre post x allowed
  | pop pre post x allowed => simpa using Step.push (r := s) (s := r) pre post x allowed

theorem Run.reverse {α : Type} {r s : Nat} {held input output final : List α}
    (h : Run r s held input output final) :
    Run s r final output.reverse input.reverse held := by
  induction h with
  | nil held => simpa using Run.nil (r := s) (s := r) held
  | cons head tail ih =>
    have hz := ih.append (Run.single head.reverse)
    simpa [List.reverse_append] using hz

namespace Unequal
open BasisFamily (delete MinimalForbidden)

def SortMinimal (r s n : Nat) (input : List Nat) : Prop :=
  input.Perm (List.range n) ∧ ¬ Run r s [] input (List.range n) [] ∧
    ∀ a, a < n → Run r s [] (delete a input) (delete a (List.range n)) []


/-! Inverse and reverse-complement of a permutation of `range n`. -/

def inv (p : List Nat) : List Nat := (List.range p.length).map (fun v => p.idxOf v)

def rc (p : List Nat) : List Nat := p.reverse.map (fun v => p.length - 1 - v)

theorem length_inv (p : List Nat) : (inv p).length = p.length := by simp [inv]

theorem length_rc (p : List Nat) : (rc p).length = p.length := by simp [rc]

theorem perm_mem_lt {p : List Nat} {n x : Nat} (hp : p.Perm (List.range n)) (hx : x ∈ p) :
    x < n := by
  have := hp.mem_iff.mp hx
  simpa using this

theorem perm_lt_mem {p : List Nat} {n x : Nat} (hp : p.Perm (List.range n)) (hx : x < n) :
    x ∈ p := hp.mem_iff.mpr (by simpa using hx)

theorem perm_length {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) : p.length = n := by
  simpa using hp.length_eq

theorem perm_nodup {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) : p.Nodup :=
  hp.nodup_iff.mpr List.nodup_range

theorem idxOf_lt {p : List Nat} {x : Nat} (hx : x ∈ p) : p.idxOf x < p.length :=
  List.idxOf_lt_length_iff.mpr hx

/-- Relabelling a permutation by positions gives the identity. -/
theorem map_idxOf_self {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) :
    p.map (fun v => p.idxOf v) = List.range n := by
  apply List.ext_getElem
  · simp [perm_length hp]
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    exact (perm_nodup hp).idxOf_getElem i (by simpa using h₁)

theorem map_getD_range {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) :
    (List.range n).map (fun i => p.getD i 0) = p := by
  apply List.ext_getElem
  · simp [perm_length hp]
  · intro i h₁ h₂
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

theorem map_getD_inv {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) :
    (inv p).map (fun i => p.getD i 0) = List.range n := by
  apply List.ext_getElem
  · simp [inv, perm_length hp]
  · intro v h₁ h₂
    have hv : v < n := by simpa using h₂
    have hm : v ∈ p := perm_lt_mem hp hv
    have hl := idxOf_lt hm
    simp only [inv, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hl, Option.getD_some]
    exact List.getElem_idxOf hl

theorem inv_perm {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) :
    (inv p).Perm (List.range n) := by
  apply perm_range_of_mem
  · simp [inv, perm_length hp]
  · intro i hi
    have hil : i < p.length := by rw [perm_length hp]; exact hi
    have hval : p[i] < n := perm_mem_lt hp (List.getElem_mem hil)
    simp only [inv, List.mem_map, List.mem_range]
    exact ⟨p[i], by rw [perm_length hp]; exact hval, (perm_nodup hp).idxOf_getElem i hil⟩

theorem map_delete {f : Nat → Nat} {b : Nat} :
    ∀ (l : List Nat), (∀ x ∈ l, f x = f b → x = b) →
      (delete b l).map f = delete (f b) (l.map f) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
    intro h
    have ih' := ih (fun y hy => h y (by simp [hy]))
    by_cases hx : x = b
    · subst hx; simp [delete] at ih' ⊢; exact ih'
    · have hf : f x ≠ f b := fun he => hx (h x (by simp) he)
      simp [delete, hx, hf] at ih' ⊢
      exact ih'

theorem delete_reverse (b : Nat) (l : List Nat) : (delete b l).reverse = delete b l.reverse := by
  simp [delete, List.filter_reverse]

theorem idxOf_injOn {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) :
    ∀ x ∈ List.range n, ∀ y, y < n → p.idxOf x = p.idxOf y → x = y := by
  intro x hx y hy he
  have hx' : x ∈ p := perm_lt_mem hp (by simpa using hx)
  have hy' : y ∈ p := perm_lt_mem hp hy
  have h₁ := List.getElem_idxOf (idxOf_lt hx')
  have h₂ := List.getElem_idxOf (idxOf_lt hy')
  have : p[p.idxOf x]'(idxOf_lt hx') = p[p.idxOf y]'(idxOf_lt hy') := by simp [he]
  rw [h₁, h₂] at this
  exact this

theorem getD_injOn {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) :
    ∀ i, i < n → ∀ j, j < n → p.getD i 0 = p.getD j 0 → i = j := by
  intro i hi j hj he
  have hil : i < p.length := by rw [perm_length hp]; exact hi
  have hjl : j < p.length := by rw [perm_length hp]; exact hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil,
    List.getElem?_eq_getElem hjl, Option.getD_some] at he
  have h₁ := (perm_nodup hp).idxOf_getElem i hil
  have h₂ := (perm_nodup hp).idxOf_getElem j hjl
  rw [he] at h₁
  omega

/-- A generated basis element inverts to a sortable basis element. -/
theorem MinimalForbidden.toSort {r s n : Nat} {p : List Nat}
    (h : MinimalForbidden r s n p) : SortMinimal r s n (inv p) := by
  obtain ⟨hp, hno, hdel⟩ := h
  refine ⟨inv_perm hp, ?_, ?_⟩
  · intro hs
    apply hno
    have hz := hs.map (fun i => p.getD i 0)
    rw [map_getD_inv hp, map_getD_range hp] at hz
    exact hz
  · intro a ha
    have hal : a < p.length := by rw [perm_length hp]; exact ha
    have hb : p[a] < n := perm_mem_lt hp (List.getElem_mem hal)
    have hz := (hdel p[a] hb).map (fun v => p.idxOf v)
    have hfa : p.idxOf p[a] = a := (perm_nodup hp).idxOf_getElem a hal
    rw [map_delete _ (fun x hx => idxOf_injOn hp x hx _ hb),
      map_delete _ (fun x hx => idxOf_injOn hp x (by simpa using perm_mem_lt hp hx) _ hb),
      hfa, map_idxOf_self hp] at hz
    simpa [inv, perm_length hp] using hz

/-- A sortable basis element inverts to a generated basis element. -/
theorem SortMinimal.toGen {r s n : Nat} {π : List Nat}
    (h : SortMinimal r s n π) : MinimalForbidden r s n (inv π) := by
  obtain ⟨hp, hno, hdel⟩ := h
  refine ⟨inv_perm hp, ?_, ?_⟩
  · intro hg
    apply hno
    have hz := hg.map (fun i => π.getD i 0)
    rw [map_getD_range hp, map_getD_inv hp] at hz
    exact hz
  · intro b hb
    have hbl : b < π.length := by rw [perm_length hp]; exact hb
    have ha : π[b] < n := perm_mem_lt hp (List.getElem_mem hbl)
    have hz := (hdel π[b] ha).map (fun v => π.idxOf v)
    have hfb : π.idxOf π[b] = b := (perm_nodup hp).idxOf_getElem b hbl
    rw [map_delete _ (fun x hx => idxOf_injOn hp x (by simpa using perm_mem_lt hp hx) _ ha),
      map_delete _ (fun x hx => idxOf_injOn hp x hx _ ha),
      hfb, map_idxOf_self hp] at hz
    simpa [inv, perm_length hp] using hz

theorem range_reverse_map (n : Nat) :
    (List.range n).reverse.map (fun v => n - 1 - v) = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    simp at h₂
    omega

theorem rc_reverse_map {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) :
    (rc p).reverse.map (fun v => n - 1 - v) = p := by
  apply List.ext_getElem
  · simp [rc]
  · intro i h₁ h₂
    have hpl := perm_length hp
    simp only [rc, List.getElem_map, List.getElem_reverse, List.length_map,
      List.length_reverse]
    have hi : i < p.length := h₂
    have hlt : p[i] < n := perm_mem_lt hp (List.getElem_mem hi)
    simp only [hpl]
    have he : p.length - 1 - (p.length - 1 - i) = i := by omega
    simp only [hpl] at he
    simp [he]
    omega

theorem rc_perm {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) :
    (rc p).Perm (List.range n) := by
  apply perm_range_of_mem
  · simp [rc, perm_length hp]
  · intro i hi
    have hm : n - 1 - i ∈ p := perm_lt_mem hp (by omega)
    simp only [rc, List.mem_map, List.mem_reverse, perm_length hp]
    exact ⟨n - 1 - i, hm, by omega⟩

theorem compl_injOn {n b : Nat} (hb : b < n) :
    ∀ x, x < n → n - 1 - x = n - 1 - b → x = b := by
  intro x hx he; omega

/-- Reverse-complement duality: a generated basis element of `(r,s)` gives a
sortable basis element of `(s,r)`. -/
theorem MinimalForbidden.toDual {r s n : Nat} {p : List Nat}
    (h : MinimalForbidden r s n p) : SortMinimal s r n (rc p) := by
  obtain ⟨hp, hno, hdel⟩ := h
  have hpl := perm_length hp
  refine ⟨rc_perm hp, ?_, ?_⟩
  · intro hs
    apply hno
    have hz := hs.reverse.map (fun v => n - 1 - v)
    rw [range_reverse_map, rc_reverse_map hp] at hz
    exact hz
  · intro a ha
    have hb : n - 1 - a < n := by omega
    have hz := (hdel (n-1-a) hb).reverse.map (fun v => n - 1 - v)
    rw [delete_reverse, delete_reverse,
      map_delete _ (fun x hx => compl_injOn hb x (by simpa using perm_mem_lt hp (List.mem_reverse.mp hx))),
      map_delete _ (fun x hx => compl_injOn hb x (by simpa using hx)),
      range_reverse_map, show n - 1 - (n - 1 - a) = a by omega] at hz
    simpa [rc, hpl] using hz

/-! Infinite bases for every unequal pair of widths, in both classes. -/

/-- For every unequal `r,s >= 2`, the class generated by the original
`(r,s)` machine has basis elements beyond every length bound. -/
theorem gen_infinite_basis (r s : Nat) (hr : 2 ≤ r) (hs : 2 ≤ s) (hne : r ≠ s) (bound : Nat) :
    ∃ p, bound < p.length ∧ MinimalForbidden r s p.length p := by
  by_cases hlt : r < s
  · obtain ⟨m, hl, hm⟩ := infinite_basis hr hlt bound
    exact ⟨family r s m, hl, hm⟩
  · have hsr : s < r := by omega
    have hF := family_minimal (m := bound) hs hsr
    have hG := (MinimalForbidden.toDual hF).toGen
    have hlen : (inv (rc (family s r bound))).length = 2*r+s+2*bound := by
      rw [length_inv, length_rc, family_length s r bound (by omega) (by omega)]
    refine ⟨_, by rw [hlen]; omega, by rw [hlen]; exact hG⟩

/-- For every unequal `r,s >= 2`, the class of inputs sortable by the original
`(r,s)` machine has basis elements beyond every length bound. -/
theorem sort_infinite_basis (r s : Nat) (hr : 2 ≤ r) (hs : 2 ≤ s) (hne : r ≠ s) (bound : Nat) :
    ∃ π, bound < π.length ∧ SortMinimal r s π.length π := by
  by_cases hlt : r < s
  · have hF := family_minimal (m := bound) hr hlt
    have hS := MinimalForbidden.toSort hF
    have hlen : (inv (family r s bound)).length = 2*s+r+2*bound := by
      rw [length_inv, family_length r s bound (by omega) (by omega)]
    exact ⟨_, by rw [hlen]; omega, by rw [hlen]; exact hS⟩
  · have hsr : s < r := by omega
    have hF := family_minimal (m := bound) hs hsr
    have hS := MinimalForbidden.toDual hF
    have hlen : (rc (family s r bound)).length = 2*r+s+2*bound := by
      rw [length_rc, family_length s r bound (by omega) (by omega)]
    exact ⟨_, by rw [hlen]; omega, by rw [hlen]; exact hS⟩

#print axioms Run.reverse
#print axioms MinimalForbidden.toSort
#print axioms SortMinimal.toGen
#print axioms MinimalForbidden.toDual
#print axioms gen_infinite_basis
#print axioms sort_infinite_basis
end Unequal
end StackSorting.Generalized
