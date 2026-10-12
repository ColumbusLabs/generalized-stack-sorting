import GeneralizedCoordinateState

/-!
# Explicit O-run relabelling of actual complete outputs

A fixed cyclic permutation turns a coordinate block Z O^a into Z^(a+1).
The theorem includes arbitrary later coordinates, arbitrary sets of earlier
physical stacks with smaller labels, and every future input length. The
bijection is on output lists, not on histories or decorated-state witnesses.
-/
namespace StackSorting.Generalized
namespace Coordinates
namespace ORun

/-- Cycle the consecutive labels l,...,l+a; fix every other natural label. -/
def rho (l a x : Nat) : Nat :=
  if x = l then l+a else if l < x ∧ x ≤ l+a then x-1 else x

/-- Explicit inverse of rho, also fixing labels outside its block. -/
def rhoInv (l a x : Nat) : Nat :=
  if x = l+a then l else if l ≤ x ∧ x < l+a then x+1 else x

@[simp] theorem rho_first (l a : Nat) : rho l a l = l+a := by simp [rho]

@[simp] theorem rho_later {l a j : Nat} (hj : 1 ≤ j) (ha : j ≤ a) :
    rho l a (l+j) = l+j-1 := by
  have hn : l+j ≠ l := by omega
  have hi : l < l+j ∧ l+j ≤ l+a := by omega
  simp only [rho, ite_eq_right hn, ite_eq_left hi]

@[simp] theorem rho_before {l a x : Nat} (hx : x < l) : rho l a x = x := by
  simp [rho, show x ≠ l by omega, show ¬ l < x by omega]

@[simp] theorem rho_after {l a x : Nat} (hx : l+a < x) : rho l a x = x := by
  simp [rho, show x ≠ l by omega, show ¬ x ≤ l+a by omega]

@[simp] theorem rhoInv_before {l a x : Nat} (hx : x < l) : rhoInv l a x = x := by
  simp [rhoInv, show x ≠ l+a by omega, show ¬ l ≤ x by omega]

@[simp] theorem rhoInv_after {l a x : Nat} (hx : l+a < x) : rhoInv l a x = x := by
  simp [rhoInv, show x ≠ l+a by omega, show ¬ x < l+a by omega]

@[simp] theorem rhoInv_rho (l a x : Nat) : rhoInv l a (rho l a x) = x := by
  by_cases hf : x = l
  · subst x; simp [rhoInv, rho]
  · by_cases hi : l < x ∧ x ≤ l+a
    · have hn : x-1 ≠ l+a := by omega
      have hh : l ≤ x-1 ∧ x-1 < l+a := by omega
      simp [rho, hf, hi, rhoInv, hn, hh]
      omega
    · have hn : x ≠ l+a := by omega
      have hh : ¬ (l ≤ x ∧ x < l+a) := by omega
      simp [rho, hf, hi, rhoInv, hn, hh]

@[simp] theorem rho_rhoInv (l a x : Nat) : rho l a (rhoInv l a x) = x := by
  by_cases hf : x = l+a
  · subst x; simp [rhoInv, rho]
  · by_cases hi : l ≤ x ∧ x < l+a
    · have hn : x+1 ≠ l := by omega
      have hh : l < x+1 ∧ x+1 ≤ l+a := by omega
      simp [rhoInv, hf, hi, rho, hn, hh]
    · have hn : x ≠ l := by omega
      have hh : ¬ (l < x ∧ x ≤ l+a) := by omega
      simp [rhoInv, hf, hi, rho, hn, hh]

@[simp] theorem map_rhoInv_rho (l a : Nat) (xs : List Nat) :
    (xs.map (rho l a)).map (rhoInv l a) = xs := by
  simp [List.map_map, Function.comp_def]

@[simp] theorem map_rho_rhoInv (l a : Nat) (xs : List Nat) :
    (xs.map (rhoInv l a)).map (rho l a) = xs := by
  simp [List.map_map, Function.comp_def]

theorem map_fixed (f : Nat → Nat) (xs : List Nat)
    (fixed : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  calc
    xs.map f = xs.map (fun x => x) := List.map_congr_left fixed
    _ = xs := by simp

theorem map_rho_old {l a : Nat} {old : List Nat}
    (small : ∀ x ∈ old, x < l) : old.map (rho l a) = old := by
  exact map_fixed _ _ (fun x hx => rho_before (small x hx))

/-- Repeated top insertion reverses the consecutive labels introduced. -/
theorem build_zeros (next count : Nat) (held : List Nat) :
    build next (List.replicate count 0) held =
      some ((List.range' next count).reverse ++ held) := by
  induction count generalizing next held with
  | zero => simp [build]
  | succ count ih =>
    simp [List.replicate_succ, build, insertAt?, ih, List.range'_succ,
      List.reverse_cons, List.append_assoc]

/-- Repeated slot-one insertion leaves the old top in place. -/
theorem build_ones (next count top : Nat) (held : List Nat) :
    build next (List.replicate count 1) (top :: held) =
      some (top :: ((List.range' next count).reverse ++ held)) := by
  induction count generalizing next held with
  | zero => simp [build]
  | succ count ih =>
    simp [List.replicate_succ, build, insertAt?, ih, List.range'_succ,
      List.reverse_cons, List.append_assoc]

theorem rho_range (l a : Nat) :
    (List.range' (l+1) a).map (rho l a) = List.range' l a := by
  rw [List.range'_succ_left, List.map_map]
  apply map_fixed
  intro x hx
  have hb := List.mem_range'_1.mp hx
  have hn : x+1 ≠ l := by omega
  have hi : l < x+1 ∧ x+1 ≤ l+a := by omega
  simp [rho, hn, hi]

/-- The physical block identity; its relabelling is independent of old order. -/
theorem block_identity {l a : Nat} {old : List Nat}
    (small : ∀ x ∈ old, x < l) :
    (build l (0 :: List.replicate a 1) old).map (List.map (rho l a)) =
      build l (List.replicate (a+1) 0) old := by
  simp [build, insertAt?, build_ones, build_zeros, List.map_reverse,
    rho_range, map_rho_old small, List.range'_1_concat]

/-- Arbitrarily many later coordinates commute with the same fixed cycle.
This equality also includes failed decodings; it makes no validity assumption
about the suffix and does not erase correlations among its allowed digits. -/
theorem suffix_identity {l a : Nat} {old suffix : List Nat}
    (small : ∀ x ∈ old, x < l) :
    (build l ((0 :: List.replicate a 1) ++ suffix) old).map
        (List.map (rho l a)) =
      build l (List.replicate (a+1) 0 ++ suffix) old := by
  rw [build_append, build_append, ← block_identity small]
  simp only [List.length_cons, List.length_replicate]
  cases hb : build l (0 :: List.replicate a 1) old with
  | none => rfl
  | some middle =>
    change (build (l+(a+1)) suffix middle).map (List.map (rho l a)) =
      build (l+(a+1)) suffix (middle.map (rho l a))
    exact build_map (rho l a) (l+(a+1)) (l+(a+1)) suffix middle
        (by intro offset; apply rho_after; omega)

/-- Explicit inverse on the physical coordinate decoder. -/
theorem suffix_inverse {l a : Nat} {old suffix : List Nat}
    (small : ∀ x ∈ old, x < l) :
    (build l (List.replicate (a+1) 0 ++ suffix) old).map
        (List.map (rhoInv l a)) =
      build l ((0 :: List.replicate a 1) ++ suffix) old := by
  rw [← suffix_identity small]
  cases build l ((0 :: List.replicate a 1) ++ suffix) old <;> simp [Function.comp_def]

/-- The increasing future input is fixed, for every finite input length. -/
theorem future_fixed {l a next : Nat} (fresh : l+a < next) (m : Nat) :
    (List.range' next m).map (rho l a) = List.range' next m := by
  apply map_fixed
  intro x hx
  have hb := List.mem_range'_1.mp hx
  apply rho_after
  omega

theorem future_inverse_fixed {l a next : Nat} (fresh : l+a < next) (m : Nat) :
    (List.range' next m).map (rhoInv l a) = List.range' next m := by
  apply map_fixed
  intro x hx
  have hb := List.mem_range'_1.mp hx
  apply rhoInv_after
  omega

/-- A coordinate family includes arbitrary choices of earlier physical order
and an arbitrary correlated language of later coordinate words. -/
def Initial (l : Nat) (block : List Nat)
    (oldAllowed suffixAllowed : List Nat → Prop) (held : List Nat) : Prop :=
  ∃ old suffix, oldAllowed old ∧ suffixAllowed suffix ∧
    build l (block ++ suffix) old = some held

/-- Feasibility of a distinct output list under the literal (3,3) machine.
There is no multiplicity for a realizing stack, coordinate word, or history. -/
def Feasible (l : Nat) (block : List Nat)
    (oldAllowed suffixAllowed : List Nat → Prop) (next m : Nat)
    (output : List Nat) : Prop :=
  ∃ held, Initial l block oldAllowed suffixAllowed held ∧
    Run 3 3 held (List.range' next m) output []

/-- All-length transfer on actual feasible output lists. -/
theorem feasible_forward {l a next m : Nat}
    {oldAllowed suffixAllowed : List Nat → Prop} {output : List Nat}
    (small : ∀ old, oldAllowed old → ∀ x ∈ old, x < l)
    (fresh : l+a < next)
    (h : Feasible l (0 :: List.replicate a 1) oldAllowed suffixAllowed next m output) :
    Feasible l (List.replicate (a+1) 0) oldAllowed suffixAllowed next m
      (output.map (rho l a)) := by
  obtain ⟨held, ⟨old, suffix, ho, hs, hb⟩, hr⟩ := h
  refine ⟨held.map (rho l a), ⟨old, suffix, ho, hs, ?_⟩, ?_⟩
  · rw [← suffix_identity (small old ho), hb]
    rfl
  · simpa only [future_fixed fresh, List.map_nil] using hr.map (rho l a)

/-- The inverse uses the same old order and suffix witnesses. -/
theorem feasible_backward {l a next m : Nat}
    {oldAllowed suffixAllowed : List Nat → Prop} {output : List Nat}
    (small : ∀ old, oldAllowed old → ∀ x ∈ old, x < l)
    (fresh : l+a < next)
    (h : Feasible l (List.replicate (a+1) 0) oldAllowed suffixAllowed next m output) :
    Feasible l (0 :: List.replicate a 1) oldAllowed suffixAllowed next m
      (output.map (rhoInv l a)) := by
  obtain ⟨held, ⟨old, suffix, ho, hs, hb⟩, hr⟩ := h
  refine ⟨held.map (rhoInv l a), ⟨old, suffix, ho, hs, ?_⟩, ?_⟩
  · rw [← suffix_inverse (small old ho), hb]
    rfl
  · simpa only [future_inverse_fixed fresh, List.map_nil] using hr.map (rhoInv l a)

theorem feasible_iff {l a next m : Nat}
    {oldAllowed suffixAllowed : List Nat → Prop} (output : List Nat)
    (small : ∀ old, oldAllowed old → ∀ x ∈ old, x < l)
    (fresh : l+a < next) :
    Feasible l (0 :: List.replicate a 1) oldAllowed suffixAllowed next m output ↔
      Feasible l (List.replicate (a+1) 0) oldAllowed suffixAllowed next m
        (output.map (rho l a)) := by
  constructor
  · exact feasible_forward small fresh
  · intro h
    simpa only [map_rhoInv_rho] using feasible_backward small fresh h

/-- A two-sided explicit bijection, without a finiteness or cardinality premise. -/
structure OutputBijection (source target : Type) where
  forward : source → target
  backward : target → source
  left_inverse : ∀ x, backward (forward x) = x
  right_inverse : ∀ y, forward (backward y) = y

/-- Genuine bijection of distinct complete outputs for every future length.
The subtype holds only the output list and its feasibility proposition;
realizing histories and choices of initial stacks are not counted. -/
def distinctOutputBijection (l a next m : Nat)
    (oldAllowed suffixAllowed : List Nat → Prop)
    (small : ∀ old, oldAllowed old → ∀ x ∈ old, x < l)
    (fresh : l+a < next) :
    OutputBijection
      {output // Feasible l (0 :: List.replicate a 1) oldAllowed suffixAllowed next m output}
      {output // Feasible l (List.replicate (a+1) 0) oldAllowed suffixAllowed next m output} where
  forward output := ⟨output.val.map (rho l a), feasible_forward small fresh output.property⟩
  backward output := ⟨output.val.map (rhoInv l a), feasible_backward small fresh output.property⟩
  left_inverse output := by apply Subtype.ext; exact map_rhoInv_rho l a output.val
  right_inverse output := by apply Subtype.ext; exact map_rho_rhoInv l a output.val


/-- Every decoded earlier supplies precisely earlier labels; callers need no
separate hypothesis about its physical orders. -/
theorem decoded_prefix_small {earlier old : List Nat} (h : Decodes earlier old) :
    ∀ x ∈ old, x < earlier.length+1 := by
  intro x hx
  have hm := h.permutation.mem_iff.mp hx
  have hb := List.mem_range'_1.mp hm
  omega

/-- The literal complete-word identity with an arbitrary preceding coordinate
word. Both earlier and suffix rejection are included in the equation. -/
theorem whole_word_identity (earlier suffix : List Nat) (a : Nat) :
    (build 1 (earlier ++ (0 :: List.replicate a 1) ++ suffix) []).map
        (List.map (rho (earlier.length+1) a)) =
      build 1 (earlier ++ List.replicate (a+1) 0 ++ suffix) [] := by
  rw [List.append_assoc, List.append_assoc, build_append, build_append]
  cases hp : build 1 earlier [] with
  | none => rfl
  | some old =>
    change (build (1+earlier.length) ((0 :: List.replicate a 1) ++ suffix) old).map
      (List.map (rho (earlier.length+1) a)) =
        build (1+earlier.length) (List.replicate (a+1) 0 ++ suffix) old
    have small := decoded_prefix_small (show Decodes earlier old from hp)
    simpa only [Nat.add_comm 1 earlier.length] using suffix_identity small

/-- Physical orders represented by any allowed earlier of the required length.
The label of the first block coordinate is l, so the earlier has l-1 labels. -/
def PrefixOrders (l : Nat) (prefixAllowed : List Nat → Prop) (old : List Nat) : Prop :=
  ∃ earlier, prefixAllowed earlier ∧ earlier.length+1 = l ∧ Decodes earlier old

theorem prefixOrders_small {l : Nat} {prefixAllowed : List Nat → Prop} :
    ∀ old, PrefixOrders l prefixAllowed old → ∀ x ∈ old, x < l := by
  rintro old ⟨earlier, _, hlen, hp⟩ x hx
  have hb := decoded_prefix_small hp x hx
  omega

/-- The feasibility subtypes in the coordinate specialization really consist
of permutations of the complete old-and-future label supply. -/
theorem coordinate_feasible_permutation {l a w m : Nat} {block output : List Nat}
    {prefixAllowed suffixAllowed : List Nat → Prop}
    (blockLength : block.length = a+1)
    (h : Feasible l block (PrefixOrders l prefixAllowed)
      (fun suffix => suffixAllowed suffix ∧ suffix.length = w) (l+a+w+1) m output) :
    output.Perm (List.range' 1 (l+a+w+m)) := by
  obtain ⟨held, ⟨old, suffix, ⟨earlier, _, hlen, hp⟩, ⟨_, hs⟩, hb⟩, hr⟩ := h
  have hfull : Decodes (earlier ++ block ++ suffix) held := by
    unfold Decodes
    rw [List.append_assoc, build_append, hp]
    change build (1+earlier.length) (block ++ suffix) old = some held
    have he : 1+earlier.length = l := by omega
    simpa only [he] using hb
  have total : (earlier ++ block ++ suffix).length = l+a+w := by
    simp only [List.length_append]
    omega
  have hpheld : held.Perm (List.range' 1 (l+a+w)) := by
    simpa only [total] using hfull.permutation
  have hop : output.Perm (held ++ List.range' (l+a+w+1) m) := by
    simpa using hr.supply.symm
  have result := hop.trans (hpheld.append_right (List.range' (l+a+w+1) m))
  have join : List.range' 1 (l+a+w) ++ List.range' (l+a+w+1) m =
      List.range' 1 (l+a+w+m) := by
    simpa only [Nat.add_comm 1 (l+a+w)] using
      (List.range'_append_1 (s := 1) (m := l+a+w) (n := m))
  simpa only [join] using result

/-- Specialization to actual coordinate-earlier families and fixed suffix
length. The future input begins at the next unused label, l+a+w+1, and m is
arbitrary. Allowed earlier and suffix words retain all correlations. -/
def coordinateOutputBijection (l a w m : Nat)
    (prefixAllowed suffixAllowed : List Nat → Prop) :
    OutputBijection
      {output // Feasible l (0 :: List.replicate a 1)
        (PrefixOrders l prefixAllowed) (fun suffix => suffixAllowed suffix ∧ suffix.length = w)
        (l+a+w+1) m output}
      {output // Feasible l (List.replicate (a+1) 0)
        (PrefixOrders l prefixAllowed) (fun suffix => suffixAllowed suffix ∧ suffix.length = w)
        (l+a+w+1) m output} :=
  distinctOutputBijection l a (l+a+w+1) m _ _ prefixOrders_small (by omega)

#print axioms rhoInv_rho
#print axioms rho_rhoInv
#print axioms block_identity
#print axioms suffix_identity
#print axioms suffix_inverse
#print axioms feasible_iff
#print axioms distinctOutputBijection
#print axioms whole_word_identity
#print axioms coordinateOutputBijection
#print axioms coordinate_feasible_permutation

end ORun
end Coordinates
end StackSorting.Generalized
