import UnequalCasesA

/-! Deletion cases with a special initial arrangement: §5.2 (a low value),
§5.3 (an extra value or an initial relay) and §5.4 (an initial record). -/
namespace StackSorting.Generalized
namespace Unequal
open BasisFamily (delete)

variable {r s m : Nat}

theorem length_delete_range'_mem {d a c : Nat} (h₁ : a ≤ d) (h₂ : d < a + c) :
    (delete d (List.range' a c)).length = c - 1 := by
  induction c with
  | zero => omega
  | succ c ih =>
    rw [List.range'_concat, delete_append, List.length_append]
    simp only [Nat.one_mul]
    by_cases hd : d < a + c
    · rw [ih hd]
      have : a + c ≠ d := by omega
      simp [delete, this] <;> omega
    · have he : a + c = d := by omega
      rw [delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega), he]
      simp [delete]

theorem perm_of_cover {n : Nat} {l : List Nat} (hl : l.length = n)
    (hm : ∀ x, x < n → x ∈ l) : l.Perm (List.range' 0 n) := by
  rw [← List.range_eq_range']
  exact perm_range_of_mem n l hl hm

/-- §5.2: deleting a low value `t < r-1`. The prefill puts the permanent
token first and the other lows after it; all of them stay protected. -/
theorem del_low (hr : 2 ≤ r) (hrs : r < s) {t : Nat} (ht : t < r - 1) :
    Run r s [] (delete t (List.range (2*s+r+2*m))) (delete t (family r s m)) [] := by
  have hlen := delete_family_length (m := m) (d := t) hr hrs (by omega)
  have hsplit := lowSeg_split s 0 (r-1) t (by omega) (by omega)
  simp only [Nat.sub_zero, Nat.zero_add] at hsplit
  have hW : delete t (family r s m) =
      lowSeg s 0 t ++ ((s+1+2*t) :: (lowSeg s (t+1) (r-1-t-1) ++
        (List.range' r (s-r) ++ (relaySeg r s 0 m ++
        ((2*s+r+2*m-1) :: (r-1) :: (delete t (lateSeg r s m) ++ delete t (termSeg r s m))))))) := by
    rw [family_segments, hsplit]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [delete_append, delete_eq_self (lowSeg_ne (fun i _ hi => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_self, delete_append,
      delete_eq_self (lowSeg_ne (fun i hi _ => ⟨by omega, by omega⟩)),
      delete_append, delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append, delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append]
  have hnd := delete_nodup (d := t) (family_nodup r s m hr hrs)
  rw [hW] at hnd hlen ⊢
  have hpre : (((r-1) :: delete t (List.range' 0 (r-1))) ++ []).Perm
      (delete t (List.range' 0 r)) := by
    have he : delete t (List.range' 0 r) = delete t (List.range' 0 (r-1)) ++ [r-1] := by
      have h := delete_range'_succ t (r-1)
      rw [show r - 1 + 1 = r by omega] at h
      rw [h]
      have hne : ¬ (r - 1 = t) := by omega
      simp [hne]
    rw [he, List.append_nil]
    exact (List.perm_append_singleton (r-1) _).symm
  have hplen : ((r-1) :: delete t (List.range' 0 (r-1))).length ≤ r - 1 := by
    rw [List.length_cons, length_delete_range', readCount_lt (by omega)]
    omega
  have h₀ : Prog r s t r [] _ (fun x => x < r ∧ x ≠ t) :=
    Prog.start _ [] _ hnd (by rw [readCount_lt (by omega)]; omega) hpre hplen
      (fun x hx => by
        by_cases hx' : x = r - 1
        · simp [hx']
        · exact List.mem_cons_of_mem _ (mem_delete_range'.mpr ⟨by omega, hx.2⟩))
  obtain ⟨n₁, h₁, hz₁, hp₁⟩ := Prog.lowAll (by omega) (by omega) (by omega) 0 t h₀
    (by omega) (fun i _ hi => ⟨⟨by omega, by omega⟩, by omega, by omega, by omega⟩)
  have hn₁ : n₁ ≤ s+1+2*t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [hz₁ h0]; omega
    · rw [hp₁ h0]; omega
  have h₂ := Prog.record (by omega) (by omega) h₁ hn₁ (by omega)
  rw [show s+1+2*t+1 = s+2+2*t by omega] at h₂
  obtain ⟨n₃, h₃, hz₃, hp₃⟩ := Prog.lowAll (by omega) (by omega) (by omega)
    (t+1) (r-1-t-1) h₂ (by omega)
    (fun i h₁ h₂ => ⟨⟨by omega, by omega⟩, by omega, by omega, by omega⟩)
  have hn₃ : n₃ = s+2*r-2 := by
    rcases Nat.eq_zero_or_pos (r-1-t-1) with h0 | h0
    · rw [hz₃ h0]; omega
    · rw [hp₃ h0]; omega
  rw [hn₃] at h₃
  have h₄ := Prog.drain (by omega) (List.range' r (s-r)) h₃
    (fun y hy => by rw [List.mem_range'] at hy; omega)
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)
  obtain ⟨n₅, h₅, hz₅, hp₅⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 m h₄
    (by omega)
    (fun j _ hj => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₅ : n₅ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [hz₅ h0]; omega
    · rw [hp₅ h0]; omega
  have hlate := length_delete_le (d := t) (l := lateSeg r s m)
  have hterm := length_delete_le (d := t) (l := termSeg r s m)
  rw [length_lateSeg] at hlate
  rw [length_termSeg] at hterm
  simp only [List.length_append, List.length_cons, length_lowSeg, length_relaySeg,
    List.length_range'] at hlen
  have h₆ := tail_std hr hrs (by simpa using h₅) hn₅ (by omega) (by omega)
    (Or.inl (by exact ⟨by omega, by omega⟩))
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₇ := Prog.finish h₆ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg] <;> omega)
  simpa [List.range_eq_range', List.append_assoc] using h₇

theorem lowSeg_split_last (s r : Nat) (hr : 2 ≤ r) :
    lowSeg s 0 (r-1) = lowSeg s 0 (r-2) ++ [s+1+2*(r-2), r-2] := by
  have h := lowSeg_append s 0 (r-2) 1
  rw [show r - 2 + 1 = r - 1 by omega] at h
  rw [← h]
  simp [lowSeg]

/-- §5.3 prefix: the permanent token first, then lows `0..r-3`, with the bottom
low `r-2` popped once the stack holds exactly `s` tokens. -/
theorem ex_prefix (hr : 2 ≤ r) (hrs : r < s) {d : Nat} (hd₁ : r ≤ d)
    (hd₂ : d < s+2*r-2) (hodd : ∀ i, d ≠ s+1+2*i) (rem : List Nat)
    (hnd : (lowSeg s 0 (r-2) ++ ((s+1+2*(r-2)) :: (r-2) :: rem)).Nodup) :
    Prog r s d (s+2*r-2) (lowSeg s 0 (r-2) ++ [s+1+2*(r-2)] ++ [r-2]) rem
      (fun x => x < r ∧ x ≠ r - 2) := by
  have hpre : (((r-1) :: List.range' 0 (r-2)) ++ [r-2]).Perm (delete d (List.range' 0 r)) := by
    rw [delete_range'_above (by omega)]
    apply perm_of_cover (by simp; omega)
    intro x hx
    by_cases h₁ : x = r - 1
    · simp [h₁]
    · by_cases h₂ : x = r - 2
      · simp [h₂]
      · simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_range']
        exact Or.inr (Or.inl ⟨x, by omega, by omega⟩)
  have h₀ : Prog r s d r [] _ (fun x => x < r ∧ x ≠ r - 2) :=
    Prog.start _ [r-2] _ hnd (by rw [readCount_ge (by omega)] <;> omega) hpre
      (by simp; omega)
      (fun x hx => by
        by_cases h₁ : x = r - 1
        · simp [h₁]
        · simp only [List.mem_cons, List.mem_range']
          exact Or.inr ⟨x, by omega, by omega⟩)
  obtain ⟨n₁, h₁, hz₁, hp₁⟩ := Prog.lowAll (by omega) (by omega) (by omega) 0 (r-2) h₀
    (by omega) (fun i _ hi => ⟨⟨by omega, by omega⟩, by omega, hodd i ∘ Eq.symm, by omega⟩)
  have hn₁ : n₁ ≤ s+1+2*(r-2) := by
    rcases Nat.eq_zero_or_pos (r-2) with h0 | h0
    · rw [hz₁ h0]; omega
    · rw [hp₁ h0]; omega
  have h₂ := Prog.record (by omega) (by omega) h₁ hn₁ (hodd (r-2) ∘ Eq.symm)
  rw [show s+1+2*(r-2)+1 = s+2*r-2 by omega] at h₂
  have h₃ := Prog.pop (by omega) h₂ (by omega) (by omega)
    (Or.inr (by rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega))
  simpa using h₃

/-- §5.3: deleting an extra value `r <= d < s`. -/
theorem del_extra (hr : 2 ≤ r) (hrs : r < s) {d : Nat} (hd₁ : r ≤ d) (hd₂ : d < s) :
    Run r s [] (delete d (List.range (2*s+r+2*m))) (delete d (family r s m)) [] := by
  have hlen := delete_family_length (m := m) (d := d) hr hrs (by omega)
  have hW : delete d (family r s m) =
      lowSeg s 0 (r-2) ++ ((s+1+2*(r-2)) :: (r-2) :: (delete d (List.range' r (s-r)) ++
        (relaySeg r s 0 m ++
        ((2*s+r+2*m-1) :: (r-1) :: (delete d (lateSeg r s m) ++ delete d (termSeg r s m)))))) := by
    rw [family_segments, lowSeg_split_last s r hr]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [delete_append, delete_eq_self (lowSeg_ne (fun i _ hi => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append,
      delete_append, delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append]
  have hnd := delete_nodup (d := d) (family_nodup r s m hr hrs)
  rw [hW] at hnd hlen ⊢
  have h₁ := ex_prefix hr hrs (d := d) hd₁ (by omega) (fun i => by omega) _ hnd
  have hX := length_delete_range'_mem (d := d) (a := r) (c := s-r) hd₁ (by omega)
  have h₂ := Prog.drain (by omega) (delete d (List.range' r (s-r))) h₁
    (fun y hy => by
      obtain ⟨hy, hyd⟩ := mem_delete.mp hy
      rw [List.mem_range'] at hy
      exact ⟨by omega, hyd⟩)
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)
  obtain ⟨n₃, h₃, hz₃, hp₃⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 m h₂
    (by omega)
    (fun j _ hj => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg, hX] <;> omega)⟩)
  have hn₃ : n₃ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [hz₃ h0]; omega
    · rw [hp₃ h0]; omega
  have hlate := length_delete_le (d := d) (l := lateSeg r s m)
  have hterm := length_delete_le (d := d) (l := termSeg r s m)
  rw [length_lateSeg] at hlate
  rw [length_termSeg] at hterm
  simp only [List.length_append, List.length_cons, length_lowSeg, length_relaySeg, hX] at hlen
  have h₄ := tail_std hr hrs (by simpa using h₃) hn₃ (by omega) (by omega)
    (Or.inl (by exact ⟨by omega, by omega⟩))
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg, hX] <;> omega)
  have h₅ := Prog.finish h₄ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg, hX] <;> omega)
  simpa [List.range_eq_range', List.append_assoc] using h₅

/-- §5.3: deleting an initial relay `E_k`, `k <= r-2`, whose output comes
after the permanent token. -/
theorem del_initRelay_late (hr : 2 ≤ r) (hrs : r < s) {k : Nat} (hk : k ≤ r - 2) (hkm : m ≤ k) :
    Run r s [] (delete (s+2*k) (List.range (2*s+r+2*m))) (delete (s+2*k) (family r s m)) [] := by
  have hlen := delete_family_length (m := m) (d := s+2*k) hr hrs (by omega)
  have hW : delete (s+2*k) (family r s m) =
      lowSeg s 0 (r-2) ++ ((s+1+2*(r-2)) :: (r-2) :: (List.range' r (s-r) ++
        (relaySeg r s 0 m ++
        ((2*s+r+2*m-1) :: (r-1) :: (delete (s+2*k) (lateSeg r s m) ++
          delete (s+2*k) (termSeg r s m)))))) := by
    rw [family_segments, lowSeg_split_last s r hr]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [delete_append, delete_eq_self (lowSeg_ne (fun i _ hi => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append,
      delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append, delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append]
  have hnd := delete_nodup (d := s+2*k) (family_nodup r s m hr hrs)
  rw [hW] at hnd hlen ⊢
  have h₁ := ex_prefix hr hrs (d := s+2*k) (by omega) (by omega) (fun i => by omega) _ hnd
  have h₂ := Prog.drain (by omega) (List.range' r (s-r)) h₁
    (fun y hy => by rw [List.mem_range'] at hy; omega)
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)
  obtain ⟨n₃, h₃, hz₃, hp₃⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 m h₂
    (by omega)
    (fun j _ hj => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₃ : n₃ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [hz₃ h0]; omega
    · rw [hp₃ h0]; omega
  have hlate := length_delete_le (d := s+2*k) (l := lateSeg r s m)
  have hterm := length_delete_le (d := s+2*k) (l := termSeg r s m)
  rw [length_lateSeg] at hlate
  rw [length_termSeg] at hterm
  simp only [List.length_append, List.length_cons, length_lowSeg, length_relaySeg,
    List.length_range'] at hlen
  have h₄ := tail_std hr hrs (by simpa using h₃) hn₃ (by omega) (by omega)
    (Or.inl (by exact ⟨by omega, by omega⟩))
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₅ := Prog.finish h₄ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg] <;> omega)
  simpa [List.range_eq_range', List.append_assoc] using h₅

/-- §5.3: deleting an initial relay `E_k`, `k <= r-2`, whose output is the
relay output of step `k < m`. -/
theorem del_initRelay_early (hr : 2 ≤ r) (hrs : r < s) {k : Nat} (hk : k ≤ r - 2) (hkm : k < m) :
    Run r s [] (delete (s+2*k) (List.range (2*s+r+2*m))) (delete (s+2*k) (family r s m)) [] := by
  have hlen := delete_family_length (m := m) (d := s+2*k) hr hrs (by omega)
  have hW : delete (s+2*k) (family r s m) =
      lowSeg s 0 (r-2) ++ ((s+1+2*(r-2)) :: (r-2) :: (List.range' r (s-r) ++
        (relaySeg r s 0 k ++ ((s+2*r-1+2*k) :: (relaySeg r s (k+1) (m-k-1) ++
        ((2*s+r+2*m-1) :: (r-1) :: (delete (s+2*k) (lateSeg r s m) ++
          delete (s+2*k) (termSeg r s m)))))))) := by
    rw [family_segments, lowSeg_split_last s r hr, relaySeg_split0 r s m k hkm]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [delete_append, delete_eq_self (lowSeg_ne (fun i _ hi => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append,
      delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append, delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_self, delete_append,
      delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append]
  have hnd := delete_nodup (d := s+2*k) (family_nodup r s m hr hrs)
  rw [hW] at hnd hlen ⊢
  have h₁ := ex_prefix hr hrs (d := s+2*k) (by omega) (by omega) (fun i => by omega) _ hnd
  have h₂ := Prog.drain (by omega) (List.range' r (s-r)) h₁
    (fun y hy => by rw [List.mem_range'] at hy; omega)
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)
  obtain ⟨n₃, h₃, hz₃, hp₃⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 k h₂
    (by omega)
    (fun j _ hj => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₃ : n₃ ≤ s+2*r-1+2*k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [hz₃ h0]; omega
    · rw [hp₃ h0]; omega
  have h₄ := Prog.record (by omega) (by omega) h₃ hn₃ (by omega)
  rw [show s+2*r-1+2*k+1 = s+2*r+2*k by omega] at h₄
  obtain ⟨n₅, h₅, hz₅, hp₅⟩ := Prog.relayAll (by omega) (by omega) (by omega)
    (k+1) (m-k-1) h₄ (by omega)
    (fun j h₁ h₂ => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)⟩)
  have hn₅ : n₅ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos (m-k-1) with h0 | h0
    · rw [hz₅ h0]; omega
    · rw [hp₅ h0]; omega
  have hlate := length_delete_le (d := s+2*k) (l := lateSeg r s m)
  have hterm := length_delete_le (d := s+2*k) (l := termSeg r s m)
  rw [length_lateSeg] at hlate
  rw [length_termSeg] at hterm
  simp only [List.length_append, List.length_cons, length_lowSeg, length_relaySeg,
    List.length_range'] at hlen
  have h₆ := tail_std hr hrs (by simpa using h₅) hn₅ (by omega) (by omega)
    (Or.inl (by exact ⟨by omega, by omega⟩))
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₇ := Prog.finish h₆ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg] <;> omega)
  simpa [List.range_eq_range', List.append_assoc] using h₇

/-- §5.4 prefix: prefill with the low `i` at the bottom, output it before the
missing record's batch, finish the low phase, and pass the extra values. -/
theorem q_prefix (hr : 2 ≤ r) (hrs : r < s) {i : Nat} (hi : i ≤ r - 2) (rem : List Nat)
    (hnd : (lowSeg s 0 i ++ (i :: (lowSeg s (i+1) (r-1-i-1) ++
      (List.range' r (s-r) ++ rem)))).Nodup) :
    ∃ nX, nX ≤ s+2*r-1 ∧ Prog r s (s+1+2*i) nX
      ([] ++ lowSeg s 0 i ++ [i] ++ lowSeg s (i+1) (r-1-i-1) ++ List.range' r (s-r))
      rem (fun x => x < r ∧ x ≠ i) := by
  have hpre : (((r-1) :: delete i (List.range' 0 (r-1))) ++ [i]).Perm
      (delete (s+1+2*i) (List.range' 0 r)) := by
    rw [delete_range'_above (d := s+1+2*i) (k := r) (by omega)]
    apply perm_of_cover
    · rw [List.length_append, List.length_cons, length_delete_range', readCount_lt (by omega)]
      simp; omega
    · intro x hx
      by_cases h₁ : x = r - 1
      · simp [h₁]
      · by_cases h₂ : x = i
        · simp [h₂]
        · simp only [List.cons_append, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl (mem_delete_range'.mpr ⟨by omega, h₂⟩))
  have hplen : ((r-1) :: delete i (List.range' 0 (r-1))).length ≤ r - 1 := by
    rw [List.length_cons, length_delete_range', readCount_lt (by omega)]
    omega
  have h₀ : Prog r s (s+1+2*i) r [] _ (fun x => x < r ∧ x ≠ i) :=
    Prog.start _ [i] _ hnd (by rw [readCount_ge (by omega)] <;> omega) hpre hplen
      (fun x hx => by
        by_cases hx' : x = r - 1
        · simp [hx']
        · exact List.mem_cons_of_mem _ (mem_delete_range'.mpr ⟨by omega, hx.2⟩))
  obtain ⟨n₁, h₁, hz₁, hp₁⟩ := Prog.lowAll (by omega) (by omega) (by omega) 0 i h₀
    (by omega) (fun j _ hj => ⟨⟨by omega, by omega⟩, by omega, by omega, by omega⟩)
  have hn₁ : (i = 0 → n₁ = r) ∧ (0 < i → n₁ = s+2*i) := by
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · rw [hz₁ h0]
    · rw [hp₁ h0]; omega
  have hn₁' : n₁ ≤ s+2*i ∨ n₁ = r := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact Or.inr (hn₁.1 h0)
    · exact Or.inl (by rw [hn₁.2 h0]; exact Nat.le_refl _)
  -- Output the bottom low `i` before the missing record's batch.
  have h₂ := Prog.pop (by omega) h₁ (by omega) (by omega)
    (Or.inr (by
      rw [readCount_ge (by omega)]
      simp [length_lowSeg]
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [hn₁.1 h0]; omega
      · rw [hn₁.2 h0]; omega))
  obtain ⟨n₃, h₃, hz₃, hp₃⟩ := Prog.lowAll (by omega) (by omega) (by omega)
    (i+1) (r-1-i-1) h₂ (by omega)
    (fun j h₁ h₂ => ⟨⟨by omega, by omega⟩, by omega, by omega, by omega⟩)
  -- The extra values: held when r >= 3, successive new maxima when r = 2.
  by_cases hr2 : r = 2
  · subst hr2
    have hi0 : i = 0 := by omega
    subst hi0
    have hn₃ : n₃ = 2 := by rw [hz₃ (by omega), hz₁ rfl]
    rw [hn₃] at h₃
    have h₄ := Prog.records (by omega) (by omega) (s-2) (a := 2) h₃
      (fun j hj => by omega)
    exact ⟨2+(s-2), by omega, h₄⟩
  · have hn₃ : s ≤ n₃ ∧ n₃ ≤ s+2*r-2 ∧ (i < r - 2 → n₃ = s+2*r-2) ∧
        (i = r - 2 → n₃ = s+2*i) := by
      rcases Nat.eq_zero_or_pos (r-1-i-1) with h0 | h0
      · have hz := hz₃ h0
        have hie : i = r - 2 := by omega
        have hi0 : 0 < i := by omega
        rw [hz, hn₁.2 hi0]
        omega
      · rw [hp₃ h0]; omega
    have h₄ := Prog.drain (by omega) (List.range' r (s-r)) h₃
      (fun y hy => by rw [List.mem_range'] at hy; omega)
      (by
        simp [length_lowSeg]
        by_cases hie : i < r - 2
        · rw [hn₃.2.2.1 hie, readCount_lt (by omega)]; omega
        · rw [hn₃.2.2.2 (by omega), readCount_ge (by omega)]; omega)
    exact ⟨n₃, by omega, h₄⟩

/-- §5.4: deleting an initial record `Q_i = s+1+2i`, `i <= r-2`. The low `i`
is put at the bottom and output, before the missing batch is read, from a
stack of at most `s` tokens. -/
theorem del_lowRecord (hr : 2 ≤ r) (hrs : r < s) {i : Nat} (hi : i ≤ r - 2) :
    Run r s [] (delete (s+1+2*i) (List.range (2*s+r+2*m)))
      (delete (s+1+2*i) (family r s m)) [] := by
  have hlen := delete_family_length (m := m) (d := s+1+2*i) hr hrs (by omega)
  have hsplit := lowSeg_split s 0 (r-1) i (by omega) (by omega)
  simp only [Nat.sub_zero, Nat.zero_add] at hsplit
  have hW : delete (s+1+2*i) (family r s m) =
      lowSeg s 0 i ++ (i :: (lowSeg s (i+1) (r-1-i-1) ++ (List.range' r (s-r) ++
        (relaySeg r s 0 m ++
        ((2*s+r+2*m-1) :: (r-1) :: (delete (s+1+2*i) (lateSeg r s m) ++
          delete (s+1+2*i) (termSeg r s m))))))) := by
    rw [family_segments, hsplit]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [delete_append, delete_eq_self (lowSeg_ne (fun j _ hj => ⟨by omega, by omega⟩)),
      delete_cons_self, delete_cons_ne _ (by omega), delete_append,
      delete_eq_self (lowSeg_ne (fun j hj _ => ⟨by omega, by omega⟩)),
      delete_append, delete_eq_self (fun x hx => by rw [List.mem_range'] at hx; omega),
      delete_append, delete_eq_self (relaySeg_ne (fun j _ _ => ⟨by omega, by omega⟩)),
      delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_append]
  have hnd := delete_nodup (d := s+1+2*i) (family_nodup r s m hr hrs)
  rw [hW] at hnd hlen ⊢
  obtain ⟨nX, hnX, h₄⟩ := q_prefix (s := s) hr hrs hi _ hnd
  obtain ⟨n₅, h₅, hz₅, hp₅⟩ := Prog.relayAll (by omega) (by omega) (by omega) 0 m h₄
    hnX
    (fun j _ hj => ⟨by omega, by omega, Or.inr (by
      rw [readCount_lt (by omega)]; simp [length_lowSeg] <;> omega)⟩)
  have hn₅ : n₅ ≤ 2*s+r+2*m-1 := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [hz₅ h0]; omega
    · rw [hp₅ h0]; omega
  have hlate := length_delete_le (d := s+1+2*i) (l := lateSeg r s m)
  have hterm := length_delete_le (d := s+1+2*i) (l := termSeg r s m)
  rw [length_lateSeg] at hlate
  rw [length_termSeg] at hterm
  simp only [List.length_append, List.length_cons, length_lowSeg, length_relaySeg,
    List.length_range'] at hlen
  have hP : r - 1 < r ∧ r - 1 ≠ i := ⟨by omega, by omega⟩
  have h₆ := tail_std hr hrs h₅ hn₅ (by omega) (by omega) (Or.inl hP)
    (by rw [readCount_lt (by omega)]; simp [length_lowSeg, length_relaySeg] <;> omega)
  have h₇ := Prog.finish h₆ (by
    rw [readCount_lt (by omega)]
    simp [length_lowSeg, length_relaySeg] <;> omega)
  rw [List.range_eq_range']
  simpa only [List.append_assoc, List.nil_append, List.singleton_append, List.cons_append]
    using h₇

#print axioms length_delete_range'_mem
#print axioms del_lowRecord
#print axioms del_initRelay_late
#print axioms del_initRelay_early
#print axioms del_extra
#print axioms del_low
end Unequal
end StackSorting.Generalized
