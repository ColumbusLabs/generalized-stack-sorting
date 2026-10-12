import InfiniteFamily
import RangeLazyInversion
import RankBlockTransitions

namespace StackSorting.Generalized

/-- Unrestricted deletion of a block minimum leaves another interval block;
this direction needs no assumption that the pop width reaches every token. -/
theorem SegmentOrder.minimum_closed {base top s : Nat} {xs ys : List Nat}
    (h : SegmentOrder base top xs) (hp : Step 2 s xs [] [base] ys)
    (hne : base < top) : SegmentOrder (base+1) top ys := by
  obtain ⟨u, high, hu, hut, hh, _, rfl⟩ :=
    (SegmentOrder.minimum_image_union hne).mp ⟨xs, h, hp⟩
  have hd := SegmentOrder.descending (base+1) (u-base-1)
  have he : base+1+(u-base-1) = u := by omega
  rw [he] at hd
  exact hh.append hd

/-- Drain a prescribed initial interval of held minima. No new read can hide
between these outputs because all of them precede the next unread value. -/
theorem RangeLazyRun.drainMinima {s limit next base top : Nat}
    (k : Nat) (high tail out : List Nat)
    (hs : SegmentOrder base top high) (hb : base+k ≤ top) (ht : top ≤ next)
    (fresh : ∀ a, base ≤ a → a < top → a ∉ tail)
    (h : RangeLazyRun 2 s limit next (high ++ tail) (List.range' base k ++ out)) :
    ∃ after, SegmentOrder (base+k) top after ∧
      RangeLazyRun 2 s limit next (after ++ tail) out := by
  induction k generalizing base high with
  | zero => exact ⟨high, by simpa using hs, by simpa using h⟩
  | succ k ih =>
    have hnon : base < top := by omega
    have hc : RangeLazyRun 2 s limit next (high ++ tail)
        (base :: (List.range' (base+1) k ++ out)) := by
      simpa [List.range'_succ] using h
    rcases hc.cons_cases with ⟨after, pop, rest⟩ | ⟨before, after, lower, upper, absent, read, pop, rest⟩
    ·
      obtain ⟨ys, hp, he⟩ := pop.pop_suffix (fresh base (Nat.le_refl _) hnon)
      rw [he] at rest
      have hy := hs.minimum_closed hp hnon
      obtain ⟨after, ha, hr⟩ := ih ys hy (by omega)
        (fun a h₁ h₂ => fresh a (by omega) h₂) rest
      exact ⟨after, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha, hr⟩
    · omega

namespace BasisFamily

/-- All original histories of the intact initial prefix reach the same
physical two-token stack, rather than merely an abstract candidate state. -/
theorem initial_prefix {s limit : Nat} (hs : 3 ≤ s) (rest : List Nat)
    (h : RangeLazyRun 2 s limit 0 []
      ([s+1,0] ++ List.range' 2 (s-2) ++ rest)) :
    RangeLazyRun 2 s limit (s+2) [s,1] rest := by
  have hfirst : RangeLazyRun 2 s limit 0 []
      ((s+1) :: 0 :: (List.range' 2 (s-2) ++ rest)) := by simpa using h
  cases hfirst with
  | held pop tail => have hz := pop.pop_mem; simp at hz
  | @record _ _ _ before after _ lower upper absent read pop tail =>
    have hread : Run 2 s [] (List.range (s+2)) [] before := by
      simpa [List.range_eq_range', Nat.add_assoc] using read
    have horder : SegmentOrder 0 (s+2) before :=
      (segmentOrder_zero _ _).mpr ((intervalOrder_iff_history _ _ _).mpr hread)
    have hafter : SegmentOrder 0 (s+1) after :=
      (SegmentOrder.maximum_image (by omega) (by omega)).mp ⟨before, horder, pop⟩
    have htail : RangeLazyRun 2 s limit (s+2) after
        (0 :: (List.range' 2 (s-2) ++ rest)) := by
      simpa [Nat.add_assoc] using tail
    cases htail with
    | held pop₀ tail₀ =>
      obtain ⟨high, hh, he⟩ :=
        (SegmentOrder.minimum_image_one_blocker (base := 0) (s := s) (by omega)).mp
          ⟨after, by simpa using hafter, pop₀⟩
      rw [he] at tail₀
      have hh' : SegmentOrder 2 (s+1) high := by simpa using hh
      obtain ⟨last, hl, hr⟩ := RangeLazyRun.drainMinima (s-2) high [1] rest hh'
        (by omega) (by omega) (by intro a ha hb; simp; omega) tail₀
      have hl' : SegmentOrder s (s+1) last := by
        have he' : 2+(s-2) = s := by omega
        simpa [he'] using hl
      have hp := hl'.perm_range
      have he' : last = [s] := by simpa [List.range'_succ] using hp
      simpa [he'] using hr
    | record lower upper absent read pop rest => omega

#print axioms initial_prefix
end BasisFamily
end StackSorting.Generalized
