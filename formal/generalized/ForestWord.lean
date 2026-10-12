import Std

/-!
# Exact operation-labelled forest/word quotient

This file checks only the forest-to-word bridge. It does not assume or prove
that these paths are in bijection with sortable permutations, or any generating
function identity. Operations remain labelled, including coincident P0/P1 edges.
-/
namespace StackSorting

inductive Forest where
  | nil : Forest
  | cons (children rest : Forest) : Forest
  deriving DecidableEq, Repr

inductive Mark where
  | L | R
  deriving DecidableEq, Repr

inductive Op where
  | bypass | push0 | push1 | pop0 | pop1
  deriving DecidableEq, Repr

open Forest Mark Op

def append : Forest → Forest → Forest
  | nil, g => g
  | cons c r, g => cons c (append r g)

def rootMark : Forest → Mark
  | nil => L
  | cons _ _ => R

def word : Forest → List Mark
  | nil => []
  | cons c r => rootMark c :: (word c ++ word r)

theorem word_append (f g : Forest) : word (append f g) = word f ++ word g := by
  induction f with
  | nil => rfl
  | cons c r _ ihr => simp [append, word, ihr, List.append_assoc]

abbrev FState := Forest × Bool
abbrev WState := List Mark × Bool

def project (s : FState) : WState := (word s.1, s.2)

def forestStep (op : Op) : FState → Option FState
  | (f, canPop) => match op, f with
    | bypass, _ => some (f, true)
    | push0, nil => some (cons nil nil, false)
    | push0, cons c r => some (cons (cons c nil) r, false)
    | push1, nil => none
    | push1, cons c r => some (cons (cons nil c) r, false)
    | pop0, nil => none
    | pop0, cons c r => if canPop then some (append c r, true) else none
    | pop1, cons nil (cons c r) =>
        if canPop then some (cons nil (append c r), true) else none
    | pop1, _ => none

def wordStep (op : Op) : WState → Option WState
  | (w, canPop) => match op, w with
    | bypass, _ => some (w, true)
    | push0, [] => some ([L], false)
    | push0, _ :: _ => some (R :: w, false)
    | push1, [] => none
    | push1, _ :: v => some (R :: L :: v, false)
    | pop0, [] => none
    | pop0, _ :: v => if canPop then some (v, true) else none
    | pop1, L :: _ :: v => if canPop then some (L :: v, true) else none
    | pop1, _ => none

/-- Exact one-step simulation and reflection, for every forest and flag. -/
theorem project_step (op : Op) (s : FState) :
    Option.map project (forestStep op s) = wordStep op (project s) := by
  rcases s with ⟨f, b⟩
  cases op <;> cases f with
  | nil => simp [forestStep, wordStep, project, word, rootMark]
  | cons c r =>
    cases c <;> cases r <;> cases b <;>
      simp [forestStep, wordStep, project, word, rootMark, word_append,
        List.append_assoc]

def forestRun : List Op → FState → Option FState
  | [], s => some s
  | op :: ops, s => (forestStep op s).bind (forestRun ops)

def wordRun : List Op → WState → Option WState
  | [], s => some s
  | op :: ops, s => (wordStep op s).bind (wordRun ops)

/-- Projection commutes with execution of every finite operation word. -/
theorem project_run (ops : List Op) (s : FState) :
    Option.map project (forestRun ops s) = wordRun ops (project s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    have hs := project_step op s
    cases h : forestStep op s with
    | none => simp [h] at hs; simp [forestRun, wordRun, h, ← hs]
    | some t =>
      simp [h] at hs
      simp [forestRun, wordRun, h, ← hs, ih]

/-- Every word execution from the projection of a forest lifts to a forest
execution with precisely the same labelled operations. -/
theorem lift_run (ops : List Op) (s : FState) (t : WState)
    (h : wordRun ops (project s) = some t) :
    ∃ u : FState, forestRun ops s = some u ∧ project u = t := by
  have hp := project_run ops s
  cases hf : forestRun ops s with
  | none => simp [hf, h] at hp
  | some u =>
    refine ⟨u, rfl, ?_⟩
    simpa [hf, h] using hp

/-- The lift is unique: no two final forest states realize the same execution. -/
theorem lift_unique (ops : List Op) (s u v : FState)
    (hu : forestRun ops s = some u) (hv : forestRun ops s = some v) : u = v := by
  have h : some u = some v := hu.symm.trans hv
  exact Option.some.inj h

theorem word_empty_iff (f : Forest) : word f = [] ↔ f = nil := by
  cases f <;> simp [word]

def ForestAccepts (ops : List Op) : Prop :=
  ∃ b, forestRun ops (nil, true) = some (nil, b)

def WordAccepts (ops : List Op) : Prop :=
  ∃ b, wordRun ops ([], true) = some ([], b)

/-- Exact equality of the two complete operation languages, at all lengths. -/
theorem accepts_iff (ops : List Op) : ForestAccepts ops ↔ WordAccepts ops := by
  constructor
  · rintro ⟨b, h⟩
    refine ⟨b, ?_⟩
    have hp := project_run ops (nil, true)
    simpa [h, project, word] using hp.symm
  · rintro ⟨b, h⟩
    have hw : wordRun ops (project (nil, true)) = some ([], b) := by
      simpa [project, word] using h
    obtain ⟨⟨f, c⟩, hf, hp⟩ := lift_run ops (nil, true) ([], b) hw
    have he : word f = [] := congrArg Prod.fst hp
    have hnil : f = nil := (word_empty_iff f).mp he
    exact ⟨c, by simpa [hnil] using hf⟩

#print axioms project_step
#print axioms project_run
#print axioms lift_run
#print axioms lift_unique
#print axioms accepts_iff

end StackSorting
