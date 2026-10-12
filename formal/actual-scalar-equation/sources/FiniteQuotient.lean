import FiniteMatrix

namespace StackSorting.FiniteGraph
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem vm_row_add {m n} (v w : Vec R m) (A : Mat R m n) :
    vm (fun i => v i+w i) A = fun j => vm v A j+vm w A j := by
  funext j
  unfold vm
  rw [←sumFin_add]
  apply sumFin_congr
  intro i
  grind

theorem vm_row_neg {m n} (v : Vec R m) (A : Mat R m n) :
    vm (fun i => -v i) A = fun j => -vm v A j := by
  funext j
  unfold vm
  rw [←sumFin_neg]
  apply sumFin_congr
  intro i
  grind

def step19 (M : Letter → Mat R 6 6) (N : Letter → Mat R 19 19)
    (C : Letter → Mat R 6 19) (a : Letter) (row : Vec R 6 × Vec R 19) :
    Vec R 6 × Vec R 19 :=
  (vm row.1 (M a), fun j => -vm row.1 (C a) j+vm row.2 (N a) j)

def run19 (M : Letter → Mat R 6 6) (N : Letter → Mat R 19 19)
    (C : Letter → Mat R 6 19) : List Letter → (Vec R 6 × Vec R 19) → (Vec R 6 × Vec R 19)
  | [], r => r
  | a::w, r => run19 M N C w (step19 M N C a r)

def project (S : Mat R 19 9) (row : Vec R 6 × Vec R 19) : Vec R 6 × Vec R 9 :=
  (row.1, vm row.2 S)

def terminal19 (kappa : Vec R 6) (nu : Vec R 19) (row : Vec R 6 × Vec R 19) : R :=
  dot row.1 kappa+dot row.2 nu

theorem quotient_step (M : Letter → Mat R 6 6) (N19 : Letter → Mat R 19 19)
    (C19 : Letter → Mat R 6 19) (N9 : Letter → Mat R 9 9) (CS : Letter → Mat R 6 9)
    (S : Mat R 19 9) (hn : ∀ a, mm (N19 a) S=mm S (N9 a))
    (hc : ∀ a, mm (C19 a) S=CS a) (a : Letter) (row : Vec R 6 × Vec R 19) :
    project S (step19 M N19 C19 a row)=step M N9 CS a (project S row) := by
  apply Prod.ext
  · rfl
  · change vm (fun j => -vm row.1 (C19 a) j+vm row.2 (N19 a) j) S =
      (fun j => -vm row.1 (CS a) j+vm (vm row.2 S) (N9 a) j)
    rw [vm_row_add, vm_row_neg, vm_mm, vm_mm, hc a, hn a, vm_mm]

theorem quotient_run (M : Letter → Mat R 6 6) (N19 : Letter → Mat R 19 19)
    (C19 : Letter → Mat R 6 19) (N9 : Letter → Mat R 9 9) (CS : Letter → Mat R 6 9)
    (S : Mat R 19 9) (hn : ∀ a, mm (N19 a) S=mm S (N9 a))
    (hc : ∀ a, mm (C19 a) S=CS a) (w : List Letter) (row : Vec R 6 × Vec R 19) :
    project S (run19 M N19 C19 w row)=run M N9 CS w (project S row) := by
  induction w generalizing row with
  | nil => rfl
  | cons a w ih =>
    simp only [run19, run, ih, quotient_step M N19 C19 N9 CS S hn hc]

theorem quotient_output (S : Mat R 19 9) (kappa : Vec R 6)
    (nu19 : Vec R 19) (nu9 : Vec R 9) (hn : mv S nu9=nu19)
    (row : Vec R 6 × Vec R 19) :
    terminal19 kappa nu19 row=terminal kappa nu9 (project S row) := by
  change dot row.1 kappa+dot row.2 nu19=dot row.1 kappa+dot (vm row.2 S) nu9
  rw [dot_vm, hn]

#print axioms quotient_run
#print axioms quotient_output
end StackSorting.FiniteGraph
