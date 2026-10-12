import CauchyRing

namespace StackSorting.FiniteGraph
open StackSorting.CauchyRing
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev Vec (R : Type) (n : Nat) := Fin n → R
abbrev Mat (R : Type) (m n : Nat) := Fin m → Fin n → R

def sumFin {R : Type} [Zero R] [Add R] : {n : Nat} → Vec R n → R
  | 0, _ => 0
  | n+1, f => sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n)

variable {R : Type} [Lean.Grind.CommRing R]

theorem sumFin_congr {n} (f g : Vec R n) (h : ∀ i, f i = g i) : sumFin f = sumFin g := by
  congr 1
  exact funext h

theorem sumFin_zero (n) : sumFin (fun _ : Fin n => (0:R)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumFin, ih]; grind

theorem sumFin_add {n} (f g : Vec R n) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  induction n with
  | zero => simp only [sumFin]; grind
  | succ n ih => simp only [sumFin, ih]; grind

theorem sumFin_mul {n} (f : Vec R n) (a : R) :
    sumFin (fun i => f i*a) = sumFin f*a := by
  induction n with
  | zero => simp only [sumFin]; grind
  | succ n ih => simp only [sumFin, ih]; grind

theorem mul_sumFin {n} (a : R) (f : Vec R n) :
    sumFin (fun i => a*f i) = a*sumFin f := by
  have h : (fun i => a*f i) = (fun i => f i*a) := by funext i; grind
  rw [h, sumFin_mul]
  grind

theorem sumFin_neg {n} (f : Vec R n) :
    sumFin (fun i => -f i) = -sumFin f := by
  have h : (fun i => -f i) = (fun i => f i*(-1)) := by funext i; grind
  rw [h, sumFin_mul]
  grind

theorem sumFin_swap {m n} (f : Fin m → Fin n → R) :
    sumFin (fun i => sumFin (f i)) = sumFin (fun j => sumFin (fun i => f i j)) := by
  induction m with
  | zero => simp only [sumFin, sumFin_zero]
  | succ m ih =>
    simp only [sumFin]
    rw [ih, ←sumFin_add]

def mm {m n p} (A : Mat R m n) (B : Mat R n p) : Mat R m p :=
  fun i j => sumFin (fun k => A i k*B k j)
def vm {m n} (v : Vec R m) (A : Mat R m n) : Vec R n :=
  fun j => sumFin (fun i => v i*A i j)
def mv {m n} (A : Mat R m n) (v : Vec R n) : Vec R m :=
  fun i => sumFin (fun j => A i j*v j)
def dot {n} (v w : Vec R n) : R := sumFin (fun i => v i*w i)

theorem vm_mm {m n p} (v : Vec R m) (A : Mat R m n) (B : Mat R n p) :
    vm (vm v A) B = vm v (mm A B) := by
  funext j
  unfold vm mm
  simp only [←sumFin_mul, ←mul_sumFin]
  rw [sumFin_swap]
  apply sumFin_congr
  intro i
  apply sumFin_congr
  intro k
  grind

theorem dot_vm {m n} (v : Vec R m) (A : Mat R m n) (w : Vec R n) :
    dot (vm v A) w = dot v (mv A w) := by
  unfold dot vm mv
  simp only [←sumFin_mul, ←mul_sumFin]
  rw [sumFin_swap]
  apply sumFin_congr
  intro i
  apply sumFin_congr
  intro k
  grind

theorem vm_add {m n} (v : Vec R m) (A B : Mat R m n) :
    vm v (fun i j => A i j+B i j) = fun j => vm v A j+vm v B j := by
  funext j
  unfold vm
  rw [←sumFin_add]
  apply sumFin_congr
  intro i
  grind

theorem vm_sub {m n} (v : Vec R m) (A B : Mat R m n) :
    vm v (fun i j => A i j-B i j) = fun j => vm v A j-vm v B j := by
  funext j
  unfold vm
  have h : (fun i => v i*(A i j-B i j)) =
      (fun i => v i*A i j + -(v i*B i j)) := by funext i; grind
  rw [h, sumFin_add, sumFin_neg]
  grind

theorem dot_add {n} (v w z : Vec R n) :
    dot v (fun i => w i+z i) = dot v w+dot v z := by
  unfold dot
  rw [←sumFin_add]
  apply sumFin_congr
  intro i
  grind

theorem dot_zero {n} (v : Vec R n) : dot v (fun _ => 0) = 0 := by
  unfold dot
  have h : (fun i => v i*(0:R)) = (fun _ => (0:R)) := by funext i; grind
  rw [h, sumFin_zero]

inductive Letter where | z | b | t deriving DecidableEq, Repr

/-- The literal residual action is the block matrix [[M,-CS],[0,N9]]. -/
def step (M : Letter → Mat R 6 6) (N : Letter → Mat R 9 9)
    (CS : Letter → Mat R 6 9) (a : Letter) (row : Vec R 6 × Vec R 9) :
    Vec R 6 × Vec R 9 :=
  (vm row.1 (M a), fun j => -vm row.1 (CS a) j+vm row.2 (N a) j)

def run (M : Letter → Mat R 6 6) (N : Letter → Mat R 9 9)
    (CS : Letter → Mat R 6 9) : List Letter → (Vec R 6 × Vec R 9) → (Vec R 6 × Vec R 9)
  | [], r => r
  | a::w, r => run M N CS w (step M N CS a r)

def graph (H : Mat R 6 9) (v : Vec R 6) : Vec R 6 × Vec R 9 := (v, vm v H)
def terminal (kappa : Vec R 6) (nu : Vec R 9) (row : Vec R 6 × Vec R 9) : R :=
  dot row.1 kappa+dot row.2 nu

theorem graph_step (M : Letter → Mat R 6 6) (N : Letter → Mat R 9 9)
    (CS : Letter → Mat R 6 9) (H : Mat R 6 9)
    (ident : ∀ a, mm (M a) H = fun i j => mm H (N a) i j-CS a i j)
    (a : Letter) (v : Vec R 6) :
    step M N CS a (graph H v) = graph H (vm v (M a)) := by
  apply Prod.ext
  · rfl
  · change (fun j => -vm v (CS a) j+vm (vm v H) (N a) j) = vm (vm v (M a)) H
    rw [vm_mm, vm_mm, ident a, vm_sub]
    funext j
    grind

theorem graph_annihilates (H : Mat R 6 9) (kappa : Vec R 6) (nu : Vec R 9)
    (ident : ∀ i, kappa i+mv H nu i=0) (v : Vec R 6) :
    terminal kappa nu (graph H v)=0 := by
  change dot v kappa+dot (vm v H) nu=0
  rw [dot_vm, ←dot_add]
  have hz : (fun i => kappa i+mv H nu i) = (fun _ => 0) := funext ident
  rw [hz, dot_zero]

theorem allwordzero (M : Letter → Mat R 6 6) (N : Letter → Mat R 9 9)
    (CS : Letter → Mat R 6 9) (H : Mat R 6 9) (kappa : Vec R 6) (nu : Vec R 9)
    (htrans : ∀ a, mm (M a) H = fun i j => mm H (N a) i j-CS a i j)
    (hterm : ∀ i, kappa i+mv H nu i=0) (w : List Letter) (v : Vec R 6) :
    terminal kappa nu (run M N CS w (graph H v))=0 := by
  induction w generalizing v with
  | nil => exact graph_annihilates H kappa nu hterm v
  | cons a w ih =>
    simp only [run, graph_step M N CS H htrans]
    exact ih _

#print axioms allwordzero
end StackSorting.FiniteGraph
