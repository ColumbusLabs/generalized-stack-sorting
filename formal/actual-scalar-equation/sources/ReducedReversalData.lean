import ReducedWitnessEnvironment
import ChangedPolynomials
import CoordinatePolynomials
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.FiniteGraph
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def entry_T_1_0 (env : Nat → FPS) : FPS := ((3 * (env 9) * (env 6)) + (2 * (env 9) * (env 6) * (env 2)) + ((-6) * (env 0) * (env 9) * (env 6) * (env 1)))

def entry_T_1_1 (env : Nat → FPS) : FPS := (((-3) * (env 3)) + ((3 * (env 9)^1) * (env 0)) + (3 * (env 0) * (env 3) * (env 1)))

def entry_T_1_2 (env : Nat → FPS) : FPS := ((env 3) + ((-1) * (env 0)))

def entry_T_1_4 (env : Nat → FPS) : FPS := (3 + ((-3) * (env 0) * (env 1)))

def entry_T_2_0 (env : Nat → FPS) : FPS := ((3 * (env 6) * ((env 9)^2)) + ((-6) * (env 6) * (env 2) * ((env 9)^2)) + (4 * (env 5) * (env 6) * ((env 9)^2)) + ((-18) * (env 0) * (env 6) * (env 1) * ((env 9)^2)))

def entry_T_2_1 (env : Nat → FPS) : FPS := (((-3) * (env 3)) + ((9 * (env 9)^2) * (env 0)) + ((-1) * (env 5) * (env 3)) + ((9 * (env 9)^1) * (env 0) * (env 3) * (env 1)))

def entry_T_2_2 (env : Nat → FPS) : FPS := (((-3 * (env 9)^1) * (env 0)) + ((3 * (env 9)^1) * (env 3)))

def entry_T_2_4 (env : Nat → FPS) : FPS := (3 + (env 5) + ((-9 * (env 9)^1) * (env 0) * (env 1)))

def entry_T_3_1 (env : Nat → FPS) : FPS := ((-1) * (env 3) * (env 2))

def entry_T_3_3 (env : Nat → FPS) : FPS := ((env 3) * (env 2))

def entry_T_3_4 (env : Nat → FPS) : FPS := ((1 * (env 9)^1) + (env 2))

def entry_T_3_5 (env : Nat → FPS) : FPS := ((1 * (env 9)^1) + ((-1) * (env 2)))

def entry_T_4_0 (env : Nat → FPS) : FPS := ((2 * (env 9) * (env 6) * (env 7) * (env 2)) + (3 * (env 9) * (env 3) * (env 6) * (env 1) * (env 7)) + ((-6) * (env 0) * (env 9) * (env 3) * (env 6) * (env 7) * ((env 1)^2)) + (2 * (env 9) * (env 3) * (env 6) * (env 1) * (env 7) * (env 2)))

def entry_T_4_1 (env : Nat → FPS) : FPS := (((-3) * ((env 3)^2)) + ((3 * (env 9)^1) * (env 0) * (env 3)) + (3 * (env 0) * (env 1) * ((env 3)^2)))

def entry_T_4_2 (env : Nat → FPS) : FPS := (((-1) * (env 6)) + ((env 4) * (env 6) * ((env 3)^2)) + ((-1) * (env 0) * (env 3) * (env 4) * (env 6)))

def entry_T_4_4 (env : Nat → FPS) : FPS := ((3 * (env 3)) + ((-3) * (env 0) * (env 3) * (env 1)))

def entry_T_5_0 (env : Nat → FPS) : FPS := ((env 6) * (env 7) * (env 2))

def entry_T_5_1 (env : Nat → FPS) : FPS := (((-1) * (env 9) * (env 6)) + ((-2) * (env 9) * (env 4) * (env 6) * (env 2) * ((env 3)^2)))

def entry_T_5_3 (env : Nat → FPS) : FPS := (((-1) * (env 9) * (env 6)) + (2 * (env 9) * (env 4) * (env 6) * (env 2) * ((env 3)^2)))

def entry_T_5_4 (env : Nat → FPS) : FPS := (((1 * (env 9)^1) * (env 3)) + ((env 3) * (env 2)))

def entry_T_5_5 (env : Nat → FPS) : FPS := (((1 * (env 9)^1) * (env 3)) + ((-1) * (env 3) * (env 2)))

def entry_K_0_0 (env : Nat → FPS) : FPS := ((-2) * (env 1) * (env 8))

def entry_K_0_1 (env : Nat → FPS) : FPS := (2 * (env 3) * (env 4) * (env 1) * (env 8))

def entry_K_0_4 (env : Nat → FPS) : FPS := ((-2) * (env 4) * (env 1) * (env 8))

def entry_K_3_1 (env : Nat → FPS) : FPS := (2 * (env 3) * (env 4))

def entry_K_3_3 (env : Nat → FPS) : FPS := ((-2) * (env 3) * (env 4))

def entry_K_3_4 (env : Nat → FPS) : FPS := ((-2) * (env 4))

def entry_K_3_5 (env : Nat → FPS) : FPS := (2 * (env 4))

def entry_K_4_0 (env : Nat → FPS) : FPS := ((-2) * (env 6) * (env 1))

def entry_K_4_1 (env : Nat → FPS) : FPS := ((-3) + (2 * (env 3) * (env 1)))

def entry_K_4_4 (env : Nat → FPS) : FPS := ((-2) * (env 1))

def entry_K_5_0 (env : Nat → FPS) : FPS := ((-2) * (env 6) * (env 1))

def entry_K_5_1 (env : Nat → FPS) : FPS := ((-1) + (2 * (env 3) * (env 1)))

def entry_K_5_4 (env : Nat → FPS) : FPS := ((-2) * (env 1))

def entry_direction_0_0 (env : Nat → FPS) : FPS := (((-8) * (env 2) * ((env 4)^2)) + (16 * ((env 4)^2) * ((env 2)^2)) + ((-48) * (env 0) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (24 * (env 0) * (env 1) * (env 2) * ((env 4)^2)))

def entry_direction_1_0 (env : Nat → FPS) : FPS := (((-16) * (env 0) * ((env 4)^2) * ((env 2)^2)) + ((-8) * (env 3) * (env 2) * ((env 4)^2)) + ((-4) * (env 0) * (env 2) * ((env 4)^2)) + (16 * (env 3) * ((env 4)^2) * ((env 2)^2)) + ((-48) * (env 0) * (env 3) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (24 * (env 0) * (env 3) * (env 1) * (env 2) * ((env 4)^2)))

def entry_direction_2_0 (env : Nat → FPS) : FPS := (((-24) * (env 0) * (env 2) * ((env 4)^2)) + ((-24) * (env 0) * ((env 4)^2) * ((env 2)^2)) + ((-12) * (env 3) * (env 2) * ((env 4)^2)) + (24 * (env 3) * ((env 4)^2) * ((env 2)^2)) + ((-24) * (env 0) * (env 5) * ((env 4)^2) * ((env 2)^2)) + (12 * (env 0) * (env 5) * (env 2) * ((env 4)^2)) + ((-72) * (env 0) * (env 3) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (36 * (env 0) * (env 3) * (env 1) * (env 2) * ((env 4)^2)))

def entry_direction_3_0 (env : Nat → FPS) : FPS := (((-16) * (env 0) * ((env 4)^2) * ((env 2)^2)) + ((-4) * (env 0) * (env 2) * ((env 4)^2)) + ((-2) * (env 3) * (env 2) * ((env 4)^2)) + (4 * (env 3) * ((env 4)^2) * ((env 2)^2)) + ((-24) * (env 0) * (env 3) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (12 * (env 0) * (env 3) * (env 1) * (env 2) * ((env 4)^2)))

def entry_direction_4_0 (env : Nat → FPS) : FPS := (((-16) * (env 4) * (env 1) * (env 7) * ((env 2)^2)) + (8 * (env 4) * (env 1) * (env 7) * (env 2)) + (12 * (env 0) * (env 7) * ((env 4)^2) * ((env 2)^2)) + ((-24) * (env 0) * (env 4) * (env 7) * (env 2) * ((env 1)^2)) + ((-8) * (env 1) * (env 7) * (env 2) * ((env 3)^2) * ((env 4)^2)) + (16 * (env 1) * (env 7) * ((env 3)^2) * ((env 4)^2) * ((env 2)^2)) + (48 * (env 0) * (env 4) * (env 7) * ((env 1)^2) * ((env 2)^2)) + ((-48) * (env 0) * (env 7) * ((env 3)^2) * ((env 4)^2) * ((env 1)^2) * ((env 2)^2)) + ((-16) * (env 0) * (env 3) * (env 1) * (env 7) * ((env 4)^2) * ((env 2)^2)) + ((-4) * (env 0) * (env 3) * (env 1) * (env 7) * (env 2) * ((env 4)^2)) + (24 * (env 0) * (env 7) * (env 2) * ((env 3)^2) * ((env 4)^2) * ((env 1)^2)))

def entry_direction_5_0 (env : Nat → FPS) : FPS := (((-4) * (env 4) * (env 1) * (env 7) * ((env 2)^2)) + (2 * (env 4) * (env 1) * (env 7) * (env 2)) + (12 * (env 0) * (env 7) * ((env 4)^2) * ((env 2)^2)) + ((-12) * (env 0) * (env 4) * (env 7) * (env 2) * ((env 1)^2)) + ((-2) * (env 1) * (env 7) * (env 2) * ((env 3)^2) * ((env 4)^2)) + (4 * (env 1) * (env 7) * ((env 3)^2) * ((env 4)^2) * ((env 2)^2)) + (24 * (env 0) * (env 4) * (env 7) * ((env 1)^2) * ((env 2)^2)) + ((-24) * (env 0) * (env 7) * ((env 3)^2) * ((env 4)^2) * ((env 1)^2) * ((env 2)^2)) + ((-16) * (env 0) * (env 3) * (env 1) * (env 7) * ((env 4)^2) * ((env 2)^2)) + ((-4) * (env 0) * (env 3) * (env 1) * (env 7) * (env 2) * ((env 4)^2)) + (12 * (env 0) * (env 7) * (env 2) * ((env 3)^2) * ((env 4)^2) * ((env 1)^2)))

def entry_den_0_0 (env : Nat → FPS) : FPS := (((-8) * (env 2) * ((env 4)^2)) + (16 * ((env 4)^2) * ((env 2)^2)) + ((-48) * (env 0) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (24 * (env 0) * (env 1) * (env 2) * ((env 4)^2)))

def entry_alpha_0_1 (env : Nat → FPS) : FPS := ((-1) * (env 3) * (env 4))

def entry_alpha_0_3 (env : Nat → FPS) : FPS := ((env 3) * (env 4))

def entry_alpha_0_4 (env : Nat → FPS) : FPS := (env 4)

def entry_alpha_0_5 (env : Nat → FPS) : FPS := ((-1) * (env 4))

def env_T (env : Nat → FPS) : Mat FPS 6 6 := fun r c =>
  match r.val, c.val with
  | 0, 2 => 1
  | 1, 0 => ((3 * (env 9) * (env 6)) + (2 * (env 9) * (env 6) * (env 2)) + ((-6) * (env 0) * (env 9) * (env 6) * (env 1)))
  | 1, 1 => (((-3) * (env 3)) + ((3 * (env 9)^1) * (env 0)) + (3 * (env 0) * (env 3) * (env 1)))
  | 1, 2 => ((env 3) + ((-1) * (env 0)))
  | 1, 4 => (3 + ((-3) * (env 0) * (env 1)))
  | 2, 0 => ((3 * (env 6) * ((env 9)^2)) + ((-6) * (env 6) * (env 2) * ((env 9)^2)) + (4 * (env 5) * (env 6) * ((env 9)^2)) + ((-18) * (env 0) * (env 6) * (env 1) * ((env 9)^2)))
  | 2, 1 => (((-3) * (env 3)) + ((9 * (env 9)^2) * (env 0)) + ((-1) * (env 5) * (env 3)) + ((9 * (env 9)^1) * (env 0) * (env 3) * (env 1)))
  | 2, 2 => (((-3 * (env 9)^1) * (env 0)) + ((3 * (env 9)^1) * (env 3)))
  | 2, 4 => (3 + (env 5) + ((-9 * (env 9)^1) * (env 0) * (env 1)))
  | 3, 1 => ((-1) * (env 3) * (env 2))
  | 3, 3 => ((env 3) * (env 2))
  | 3, 4 => ((1 * (env 9)^1) + (env 2))
  | 3, 5 => ((1 * (env 9)^1) + ((-1) * (env 2)))
  | 4, 0 => ((2 * (env 9) * (env 6) * (env 7) * (env 2)) + (3 * (env 9) * (env 3) * (env 6) * (env 1) * (env 7)) + ((-6) * (env 0) * (env 9) * (env 3) * (env 6) * (env 7) * ((env 1)^2)) + (2 * (env 9) * (env 3) * (env 6) * (env 1) * (env 7) * (env 2)))
  | 4, 1 => (((-3) * ((env 3)^2)) + ((3 * (env 9)^1) * (env 0) * (env 3)) + (3 * (env 0) * (env 1) * ((env 3)^2)))
  | 4, 2 => (((-1) * (env 6)) + ((env 4) * (env 6) * ((env 3)^2)) + ((-1) * (env 0) * (env 3) * (env 4) * (env 6)))
  | 4, 4 => ((3 * (env 3)) + ((-3) * (env 0) * (env 3) * (env 1)))
  | 5, 0 => ((env 6) * (env 7) * (env 2))
  | 5, 1 => (((-1) * (env 9) * (env 6)) + ((-2) * (env 9) * (env 4) * (env 6) * (env 2) * ((env 3)^2)))
  | 5, 3 => (((-1) * (env 9) * (env 6)) + (2 * (env 9) * (env 4) * (env 6) * (env 2) * ((env 3)^2)))
  | 5, 4 => (((1 * (env 9)^1) * (env 3)) + ((env 3) * (env 2)))
  | 5, 5 => (((1 * (env 9)^1) * (env 3)) + ((-1) * (env 3) * (env 2)))
  | _, _ => 0

def env_K (env : Nat → FPS) : Mat FPS 6 6 := fun r c =>
  match r.val, c.val with
  | 0, 0 => ((-2) * (env 1) * (env 8))
  | 0, 1 => (2 * (env 3) * (env 4) * (env 1) * (env 8))
  | 0, 4 => ((-2) * (env 4) * (env 1) * (env 8))
  | 1, 0 => (-3)
  | 2, 0 => (-3)
  | 3, 0 => (-3)
  | 3, 1 => (2 * (env 3) * (env 4))
  | 3, 3 => ((-2) * (env 3) * (env 4))
  | 3, 4 => ((-2) * (env 4))
  | 3, 5 => (2 * (env 4))
  | 4, 0 => ((-2) * (env 6) * (env 1))
  | 4, 1 => ((-3) + (2 * (env 3) * (env 1)))
  | 4, 4 => ((-2) * (env 1))
  | 5, 0 => ((-2) * (env 6) * (env 1))
  | 5, 1 => ((-1) + (2 * (env 3) * (env 1)))
  | 5, 3 => (-2)
  | 5, 4 => ((-2) * (env 1))
  | _, _ => 0

def env_direction (env : Nat → FPS) : Mat FPS 6 1 := fun r c =>
  match r.val, c.val with
  | 0, 0 => (((-8) * (env 2) * ((env 4)^2)) + (16 * ((env 4)^2) * ((env 2)^2)) + ((-48) * (env 0) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (24 * (env 0) * (env 1) * (env 2) * ((env 4)^2)))
  | 1, 0 => (((-16) * (env 0) * ((env 4)^2) * ((env 2)^2)) + ((-8) * (env 3) * (env 2) * ((env 4)^2)) + ((-4) * (env 0) * (env 2) * ((env 4)^2)) + (16 * (env 3) * ((env 4)^2) * ((env 2)^2)) + ((-48) * (env 0) * (env 3) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (24 * (env 0) * (env 3) * (env 1) * (env 2) * ((env 4)^2)))
  | 2, 0 => (((-24) * (env 0) * (env 2) * ((env 4)^2)) + ((-24) * (env 0) * ((env 4)^2) * ((env 2)^2)) + ((-12) * (env 3) * (env 2) * ((env 4)^2)) + (24 * (env 3) * ((env 4)^2) * ((env 2)^2)) + ((-24) * (env 0) * (env 5) * ((env 4)^2) * ((env 2)^2)) + (12 * (env 0) * (env 5) * (env 2) * ((env 4)^2)) + ((-72) * (env 0) * (env 3) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (36 * (env 0) * (env 3) * (env 1) * (env 2) * ((env 4)^2)))
  | 3, 0 => (((-16) * (env 0) * ((env 4)^2) * ((env 2)^2)) + ((-4) * (env 0) * (env 2) * ((env 4)^2)) + ((-2) * (env 3) * (env 2) * ((env 4)^2)) + (4 * (env 3) * ((env 4)^2) * ((env 2)^2)) + ((-24) * (env 0) * (env 3) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (12 * (env 0) * (env 3) * (env 1) * (env 2) * ((env 4)^2)))
  | 4, 0 => (((-16) * (env 4) * (env 1) * (env 7) * ((env 2)^2)) + (8 * (env 4) * (env 1) * (env 7) * (env 2)) + (12 * (env 0) * (env 7) * ((env 4)^2) * ((env 2)^2)) + ((-24) * (env 0) * (env 4) * (env 7) * (env 2) * ((env 1)^2)) + ((-8) * (env 1) * (env 7) * (env 2) * ((env 3)^2) * ((env 4)^2)) + (16 * (env 1) * (env 7) * ((env 3)^2) * ((env 4)^2) * ((env 2)^2)) + (48 * (env 0) * (env 4) * (env 7) * ((env 1)^2) * ((env 2)^2)) + ((-48) * (env 0) * (env 7) * ((env 3)^2) * ((env 4)^2) * ((env 1)^2) * ((env 2)^2)) + ((-16) * (env 0) * (env 3) * (env 1) * (env 7) * ((env 4)^2) * ((env 2)^2)) + ((-4) * (env 0) * (env 3) * (env 1) * (env 7) * (env 2) * ((env 4)^2)) + (24 * (env 0) * (env 7) * (env 2) * ((env 3)^2) * ((env 4)^2) * ((env 1)^2)))
  | 5, 0 => (((-4) * (env 4) * (env 1) * (env 7) * ((env 2)^2)) + (2 * (env 4) * (env 1) * (env 7) * (env 2)) + (12 * (env 0) * (env 7) * ((env 4)^2) * ((env 2)^2)) + ((-12) * (env 0) * (env 4) * (env 7) * (env 2) * ((env 1)^2)) + ((-2) * (env 1) * (env 7) * (env 2) * ((env 3)^2) * ((env 4)^2)) + (4 * (env 1) * (env 7) * ((env 3)^2) * ((env 4)^2) * ((env 2)^2)) + (24 * (env 0) * (env 4) * (env 7) * ((env 1)^2) * ((env 2)^2)) + ((-24) * (env 0) * (env 7) * ((env 3)^2) * ((env 4)^2) * ((env 1)^2) * ((env 2)^2)) + ((-16) * (env 0) * (env 3) * (env 1) * (env 7) * ((env 4)^2) * ((env 2)^2)) + ((-4) * (env 0) * (env 3) * (env 1) * (env 7) * (env 2) * ((env 4)^2)) + (12 * (env 0) * (env 7) * (env 2) * ((env 3)^2) * ((env 4)^2) * ((env 1)^2)))
  | _, _ => 0

def env_den (env : Nat → FPS) : Mat FPS 1 1 := fun r c =>
  match r.val, c.val with
  | 0, 0 => (((-8) * (env 2) * ((env 4)^2)) + (16 * ((env 4)^2) * ((env 2)^2)) + ((-48) * (env 0) * (env 1) * ((env 4)^2) * ((env 2)^2)) + (24 * (env 0) * (env 1) * (env 2) * ((env 4)^2)))
  | _, _ => 0

def env_alpha (env : Nat → FPS) : Mat FPS 1 6 := fun r c =>
  match r.val, c.val with
  | 0, 0 => 1
  | 0, 1 => ((-1) * (env 3) * (env 4))
  | 0, 3 => ((env 3) * (env 4))
  | 0, 4 => (env 4)
  | 0, 5 => ((-1) * (env 4))
  | _, _ => 0

def envResidual (env : Nat → FPS) (r : Fin 6) : FPS :=
  env_direction env r 0 + mv (env_K env) (fun j => env_direction env j 0) r -
  env 10 * mv (env_T env) (fun j => env_direction env j 0 +
    mv (env_K env) (fun k => env_direction env k 0) j) r - env 10 * env_direction env r 0

def reversalVars (z : ReducedChart FPS) (x y : FPS) : Nat → FPS
  | 0 => z.a
  | 1 => z.t
  | 2 => z.u
  | 3 => z.i
  | 4 => z.q
  | 5 => z.c
  | 6 => z.qi
  | 7 => z.ti
  | 8 => z.ui
  | 9 => z.half
  | 10 => x
  | 11 => y
  | _ => 0
end StackSorting.RationalLift
