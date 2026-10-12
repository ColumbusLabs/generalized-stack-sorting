import FiniteMatrix
namespace StackSorting.RationalLift
open StackSorting.FiniteGraph
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

/-- A regular coordinate change inside the original seven-parameter chart.
Only the explicitly displayed q,t,u and 2 units are used. -/
structure ReducedChart (R : Type) [Lean.Grind.CommRing R] where
  a : R
  t : R
  u : R
  i : R
  q : R
  c : R
  qi : R
  ti : R
  ui : R
  half : R
  q_unit : q*qi=1
  t_unit : t*ti=1
  u_unit : u*ui=1
  half_unit : 2*half=1

variable {R : Type} [Lean.Grind.CommRing R]

def reduced_T (z : ReducedChart R) : Mat R 6 6 := fun r c =>
  match r.val, c.val with
  | 0, 2 => 1
  | 1, 0 => ((3 * z.half * z.qi) + (2 * z.half * z.qi * z.u) + ((-6) * z.a * z.half * z.qi * z.t))
  | 1, 1 => (((-3) * z.i) + ((3 * z.half^1) * z.a) + (3 * z.a * z.i * z.t))
  | 1, 2 => (z.i + ((-1) * z.a))
  | 1, 4 => (3 + ((-3) * z.a * z.t))
  | 2, 0 => ((3 * z.qi * (z.half^2)) + ((-6) * z.qi * z.u * (z.half^2)) + (4 * z.c * z.qi * (z.half^2)) + ((-18) * z.a * z.qi * z.t * (z.half^2)))
  | 2, 1 => (((-3) * z.i) + ((9 * z.half^2) * z.a) + ((-1) * z.c * z.i) + ((9 * z.half^1) * z.a * z.i * z.t))
  | 2, 2 => (((-3 * z.half^1) * z.a) + ((3 * z.half^1) * z.i))
  | 2, 4 => (3 + z.c + ((-9 * z.half^1) * z.a * z.t))
  | 3, 1 => ((-1) * z.i * z.u)
  | 3, 3 => (z.i * z.u)
  | 3, 4 => ((1 * z.half^1) + z.u)
  | 3, 5 => ((1 * z.half^1) + ((-1) * z.u))
  | 4, 0 => ((2 * z.half * z.qi * z.ti * z.u) + (3 * z.half * z.i * z.qi * z.t * z.ti) + ((-6) * z.a * z.half * z.i * z.qi * z.ti * (z.t^2)) + (2 * z.half * z.i * z.qi * z.t * z.ti * z.u))
  | 4, 1 => (((-3) * (z.i^2)) + ((3 * z.half^1) * z.a * z.i) + (3 * z.a * z.t * (z.i^2)))
  | 4, 2 => (((-1) * z.qi) + (z.q * z.qi * (z.i^2)) + ((-1) * z.a * z.i * z.q * z.qi))
  | 4, 4 => ((3 * z.i) + ((-3) * z.a * z.i * z.t))
  | 5, 0 => (z.qi * z.ti * z.u)
  | 5, 1 => (((-1) * z.half * z.qi) + ((-2) * z.half * z.q * z.qi * z.u * (z.i^2)))
  | 5, 3 => (((-1) * z.half * z.qi) + (2 * z.half * z.q * z.qi * z.u * (z.i^2)))
  | 5, 4 => (((1 * z.half^1) * z.i) + (z.i * z.u))
  | 5, 5 => (((1 * z.half^1) * z.i) + ((-1) * z.i * z.u))
  | _, _ => 0

def reduced_K (z : ReducedChart R) : Mat R 6 6 := fun r c =>
  match r.val, c.val with
  | 0, 0 => ((-2) * z.t * z.ui)
  | 0, 1 => (2 * z.i * z.q * z.t * z.ui)
  | 0, 4 => ((-2) * z.q * z.t * z.ui)
  | 1, 0 => (-3)
  | 2, 0 => (-3)
  | 3, 0 => (-3)
  | 3, 1 => (2 * z.i * z.q)
  | 3, 3 => ((-2) * z.i * z.q)
  | 3, 4 => ((-2) * z.q)
  | 3, 5 => (2 * z.q)
  | 4, 0 => ((-2) * z.qi * z.t)
  | 4, 1 => ((-3) + (2 * z.i * z.t))
  | 4, 4 => ((-2) * z.t)
  | 5, 0 => ((-2) * z.qi * z.t)
  | 5, 1 => ((-1) + (2 * z.i * z.t))
  | 5, 3 => (-2)
  | 5, 4 => ((-2) * z.t)
  | _, _ => 0

def reduced_direction (z : ReducedChart R) : Mat R 6 1 := fun r c =>
  match r.val, c.val with
  | 0, 0 => (((-8) * z.u * (z.q^2)) + (16 * (z.q^2) * (z.u^2)) + ((-48) * z.a * z.t * (z.q^2) * (z.u^2)) + (24 * z.a * z.t * z.u * (z.q^2)))
  | 1, 0 => (((-16) * z.a * (z.q^2) * (z.u^2)) + ((-8) * z.i * z.u * (z.q^2)) + ((-4) * z.a * z.u * (z.q^2)) + (16 * z.i * (z.q^2) * (z.u^2)) + ((-48) * z.a * z.i * z.t * (z.q^2) * (z.u^2)) + (24 * z.a * z.i * z.t * z.u * (z.q^2)))
  | 2, 0 => (((-24) * z.a * z.u * (z.q^2)) + ((-24) * z.a * (z.q^2) * (z.u^2)) + ((-12) * z.i * z.u * (z.q^2)) + (24 * z.i * (z.q^2) * (z.u^2)) + ((-24) * z.a * z.c * (z.q^2) * (z.u^2)) + (12 * z.a * z.c * z.u * (z.q^2)) + ((-72) * z.a * z.i * z.t * (z.q^2) * (z.u^2)) + (36 * z.a * z.i * z.t * z.u * (z.q^2)))
  | 3, 0 => (((-16) * z.a * (z.q^2) * (z.u^2)) + ((-4) * z.a * z.u * (z.q^2)) + ((-2) * z.i * z.u * (z.q^2)) + (4 * z.i * (z.q^2) * (z.u^2)) + ((-24) * z.a * z.i * z.t * (z.q^2) * (z.u^2)) + (12 * z.a * z.i * z.t * z.u * (z.q^2)))
  | 4, 0 => (((-16) * z.q * z.t * z.ti * (z.u^2)) + (8 * z.q * z.t * z.ti * z.u) + (12 * z.a * z.ti * (z.q^2) * (z.u^2)) + ((-24) * z.a * z.q * z.ti * z.u * (z.t^2)) + ((-8) * z.t * z.ti * z.u * (z.i^2) * (z.q^2)) + (16 * z.t * z.ti * (z.i^2) * (z.q^2) * (z.u^2)) + (48 * z.a * z.q * z.ti * (z.t^2) * (z.u^2)) + ((-48) * z.a * z.ti * (z.i^2) * (z.q^2) * (z.t^2) * (z.u^2)) + ((-16) * z.a * z.i * z.t * z.ti * (z.q^2) * (z.u^2)) + ((-4) * z.a * z.i * z.t * z.ti * z.u * (z.q^2)) + (24 * z.a * z.ti * z.u * (z.i^2) * (z.q^2) * (z.t^2)))
  | 5, 0 => (((-4) * z.q * z.t * z.ti * (z.u^2)) + (2 * z.q * z.t * z.ti * z.u) + (12 * z.a * z.ti * (z.q^2) * (z.u^2)) + ((-12) * z.a * z.q * z.ti * z.u * (z.t^2)) + ((-2) * z.t * z.ti * z.u * (z.i^2) * (z.q^2)) + (4 * z.t * z.ti * (z.i^2) * (z.q^2) * (z.u^2)) + (24 * z.a * z.q * z.ti * (z.t^2) * (z.u^2)) + ((-24) * z.a * z.ti * (z.i^2) * (z.q^2) * (z.t^2) * (z.u^2)) + ((-16) * z.a * z.i * z.t * z.ti * (z.q^2) * (z.u^2)) + ((-4) * z.a * z.i * z.t * z.ti * z.u * (z.q^2)) + (12 * z.a * z.ti * z.u * (z.i^2) * (z.q^2) * (z.t^2)))
  | _, _ => 0

def reduced_den (z : ReducedChart R) : Mat R 1 1 := fun r c =>
  match r.val, c.val with
  | 0, 0 => (((-8) * z.u * (z.q^2)) + (16 * (z.q^2) * (z.u^2)) + ((-48) * z.a * z.t * (z.q^2) * (z.u^2)) + (24 * z.a * z.t * z.u * (z.q^2)))
  | _, _ => 0

def reduced_alpha (z : ReducedChart R) : Mat R 1 6 := fun r c =>
  match r.val, c.val with
  | 0, 0 => 1
  | 0, 1 => ((-1) * z.i * z.q)
  | 0, 3 => (z.i * z.q)
  | 0, 4 => z.q
  | 0, 5 => ((-1) * z.q)
  | _, _ => 0

def reducedResidual (z : ReducedChart R) (x : R) (r : Fin 6) : R :=
  reduced_direction z r 0 + mv (reduced_K z) (fun j => reduced_direction z j 0) r -
  x * mv (reduced_T z) (fun j => reduced_direction z j 0 +
    mv (reduced_K z) (fun k => reduced_direction z k 0) j) r -
  x * reduced_direction z r 0

end StackSorting.RationalLift
