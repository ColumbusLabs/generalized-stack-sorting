import UnitSplitFactorSharedNodes046
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn2705E : RingExpr := (.add usfn2682E usfn2704E)
def usfn2705P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))))))
theorem usfn2705_norm : (reflectRing usfn2705E).toPoly=usfn2705P := by
  change (reflectRing usfn2682E).toPoly.combine (reflectRing usfn2704E).toPoly=usfn2705P
  rw [usfn2682_norm, usfn2704_norm]
  exact eq_of_beq (by decide : usfn2682P.combine usfn2704P == usfn2705P)

def usfn2706E : RingExpr := (.add usfn2681E usfn2705E)
def usfn2706P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))))))))
theorem usfn2706_norm : (reflectRing usfn2706E).toPoly=usfn2706P := by
  change (reflectRing usfn2681E).toPoly.combine (reflectRing usfn2705E).toPoly=usfn2706P
  rw [usfn2681_norm, usfn2705_norm]
  exact eq_of_beq (by decide : usfn2681P.combine usfn2705P == usfn2706P)

def usfn2707E : RingExpr := (.add usfn2680E usfn2706E)
def usfn2707P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))))))
theorem usfn2707_norm : (reflectRing usfn2707E).toPoly=usfn2707P := by
  change (reflectRing usfn2680E).toPoly.combine (reflectRing usfn2706E).toPoly=usfn2707P
  rw [usfn2680_norm, usfn2706_norm]
  exact eq_of_beq (by decide : usfn2680P.combine usfn2706P == usfn2707P)

def usfn2708E : RingExpr := (.add usfn2655E usfn2707E)
def usfn2708P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))))))))))
theorem usfn2708_norm : (reflectRing usfn2708E).toPoly=usfn2708P := by
  change (reflectRing usfn2655E).toPoly.combine (reflectRing usfn2707E).toPoly=usfn2708P
  rw [usfn2655_norm, usfn2707_norm]
  exact eq_of_beq (by decide : usfn2655P.combine usfn2707P == usfn2708P)

def usfn2709E : RingExpr := (.add usfn2679E usfn2708E)
def usfn2709P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))) (.num (0))))))))))))))))))))))
theorem usfn2709_norm : (reflectRing usfn2709E).toPoly=usfn2709P := by
  change (reflectRing usfn2679E).toPoly.combine (reflectRing usfn2708E).toPoly=usfn2709P
  rw [usfn2679_norm, usfn2708_norm]
  exact eq_of_beq (by decide : usfn2679P.combine usfn2708P == usfn2709P)

def usfn2710E : RingExpr := (.add usfn793E usfn2709E)
def usfn2710P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))) (.add (-1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))))))))))))))
theorem usfn2710_norm : (reflectRing usfn2710E).toPoly=usfn2710P := by
  change (reflectRing usfn793E).toPoly.combine (reflectRing usfn2709E).toPoly=usfn2710P
  rw [usfn793_norm, usfn2709_norm]
  exact eq_of_beq (by decide : usfn793P.combine usfn2709P == usfn2710P)

def usfn2711E : RingExpr := (.add usfn2678E usfn2710E)
def usfn2711P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))) (.add (-1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (6) (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)) (.num (0))))))))))))))))))))))))
theorem usfn2711_norm : (reflectRing usfn2711E).toPoly=usfn2711P := by
  change (reflectRing usfn2678E).toPoly.combine (reflectRing usfn2710E).toPoly=usfn2711P
  rw [usfn2678_norm, usfn2710_norm]
  exact eq_of_beq (by decide : usfn2678P.combine usfn2710P == usfn2711P)

def usfn2712E : RingExpr := (.add usfn655E usfn2711E)
def usfn2712P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))) (.add (-1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ .unit)) (.add (6) (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)) (.num (0)))))))))))))))))))))))))
theorem usfn2712_norm : (reflectRing usfn2712E).toPoly=usfn2712P := by
  change (reflectRing usfn655E).toPoly.combine (reflectRing usfn2711E).toPoly=usfn2712P
  rw [usfn655_norm, usfn2711_norm]
  exact eq_of_beq (by decide : usfn655P.combine usfn2711P == usfn2712P)

def usfn2713E : RingExpr := (.mul usfn4E usfn2712E)
def usfn2713P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))) (.add (-1) (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ .unit))) (.add (6) (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))))))))))))))))
theorem usfn2713_norm : (reflectRing usfn2713E).toPoly=usfn2713P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2712E).toPoly=usfn2713P
  rw [usfn4_norm, usfn2712_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2712P == usfn2713P)

def usfn2714E : RingExpr := (.mul usfn1E usfn2713E)
def usfn2714P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))))))))))))))
theorem usfn2714_norm : (reflectRing usfn2714E).toPoly=usfn2714P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2713E).toPoly=usfn2714P
  rw [usfn1_norm, usfn2713_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2713P == usfn2714P)

def usfn2715E : RingExpr := (.mul usfn100E usfn2714E)
def usfn2715P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-3) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))))))))))))))
theorem usfn2715_norm : (reflectRing usfn2715E).toPoly=usfn2715P := by
  change (reflectRing usfn100E).toPoly.mul (reflectRing usfn2714E).toPoly=usfn2715P
  rw [usfn100_norm, usfn2714_norm]
  exact eq_of_beq (by decide : usfn100P.mul usfn2714P == usfn2715P)

def usfn2716E : RingExpr := (.mul usfn134E usfn2715E)
def usfn2716P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (3) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-4) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-8) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-3) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (1) (.mult ⟨2,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (1) (.mult ⟨2,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (-6) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.num (0)))))))))))))))))))))))))
theorem usfn2716_norm : (reflectRing usfn2716E).toPoly=usfn2716P := by
  change (reflectRing usfn134E).toPoly.mul (reflectRing usfn2715E).toPoly=usfn2716P
  rw [usfn134_norm, usfn2715_norm]
  exact eq_of_beq (by decide : usfn134P.mul usfn2715P == usfn2716P)

def usfn2717E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))
def usfn2717P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ .unit))) (.num (0)))
theorem usfn2717_norm : (reflectRing usfn2717E).toPoly=usfn2717P := by
  exact eq_of_beq (by decide : (reflectRing usfn2717E).toPoly == usfn2717P)

def usfn2718E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))))
def usfn2718P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ .unit))) (.num (0)))
theorem usfn2718_norm : (reflectRing usfn2718E).toPoly=usfn2718P := by
  exact eq_of_beq (by decide : (reflectRing usfn2718E).toPoly == usfn2718P)

def usfn2719E : RingExpr := (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 8) 2)))))
def usfn2719P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2719_norm : (reflectRing usfn2719E).toPoly=usfn2719P := by
  exact eq_of_beq (by decide : (reflectRing usfn2719E).toPoly == usfn2719P)

def usfn2720E : RingExpr := (.mul (.int (-2)) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 8) 2)))))
def usfn2720P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.num (0)))
theorem usfn2720_norm : (reflectRing usfn2720E).toPoly=usfn2720P := by
  exact eq_of_beq (by decide : (reflectRing usfn2720E).toPoly == usfn2720P)

def usfn2721E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.var 9)))))
def usfn2721P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2721_norm : (reflectRing usfn2721E).toPoly=usfn2721P := by
  exact eq_of_beq (by decide : (reflectRing usfn2721E).toPoly == usfn2721P)

def usfn2722E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))
def usfn2722P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.num (0)))
theorem usfn2722_norm : (reflectRing usfn2722E).toPoly=usfn2722P := by
  exact eq_of_beq (by decide : (reflectRing usfn2722E).toPoly == usfn2722P)

def usfn2723E : RingExpr := (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2)))))))))))
def usfn2723P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.num (0)))))))
theorem usfn2723_norm : (reflectRing usfn2723E).toPoly=usfn2723P := by
  exact eq_of_beq (by decide : (reflectRing usfn2723E).toPoly == usfn2723P)

def usfn2724E : RingExpr := (.add usfn2722E usfn2723E)
def usfn2724P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.num (0))))))))
theorem usfn2724_norm : (reflectRing usfn2724E).toPoly=usfn2724P := by
  change (reflectRing usfn2722E).toPoly.combine (reflectRing usfn2723E).toPoly=usfn2724P
  rw [usfn2722_norm, usfn2723_norm]
  exact eq_of_beq (by decide : usfn2722P.combine usfn2723P == usfn2724P)

def usfn2725E : RingExpr := (.add usfn2721E usfn2724E)
def usfn2725P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))))))))
theorem usfn2725_norm : (reflectRing usfn2725E).toPoly=usfn2725P := by
  change (reflectRing usfn2721E).toPoly.combine (reflectRing usfn2724E).toPoly=usfn2725P
  rw [usfn2721_norm, usfn2724_norm]
  exact eq_of_beq (by decide : usfn2721P.combine usfn2724P == usfn2725P)

def usfn2726E : RingExpr := (.add usfn2720E usfn2725E)
def usfn2726P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))
theorem usfn2726_norm : (reflectRing usfn2726E).toPoly=usfn2726P := by
  change (reflectRing usfn2720E).toPoly.combine (reflectRing usfn2725E).toPoly=usfn2726P
  rw [usfn2720_norm, usfn2725_norm]
  exact eq_of_beq (by decide : usfn2720P.combine usfn2725P == usfn2726P)

def usfn2727E : RingExpr := (.add usfn2719E usfn2726E)
def usfn2727P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))))))))))
theorem usfn2727_norm : (reflectRing usfn2727E).toPoly=usfn2727P := by
  change (reflectRing usfn2719E).toPoly.combine (reflectRing usfn2726E).toPoly=usfn2727P
  rw [usfn2719_norm, usfn2726_norm]
  exact eq_of_beq (by decide : usfn2719P.combine usfn2726P == usfn2727P)

def usfn2728E : RingExpr := (.add usfn2718E usfn2727E)
def usfn2728P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn2728_norm : (reflectRing usfn2728E).toPoly=usfn2728P := by
  change (reflectRing usfn2718E).toPoly.combine (reflectRing usfn2727E).toPoly=usfn2728P
  rw [usfn2718_norm, usfn2727_norm]
  exact eq_of_beq (by decide : usfn2718P.combine usfn2727P == usfn2728P)

def usfn2729E : RingExpr := (.add usfn2717E usfn2728E)
def usfn2729P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ .unit))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))))))))))))
theorem usfn2729_norm : (reflectRing usfn2729E).toPoly=usfn2729P := by
  change (reflectRing usfn2717E).toPoly.combine (reflectRing usfn2728E).toPoly=usfn2729P
  rw [usfn2717_norm, usfn2728_norm]
  exact eq_of_beq (by decide : usfn2717P.combine usfn2728P == usfn2729P)

def usfn2730E : RingExpr := (.add usfn2564E usfn2729E)
def usfn2730P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ .unit))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn2730_norm : (reflectRing usfn2730E).toPoly=usfn2730P := by
  change (reflectRing usfn2564E).toPoly.combine (reflectRing usfn2729E).toPoly=usfn2730P
  rw [usfn2564_norm, usfn2729_norm]
  exact eq_of_beq (by decide : usfn2564P.combine usfn2729P == usfn2730P)

def usfn2731E : RingExpr := (.add usfn410E usfn2730E)
def usfn2731P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ .unit))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-2) (.mult ⟨4,1⟩ .unit) (.num (0)))))))))))))))
theorem usfn2731_norm : (reflectRing usfn2731E).toPoly=usfn2731P := by
  change (reflectRing usfn410E).toPoly.combine (reflectRing usfn2730E).toPoly=usfn2731P
  rw [usfn410_norm, usfn2730_norm]
  exact eq_of_beq (by decide : usfn410P.combine usfn2730P == usfn2731P)

def usfn2732E : RingExpr := (.mul usfn4E usfn2731E)
def usfn2732P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ .unit))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,3⟩ .unit))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)) (.num (0)))))))))))))))
theorem usfn2732_norm : (reflectRing usfn2732E).toPoly=usfn2732P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2731E).toPoly=usfn2732P
  rw [usfn4_norm, usfn2731_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2731P == usfn2732P)

def usfn2733E : RingExpr := (.mul usfn362E usfn2732E)
def usfn2733P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ .unit)) (.num (0)))))))))))))))
theorem usfn2733_norm : (reflectRing usfn2733E).toPoly=usfn2733P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn2732E).toPoly=usfn2733P
  rw [usfn362_norm, usfn2732_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn2732P == usfn2733P)

def usfn2734E : RingExpr := (.mul usfn382E usfn2733E)
def usfn2734P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ .unit))) (.num (0)))))))))))))))
theorem usfn2734_norm : (reflectRing usfn2734E).toPoly=usfn2734P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn2733E).toPoly=usfn2734P
  rw [usfn382_norm, usfn2733_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn2733P == usfn2734P)

def usfn2735E : RingExpr := (.mul usfn2E usfn2734E)
def usfn2735P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))))
theorem usfn2735_norm : (reflectRing usfn2735E).toPoly=usfn2735P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn2734E).toPoly=usfn2735P
  rw [usfn2_norm, usfn2734_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn2734P == usfn2735P)

def usfn2736E : RingExpr := (.mul usfn1E usfn2735E)
def usfn2736P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))))
theorem usfn2736_norm : (reflectRing usfn2736E).toPoly=usfn2736P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2735E).toPoly=usfn2736P
  rw [usfn1_norm, usfn2735_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2735P == usfn2736P)

def usfn2737E : RingExpr := (.mul usfn361E usfn2736E)
def usfn2737P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))))
theorem usfn2737_norm : (reflectRing usfn2737E).toPoly=usfn2737P := by
  change (reflectRing usfn361E).toPoly.mul (reflectRing usfn2736E).toPoly=usfn2737P
  rw [usfn361_norm, usfn2736_norm]
  exact eq_of_beq (by decide : usfn361P.mul usfn2736P == usfn2737P)

def usfn2738E : RingExpr := (.mul usfn933E usfn2737E)
def usfn2738P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (8) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (2) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-4) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.num (0)))))))))))))))
theorem usfn2738_norm : (reflectRing usfn2738E).toPoly=usfn2738P := by
  change (reflectRing usfn933E).toPoly.mul (reflectRing usfn2737E).toPoly=usfn2738P
  rw [usfn933_norm, usfn2737_norm]
  exact eq_of_beq (by decide : usfn933P.mul usfn2737P == usfn2738P)

def usfn2739E : RingExpr := (.mul (.mul (.var 14) (.pow (.var 2) 2)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 8))))))))))))))
def usfn2739P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨14,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit))))))))) (.num (0))))
theorem usfn2739_norm : (reflectRing usfn2739E).toPoly=usfn2739P := by
  exact eq_of_beq (by decide : (reflectRing usfn2739E).toPoly == usfn2739P)

def usfn2740E : RingExpr := (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2))))
def usfn2740P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn2740_norm : (reflectRing usfn2740E).toPoly=usfn2740P := by
  exact eq_of_beq (by decide : (reflectRing usfn2740E).toPoly == usfn2740P)

def usfn2741E : RingExpr := (.mul (.int 4) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))
def usfn2741P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn2741_norm : (reflectRing usfn2741E).toPoly=usfn2741P := by
  exact eq_of_beq (by decide : (reflectRing usfn2741E).toPoly == usfn2741P)

def usfn2742E : RingExpr := (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))))))))
def usfn2742P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn2742_norm : (reflectRing usfn2742E).toPoly=usfn2742P := by
  exact eq_of_beq (by decide : (reflectRing usfn2742E).toPoly == usfn2742P)

def usfn2743E : RingExpr := (.add usfn2658E usfn2742E)
def usfn2743P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))
theorem usfn2743_norm : (reflectRing usfn2743E).toPoly=usfn2743P := by
  change (reflectRing usfn2658E).toPoly.combine (reflectRing usfn2742E).toPoly=usfn2743P
  rw [usfn2658_norm, usfn2742_norm]
  exact eq_of_beq (by decide : usfn2658P.combine usfn2742P == usfn2743P)

def usfn2744E : RingExpr := (.add usfn2741E usfn2743E)
def usfn2744P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn2744_norm : (reflectRing usfn2744E).toPoly=usfn2744P := by
  change (reflectRing usfn2741E).toPoly.combine (reflectRing usfn2743E).toPoly=usfn2744P
  rw [usfn2741_norm, usfn2743_norm]
  exact eq_of_beq (by decide : usfn2741P.combine usfn2743P == usfn2744P)

def usfn2745E : RingExpr := (.add usfn2656E usfn2744E)
def usfn2745P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn2745_norm : (reflectRing usfn2745E).toPoly=usfn2745P := by
  change (reflectRing usfn2656E).toPoly.combine (reflectRing usfn2744E).toPoly=usfn2745P
  rw [usfn2656_norm, usfn2744_norm]
  exact eq_of_beq (by decide : usfn2656P.combine usfn2744P == usfn2745P)

def usfn2746E : RingExpr := (.add usfn2511E usfn2745E)
def usfn2746P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))))))))))
theorem usfn2746_norm : (reflectRing usfn2746E).toPoly=usfn2746P := by
  change (reflectRing usfn2511E).toPoly.combine (reflectRing usfn2745E).toPoly=usfn2746P
  rw [usfn2511_norm, usfn2745_norm]
  exact eq_of_beq (by decide : usfn2511P.combine usfn2745P == usfn2746P)

def usfn2747E : RingExpr := (.add usfn2655E usfn2746E)
def usfn2747P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn2747_norm : (reflectRing usfn2747E).toPoly=usfn2747P := by
  change (reflectRing usfn2655E).toPoly.combine (reflectRing usfn2746E).toPoly=usfn2747P
  rw [usfn2655_norm, usfn2746_norm]
  exact eq_of_beq (by decide : usfn2655P.combine usfn2746P == usfn2747P)

def usfn2748E : RingExpr := (.add usfn2740E usfn2747E)
def usfn2748P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))))
theorem usfn2748_norm : (reflectRing usfn2748E).toPoly=usfn2748P := by
  change (reflectRing usfn2740E).toPoly.combine (reflectRing usfn2747E).toPoly=usfn2748P
  rw [usfn2740_norm, usfn2747_norm]
  exact eq_of_beq (by decide : usfn2740P.combine usfn2747P == usfn2748P)

def usfn2749E : RingExpr := (.add usfn2508E usfn2748E)
def usfn2749P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn2749_norm : (reflectRing usfn2749E).toPoly=usfn2749P := by
  change (reflectRing usfn2508E).toPoly.combine (reflectRing usfn2748E).toPoly=usfn2749P
  rw [usfn2508_norm, usfn2748_norm]
  exact eq_of_beq (by decide : usfn2508P.combine usfn2748P == usfn2749P)

def usfn2750E : RingExpr := (.add usfn2507E usfn2749E)
def usfn2750P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))))))))))))))
theorem usfn2750_norm : (reflectRing usfn2750E).toPoly=usfn2750P := by
  change (reflectRing usfn2507E).toPoly.combine (reflectRing usfn2749E).toPoly=usfn2750P
  rw [usfn2507_norm, usfn2749_norm]
  exact eq_of_beq (by decide : usfn2507P.combine usfn2749P == usfn2750P)

def usfn2751E : RingExpr := (.add usfn655E usfn2750E)
def usfn2751P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ .unit)) (.num (0))))))))))))))))
theorem usfn2751_norm : (reflectRing usfn2751E).toPoly=usfn2751P := by
  change (reflectRing usfn655E).toPoly.combine (reflectRing usfn2750E).toPoly=usfn2751P
  rw [usfn655_norm, usfn2750_norm]
  exact eq_of_beq (by decide : usfn655P.combine usfn2750P == usfn2751P)

def usfn2752E : RingExpr := (.add usfn410E usfn2751E)
def usfn2752P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ .unit)) (.add (-2) (.mult ⟨4,1⟩ .unit) (.num (0)))))))))))))))))
theorem usfn2752_norm : (reflectRing usfn2752E).toPoly=usfn2752P := by
  change (reflectRing usfn410E).toPoly.combine (reflectRing usfn2751E).toPoly=usfn2752P
  rw [usfn410_norm, usfn2751_norm]
  exact eq_of_beq (by decide : usfn410P.combine usfn2751P == usfn2752P)

def usfn2753E : RingExpr := (.mul usfn52E usfn2752E)
def usfn2753P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,3⟩ .unit))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)) (.num (0)))))))))))))))))
theorem usfn2753_norm : (reflectRing usfn2753E).toPoly=usfn2753P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn2752E).toPoly=usfn2753P
  rw [usfn52_norm, usfn2752_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn2752P == usfn2753P)

def usfn2754E : RingExpr := (.mul usfn409E usfn2753E)
def usfn2754P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-6) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,3⟩ .unit))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit))) (.num (0)))))))))))))))))
theorem usfn2754_norm : (reflectRing usfn2754E).toPoly=usfn2754P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn2753E).toPoly=usfn2754P
  rw [usfn409_norm, usfn2753_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn2753P == usfn2754P)

def usfn2755E : RingExpr := (.mul usfn2E usfn2754E)
def usfn2755P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))))))
theorem usfn2755_norm : (reflectRing usfn2755E).toPoly=usfn2755P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn2754E).toPoly=usfn2755P
  rw [usfn2_norm, usfn2754_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn2754P == usfn2755P)

def usfn2756E : RingExpr := (.mul usfn1E usfn2755E)
def usfn2756P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-6) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))))))
theorem usfn2756_norm : (reflectRing usfn2756E).toPoly=usfn2756P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn2755E).toPoly=usfn2756P
  rw [usfn1_norm, usfn2755_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn2755P == usfn2756P)

def usfn2757E : RingExpr := (.mul usfn408E usfn2756E)
def usfn2757P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (12) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))))))
theorem usfn2757_norm : (reflectRing usfn2757E).toPoly=usfn2757P := by
  change (reflectRing usfn408E).toPoly.mul (reflectRing usfn2756E).toPoly=usfn2757P
  rw [usfn408_norm, usfn2756_norm]
  exact eq_of_beq (by decide : usfn408P.mul usfn2756P == usfn2757P)

def usfn2758E : RingExpr := (.mul usfn944E usfn2757E)
def usfn2758P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (12) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.add (-8) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.num (0)))))))))))))))))
theorem usfn2758_norm : (reflectRing usfn2758E).toPoly=usfn2758P := by
  change (reflectRing usfn944E).toPoly.mul (reflectRing usfn2757E).toPoly=usfn2758P
  rw [usfn944_norm, usfn2757_norm]
  exact eq_of_beq (by decide : usfn944P.mul usfn2757P == usfn2758P)

def usfn2759E : RingExpr := (.mul (.mul (.var 16) (.pow (.var 2) 2)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.mul (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))
def usfn2759P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit)))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit))))))) (.num (0))))))
theorem usfn2759_norm : (reflectRing usfn2759E).toPoly=usfn2759P := by
  exact eq_of_beq (by decide : (reflectRing usfn2759E).toPoly == usfn2759P)

def usfn2760E : RingExpr := (.mul (.int (-3)) (.var 10))
def usfn2760P : Lean.Grind.CommRing.Poly := (.add (-3) (.mult ⟨10,1⟩ .unit) (.num (0)))
theorem usfn2760_norm : (reflectRing usfn2760E).toPoly=usfn2760P := by
  exact eq_of_beq (by decide : (reflectRing usfn2760E).toPoly == usfn2760P)

def usfn2761E : RingExpr := (.mul (.int (-1)) (.mul (.pow (.var 0) 2) (.pow (.var 3) 3)))
def usfn2761P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ .unit)) (.num (0)))
theorem usfn2761_norm : (reflectRing usfn2761E).toPoly=usfn2761P := by
  exact eq_of_beq (by decide : (reflectRing usfn2761E).toPoly == usfn2761P)

def usfn2762E : RingExpr := (.mul (.int (-4)) (.mul (.var 10) (.mul (.var 3) (.pow (.var 4) 2))))
def usfn2762P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn2762_norm : (reflectRing usfn2762E).toPoly=usfn2762P := by
  exact eq_of_beq (by decide : (reflectRing usfn2762E).toPoly == usfn2762P)

def usfn2763E : RingExpr := (.mul (.var 0) (.mul (.var 10) (.mul (.var 3) (.var 9))))
def usfn2763P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2763_norm : (reflectRing usfn2763E).toPoly=usfn2763P := by
  exact eq_of_beq (by decide : (reflectRing usfn2763E).toPoly == usfn2763P)

def usfn2764E : RingExpr := (.mul (.int 2) (.mul (.var 10) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 8) 2)))))
def usfn2764P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2764_norm : (reflectRing usfn2764E).toPoly=usfn2764P := by
  exact eq_of_beq (by decide : (reflectRing usfn2764E).toPoly == usfn2764P)

def usfn2765E : RingExpr := (.mul (.int 4) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))
def usfn2765P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2765_norm : (reflectRing usfn2765E).toPoly=usfn2765P := by
  exact eq_of_beq (by decide : (reflectRing usfn2765E).toPoly == usfn2765P)

def usfn2766E : RingExpr := (.mul (.int 6) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.pow (.var 3) 2)))))
def usfn2766P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn2766_norm : (reflectRing usfn2766E).toPoly=usfn2766P := by
  exact eq_of_beq (by decide : (reflectRing usfn2766E).toPoly == usfn2766P)

def usfn2767E : RingExpr := (.mul (.var 10) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))
def usfn2767P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2767_norm : (reflectRing usfn2767E).toPoly=usfn2767P := by
  exact eq_of_beq (by decide : (reflectRing usfn2767E).toPoly == usfn2767P)

def usfn2768E : RingExpr := (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 4) (.pow (.var 8) 2))))))
def usfn2768P : Lean.Grind.CommRing.Poly := (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2768_norm : (reflectRing usfn2768E).toPoly=usfn2768P := by
  exact eq_of_beq (by decide : (reflectRing usfn2768E).toPoly == usfn2768P)

def usfn2769E : RingExpr := (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.pow (.var 8) 2))))))
def usfn2769P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn2769_norm : (reflectRing usfn2769E).toPoly=usfn2769P := by
  exact eq_of_beq (by decide : (reflectRing usfn2769E).toPoly == usfn2769P)

def usfn2770E : RingExpr := (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))
def usfn2770P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn2770_norm : (reflectRing usfn2770E).toPoly=usfn2770P := by
  exact eq_of_beq (by decide : (reflectRing usfn2770E).toPoly == usfn2770P)

def usfn2771E : RingExpr := (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))
def usfn2771P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn2771_norm : (reflectRing usfn2771E).toPoly=usfn2771P := by
  exact eq_of_beq (by decide : (reflectRing usfn2771E).toPoly == usfn2771P)

def usfn2772E : RingExpr := (.add usfn2770E usfn2771E)
def usfn2772P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))
theorem usfn2772_norm : (reflectRing usfn2772E).toPoly=usfn2772P := by
  change (reflectRing usfn2770E).toPoly.combine (reflectRing usfn2771E).toPoly=usfn2772P
  rw [usfn2770_norm, usfn2771_norm]
  exact eq_of_beq (by decide : usfn2770P.combine usfn2771P == usfn2772P)

def usfn2773E : RingExpr := (.add usfn2769E usfn2772E)
def usfn2773P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn2773_norm : (reflectRing usfn2773E).toPoly=usfn2773P := by
  change (reflectRing usfn2769E).toPoly.combine (reflectRing usfn2772E).toPoly=usfn2773P
  rw [usfn2769_norm, usfn2772_norm]
  exact eq_of_beq (by decide : usfn2769P.combine usfn2772P == usfn2773P)

def usfn2774E : RingExpr := (.add usfn2768E usfn2773E)
def usfn2774P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn2774_norm : (reflectRing usfn2774E).toPoly=usfn2774P := by
  change (reflectRing usfn2768E).toPoly.combine (reflectRing usfn2773E).toPoly=usfn2774P
  rw [usfn2768_norm, usfn2773_norm]
  exact eq_of_beq (by decide : usfn2768P.combine usfn2773P == usfn2774P)

def usfn2775E : RingExpr := (.add usfn2767E usfn2774E)
def usfn2775P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))
theorem usfn2775_norm : (reflectRing usfn2775E).toPoly=usfn2775P := by
  change (reflectRing usfn2767E).toPoly.combine (reflectRing usfn2774E).toPoly=usfn2775P
  rw [usfn2767_norm, usfn2774_norm]
  exact eq_of_beq (by decide : usfn2767P.combine usfn2774P == usfn2775P)

def usfn2776E : RingExpr := (.add usfn2766E usfn2775E)
def usfn2776P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn2776_norm : (reflectRing usfn2776E).toPoly=usfn2776P := by
  change (reflectRing usfn2766E).toPoly.combine (reflectRing usfn2775E).toPoly=usfn2776P
  rw [usfn2766_norm, usfn2775_norm]
  exact eq_of_beq (by decide : usfn2766P.combine usfn2775P == usfn2776P)

def usfn2777E : RingExpr := (.add usfn2765E usfn2776E)
def usfn2777P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))
theorem usfn2777_norm : (reflectRing usfn2777E).toPoly=usfn2777P := by
  change (reflectRing usfn2765E).toPoly.combine (reflectRing usfn2776E).toPoly=usfn2777P
  rw [usfn2765_norm, usfn2776_norm]
  exact eq_of_beq (by decide : usfn2765P.combine usfn2776P == usfn2777P)

def usfn2778E : RingExpr := (.add usfn2764E usfn2777E)
def usfn2778P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))
theorem usfn2778_norm : (reflectRing usfn2778E).toPoly=usfn2778P := by
  change (reflectRing usfn2764E).toPoly.combine (reflectRing usfn2777E).toPoly=usfn2778P
  rw [usfn2764_norm, usfn2777_norm]
  exact eq_of_beq (by decide : usfn2764P.combine usfn2777P == usfn2778P)

def usfn2779E : RingExpr := (.add usfn2763E usfn2778E)
def usfn2779P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))))
theorem usfn2779_norm : (reflectRing usfn2779E).toPoly=usfn2779P := by
  change (reflectRing usfn2763E).toPoly.combine (reflectRing usfn2778E).toPoly=usfn2779P
  rw [usfn2763_norm, usfn2778_norm]
  exact eq_of_beq (by decide : usfn2763P.combine usfn2778P == usfn2779P)

def usfn2780E : RingExpr := (.add usfn506E usfn2779E)
def usfn2780P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn2780_norm : (reflectRing usfn2780E).toPoly=usfn2780P := by
  change (reflectRing usfn506E).toPoly.combine (reflectRing usfn2779E).toPoly=usfn2780P
  rw [usfn506_norm, usfn2779_norm]
  exact eq_of_beq (by decide : usfn506P.combine usfn2779P == usfn2780P)

def usfn2781E : RingExpr := (.add usfn2762E usfn2780E)
def usfn2781P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))))))))))))))))
theorem usfn2781_norm : (reflectRing usfn2781E).toPoly=usfn2781P := by
  change (reflectRing usfn2762E).toPoly.combine (reflectRing usfn2780E).toPoly=usfn2781P
  rw [usfn2762_norm, usfn2780_norm]
  exact eq_of_beq (by decide : usfn2762P.combine usfn2780P == usfn2781P)

def usfn2782E : RingExpr := (.add usfn2761E usfn2781E)
def usfn2782P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ .unit)) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))))
theorem usfn2782_norm : (reflectRing usfn2782E).toPoly=usfn2782P := by
  change (reflectRing usfn2761E).toPoly.combine (reflectRing usfn2781E).toPoly=usfn2782P
  rw [usfn2761_norm, usfn2781_norm]
  exact eq_of_beq (by decide : usfn2761P.combine usfn2781P == usfn2782P)

def usfn2783E : RingExpr := (.add usfn2760E usfn2782E)
def usfn2783P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ .unit)) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-3) (.mult ⟨10,1⟩ .unit) (.num (0)))))))))))))))))))
theorem usfn2783_norm : (reflectRing usfn2783E).toPoly=usfn2783P := by
  change (reflectRing usfn2760E).toPoly.combine (reflectRing usfn2782E).toPoly=usfn2783P
  rw [usfn2760_norm, usfn2782_norm]
  exact eq_of_beq (by decide : usfn2760P.combine usfn2782P == usfn2783P)

def usfn2784E : RingExpr := (.mul usfn4E usfn2783E)
def usfn2784P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨8,2⟩ .unit))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,2⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-3) (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)) (.num (0)))))))))))))))))))
theorem usfn2784_norm : (reflectRing usfn2784E).toPoly=usfn2784P := by
  change (reflectRing usfn4E).toPoly.mul (reflectRing usfn2783E).toPoly=usfn2784P
  rw [usfn4_norm, usfn2783_norm]
  exact eq_of_beq (by decide : usfn4P.mul usfn2783P == usfn2784P)

#print axioms usfn2784_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
