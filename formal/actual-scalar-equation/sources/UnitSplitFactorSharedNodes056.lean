import UnitSplitFactorSharedNodes055
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn3113E : RingExpr := (.mul (.mul (.var 11) (.mul (.var 6) (.pow (.var 2) 4))) (.mul (.int 12) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.var 4) (.var 9))))))))))
def usfn3113P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-12) (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.num (0))))
theorem usfn3113_norm : (reflectRing usfn3113E).toPoly=usfn3113P := by
  exact eq_of_beq (by decide : (reflectRing usfn3113E).toPoly == usfn3113P)

def usfn3114E : RingExpr := (.add (.mul (.int (-7)) (.mul (.var 4) (.var 9))) (.add (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int 3) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))
def usfn3114P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-7) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))
theorem usfn3114_norm : (reflectRing usfn3114E).toPoly=usfn3114P := by
  exact eq_of_beq (by decide : (reflectRing usfn3114E).toPoly == usfn3114P)

def usfn3115E : RingExpr := (.add usfn2457E usfn3114E)
def usfn3115P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨8,1⟩ .unit)) (.add (-7) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))))))))))
theorem usfn3115_norm : (reflectRing usfn3115E).toPoly=usfn3115P := by
  change (reflectRing usfn2457E).toPoly.combine (reflectRing usfn3114E).toPoly=usfn3115P
  rw [usfn2457_norm, usfn3114_norm]
  exact eq_of_beq (by decide : usfn2457P.combine usfn3114P == usfn3115P)

def usfn3116E : RingExpr := (.add usfn1944E usfn3115E)
def usfn3116P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨8,1⟩ .unit)) (.add (-7) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (4)))))))))))
theorem usfn3116_norm : (reflectRing usfn3116E).toPoly=usfn3116P := by
  change (reflectRing usfn1944E).toPoly.combine (reflectRing usfn3115E).toPoly=usfn3116P
  rw [usfn1944_norm, usfn3115_norm]
  exact eq_of_beq (by decide : usfn1944P.combine usfn3115P == usfn3116P)

def usfn3117E : RingExpr := (.mul usfn52E usfn3116E)
def usfn3117P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ .unit)) (.add (-7) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (4) (.mult ⟨8,3⟩ .unit) (.num (0))))))))))))
theorem usfn3117_norm : (reflectRing usfn3117E).toPoly=usfn3117P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn3116E).toPoly=usfn3117P
  rw [usfn52_norm, usfn3116_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn3116P == usfn3117P)

def usfn3118E : RingExpr := (.mul usfn362E usfn3117E)
def usfn3118P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.add (-7) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)) (.num (0))))))))))))
theorem usfn3118_norm : (reflectRing usfn3118E).toPoly=usfn3118P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn3117E).toPoly=usfn3118P
  rw [usfn362_norm, usfn3117_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn3117P == usfn3118P)

def usfn3119E : RingExpr := (.mul usfn2E usfn3118E)
def usfn3119P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-7) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))
theorem usfn3119_norm : (reflectRing usfn3119E).toPoly=usfn3119P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn3118E).toPoly=usfn3119P
  rw [usfn2_norm, usfn3118_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn3118P == usfn3119P)

def usfn3120E : RingExpr := (.mul usfn1E usfn3119E)
def usfn3120P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn3120_norm : (reflectRing usfn3120E).toPoly=usfn3120P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3119E).toPoly=usfn3120P
  rw [usfn1_norm, usfn3119_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3119P == usfn3120P)

def usfn3121E : RingExpr := (.mul usfn890E usfn3120E)
def usfn3121P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (28) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-16) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn3121_norm : (reflectRing usfn3121E).toPoly=usfn3121P := by
  change (reflectRing usfn890E).toPoly.mul (reflectRing usfn3120E).toPoly=usfn3121P
  rw [usfn890_norm, usfn3120_norm]
  exact eq_of_beq (by decide : usfn890P.mul usfn3120P == usfn3121P)

def usfn3122E : RingExpr := (.mul usfn889E usfn3121E)
def usfn3122P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-12) (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-4) (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-4) (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (28) (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-16) (.mult ⟨2,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.num (0))))))))))))
theorem usfn3122_norm : (reflectRing usfn3122E).toPoly=usfn3122P := by
  change (reflectRing usfn889E).toPoly.mul (reflectRing usfn3121E).toPoly=usfn3122P
  rw [usfn889_norm, usfn3121_norm]
  exact eq_of_beq (by decide : usfn889P.mul usfn3121P == usfn3122P)

def usfn3123E : RingExpr := (.mul (.mul (.var 12) (.pow (.var 2) 4)) (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.mul (.pow (.var 8) 3) (.mul (.add (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.mul (.var 0) (.var 3)) (.mul (.int 6) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))))))))))))
def usfn3123P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (24) (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.num (0))))))
theorem usfn3123_norm : (reflectRing usfn3123E).toPoly=usfn3123P := by
  exact eq_of_beq (by decide : (reflectRing usfn3123E).toPoly == usfn3123P)

def usfn3124E : RingExpr := (.mul (.mul (.var 14) (.pow (.var 2) 4)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))))
def usfn3124P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.num (0))))
theorem usfn3124_norm : (reflectRing usfn3124E).toPoly=usfn3124P := by
  exact eq_of_beq (by decide : (reflectRing usfn3124E).toPoly == usfn3124P)

def usfn3125E : RingExpr := (.mul (.mul (.var 11) (.mul (.var 6) (.pow (.var 2) 3))) (.mul (.int (-12)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.mul (.int (-1)) (.var 9)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-1)) (.mul (.var 10) (.var 9))) (.add (.mul (.var 3) (.mul (.var 8) (.var 9))) (.add (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2)))) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 9))))))))))))))))
def usfn3125P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-12) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-12) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.num (0))))))))
theorem usfn3125_norm : (reflectRing usfn3125E).toPoly=usfn3125P := by
  exact eq_of_beq (by decide : (reflectRing usfn3125E).toPoly == usfn3125P)

def usfn3126E : RingExpr := (.mul (.mul (.var 12) (.mul (.var 6) (.pow (.var 2) 3))) (.mul (.int (-24)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))))
def usfn3126P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (24) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.num (0))))
theorem usfn3126_norm : (reflectRing usfn3126E).toPoly=usfn3126P := by
  exact eq_of_beq (by decide : (reflectRing usfn3126E).toPoly == usfn3126P)

def usfn3127E : RingExpr := (.mul (.int (-1)) (.mul (.var 3) (.var 8)))
def usfn3127P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,1⟩ .unit)) (.num (0)))
theorem usfn3127_norm : (reflectRing usfn3127E).toPoly=usfn3127P := by
  exact eq_of_beq (by decide : (reflectRing usfn3127E).toPoly == usfn3127P)

def usfn3128E : RingExpr := (.mul (.int 16) (.mul (.var 3) (.pow (.var 4) 2)))
def usfn3128P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.num (0)))
theorem usfn3128_norm : (reflectRing usfn3128E).toPoly=usfn3128P := by
  exact eq_of_beq (by decide : (reflectRing usfn3128E).toPoly == usfn3128P)

def usfn3129E : RingExpr := (.mul (.int 16) (.mul (.var 4) (.var 9)))
def usfn3129P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))
theorem usfn3129_norm : (reflectRing usfn3129E).toPoly=usfn3129P := by
  exact eq_of_beq (by decide : (reflectRing usfn3129E).toPoly == usfn3129P)

def usfn3130E : RingExpr := (.mul (.int (-16)) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))
def usfn3130P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.num (0)))
theorem usfn3130_norm : (reflectRing usfn3130E).toPoly=usfn3130P := by
  exact eq_of_beq (by decide : (reflectRing usfn3130E).toPoly == usfn3130P)

def usfn3131E : RingExpr := (.mul (.int (-20)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def usfn3131P : Lean.Grind.CommRing.Poly := (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn3131_norm : (reflectRing usfn3131E).toPoly=usfn3131P := by
  exact eq_of_beq (by decide : (reflectRing usfn3131E).toPoly == usfn3131P)

def usfn3132E : RingExpr := (.mul (.int (-7)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))
def usfn3132P : Lean.Grind.CommRing.Poly := (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn3132_norm : (reflectRing usfn3132E).toPoly=usfn3132P := by
  exact eq_of_beq (by decide : (reflectRing usfn3132E).toPoly == usfn3132P)

def usfn3133E : RingExpr := (.mul (.int (-4)) (.mul (.var 8) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))
def usfn3133P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.num (0)))
theorem usfn3133_norm : (reflectRing usfn3133E).toPoly=usfn3133P := by
  exact eq_of_beq (by decide : (reflectRing usfn3133E).toPoly == usfn3133P)

def usfn3134E : RingExpr := (.mul (.int 24) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3)))))
def usfn3134P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn3134_norm : (reflectRing usfn3134E).toPoly=usfn3134P := by
  exact eq_of_beq (by decide : (reflectRing usfn3134E).toPoly == usfn3134P)

def usfn3135E : RingExpr := (.mul (.int (-24)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))))
def usfn3135P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn3135_norm : (reflectRing usfn3135E).toPoly=usfn3135P := by
  exact eq_of_beq (by decide : (reflectRing usfn3135E).toPoly == usfn3135P)

def usfn3136E : RingExpr := (.add (.mul (.int (-12)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.add (.mul (.int 4) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 14) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))
def usfn3136P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn3136_norm : (reflectRing usfn3136E).toPoly=usfn3136P := by
  exact eq_of_beq (by decide : (reflectRing usfn3136E).toPoly == usfn3136P)

def usfn3137E : RingExpr := (.add usfn3135E usfn3136E)
def usfn3137P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))
theorem usfn3137_norm : (reflectRing usfn3137E).toPoly=usfn3137P := by
  change (reflectRing usfn3135E).toPoly.combine (reflectRing usfn3136E).toPoly=usfn3137P
  rw [usfn3135_norm, usfn3136_norm]
  exact eq_of_beq (by decide : usfn3135P.combine usfn3136P == usfn3137P)

def usfn3138E : RingExpr := (.add usfn3134E usfn3137E)
def usfn3138P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn3138_norm : (reflectRing usfn3138E).toPoly=usfn3138P := by
  change (reflectRing usfn3134E).toPoly.combine (reflectRing usfn3137E).toPoly=usfn3138P
  rw [usfn3134_norm, usfn3137_norm]
  exact eq_of_beq (by decide : usfn3134P.combine usfn3137P == usfn3138P)

def usfn3139E : RingExpr := (.add usfn2987E usfn3138E)
def usfn3139P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn3139_norm : (reflectRing usfn3139E).toPoly=usfn3139P := by
  change (reflectRing usfn2987E).toPoly.combine (reflectRing usfn3138E).toPoly=usfn3139P
  rw [usfn2987_norm, usfn3138_norm]
  exact eq_of_beq (by decide : usfn2987P.combine usfn3138P == usfn3139P)

def usfn3140E : RingExpr := (.add usfn3133E usfn3139E)
def usfn3140P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))
theorem usfn3140_norm : (reflectRing usfn3140E).toPoly=usfn3140P := by
  change (reflectRing usfn3133E).toPoly.combine (reflectRing usfn3139E).toPoly=usfn3140P
  rw [usfn3133_norm, usfn3139_norm]
  exact eq_of_beq (by decide : usfn3133P.combine usfn3139P == usfn3140P)

def usfn3141E : RingExpr := (.add usfn2985E usfn3140E)
def usfn3141P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn3141_norm : (reflectRing usfn3141E).toPoly=usfn3141P := by
  change (reflectRing usfn2985E).toPoly.combine (reflectRing usfn3140E).toPoly=usfn3141P
  rw [usfn2985_norm, usfn3140_norm]
  exact eq_of_beq (by decide : usfn2985P.combine usfn3140P == usfn3141P)

def usfn3142E : RingExpr := (.add usfn3132E usfn3141E)
def usfn3142P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))))))))))))
theorem usfn3142_norm : (reflectRing usfn3142E).toPoly=usfn3142P := by
  change (reflectRing usfn3132E).toPoly.combine (reflectRing usfn3141E).toPoly=usfn3142P
  rw [usfn3132_norm, usfn3141_norm]
  exact eq_of_beq (by decide : usfn3132P.combine usfn3141P == usfn3142P)

def usfn3143E : RingExpr := (.add usfn3131E usfn3142E)
def usfn3143P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0))))))))))))))
theorem usfn3143_norm : (reflectRing usfn3143E).toPoly=usfn3143P := by
  change (reflectRing usfn3131E).toPoly.combine (reflectRing usfn3142E).toPoly=usfn3143P
  rw [usfn3131_norm, usfn3142_norm]
  exact eq_of_beq (by decide : usfn3131P.combine usfn3142P == usfn3143P)

def usfn3144E : RingExpr := (.add usfn2984E usfn3143E)
def usfn3144P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))))))))))))))
theorem usfn3144_norm : (reflectRing usfn3144E).toPoly=usfn3144P := by
  change (reflectRing usfn2984E).toPoly.combine (reflectRing usfn3143E).toPoly=usfn3144P
  rw [usfn2984_norm, usfn3143_norm]
  exact eq_of_beq (by decide : usfn2984P.combine usfn3143P == usfn3144P)

def usfn3145E : RingExpr := (.add usfn2983E usfn3144E)
def usfn3145P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))))))
theorem usfn3145_norm : (reflectRing usfn3145E).toPoly=usfn3145P := by
  change (reflectRing usfn2983E).toPoly.combine (reflectRing usfn3144E).toPoly=usfn3145P
  rw [usfn2983_norm, usfn3144_norm]
  exact eq_of_beq (by decide : usfn2983P.combine usfn3144P == usfn3145P)

def usfn3146E : RingExpr := (.add usfn3130E usfn3145E)
def usfn3146P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))))))))
theorem usfn3146_norm : (reflectRing usfn3146E).toPoly=usfn3146P := by
  change (reflectRing usfn3130E).toPoly.combine (reflectRing usfn3145E).toPoly=usfn3146P
  rw [usfn3130_norm, usfn3145_norm]
  exact eq_of_beq (by decide : usfn3130P.combine usfn3145P == usfn3146P)

def usfn3147E : RingExpr := (.add usfn3129E usfn3146E)
def usfn3147P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (16) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))))))))
theorem usfn3147_norm : (reflectRing usfn3147E).toPoly=usfn3147P := by
  change (reflectRing usfn3129E).toPoly.combine (reflectRing usfn3146E).toPoly=usfn3147P
  rw [usfn3129_norm, usfn3146_norm]
  exact eq_of_beq (by decide : usfn3129P.combine usfn3146P == usfn3147P)

def usfn3148E : RingExpr := (.add usfn3128E usfn3147E)
def usfn3148P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (16) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))))))))))))))))))
theorem usfn3148_norm : (reflectRing usfn3148E).toPoly=usfn3148P := by
  change (reflectRing usfn3128E).toPoly.combine (reflectRing usfn3147E).toPoly=usfn3148P
  rw [usfn3128_norm, usfn3147_norm]
  exact eq_of_beq (by decide : usfn3128P.combine usfn3147P == usfn3148P)

def usfn3149E : RingExpr := (.add usfn3127E usfn3148E)
def usfn3149P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,1⟩ .unit)) (.add (16) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))))))))))
theorem usfn3149_norm : (reflectRing usfn3149E).toPoly=usfn3149P := by
  change (reflectRing usfn3127E).toPoly.combine (reflectRing usfn3148E).toPoly=usfn3149P
  rw [usfn3127_norm, usfn3148_norm]
  exact eq_of_beq (by decide : usfn3127P.combine usfn3148P == usfn3149P)

def usfn3150E : RingExpr := (.add usfn890E usfn3149E)
def usfn3150P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,1⟩ .unit)) (.add (16) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (-4))))))))))))))))))))
theorem usfn3150_norm : (reflectRing usfn3150E).toPoly=usfn3150P := by
  change (reflectRing usfn890E).toPoly.combine (reflectRing usfn3149E).toPoly=usfn3150P
  rw [usfn890_norm, usfn3149_norm]
  exact eq_of_beq (by decide : usfn890P.combine usfn3149P == usfn3150P)

def usfn3151E : RingExpr := (.mul usfn52E usfn3150E)
def usfn3151P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ .unit)) (.add (16) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-4) (.mult ⟨8,3⟩ .unit) (.num (0)))))))))))))))))))))
theorem usfn3151_norm : (reflectRing usfn3151E).toPoly=usfn3151P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn3150E).toPoly=usfn3151P
  rw [usfn52_norm, usfn3150_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn3150P == usfn3151P)

def usfn3152E : RingExpr := (.mul usfn2E usfn3151E)
def usfn3152P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.add (16) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)) (.num (0)))))))))))))))))))))
theorem usfn3152_norm : (reflectRing usfn3152E).toPoly=usfn3152P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn3151E).toPoly=usfn3152P
  rw [usfn2_norm, usfn3151_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn3151P == usfn3152P)

def usfn3153E : RingExpr := (.mul usfn1E usfn3152E)
def usfn3153P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-7) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (16) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))))))))))))
theorem usfn3153_norm : (reflectRing usfn3153E).toPoly=usfn3153P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3152E).toPoly=usfn3153P
  rw [usfn1_norm, usfn3152_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3152P == usfn3153P)

def usfn3154E : RingExpr := (.mul usfn459E usfn3153E)
def usfn3154P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (14) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-24) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-4) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-20) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (24) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-16) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-12) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-7) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (16) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-1) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (16) (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (-4) (.mult ⟨2,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))) (.num (0)))))))))))))))))))))
theorem usfn3154_norm : (reflectRing usfn3154E).toPoly=usfn3154P := by
  change (reflectRing usfn459E).toPoly.mul (reflectRing usfn3153E).toPoly=usfn3154P
  rw [usfn459_norm, usfn3153_norm]
  exact eq_of_beq (by decide : usfn459P.mul usfn3153P == usfn3154P)

def usfn3155E : RingExpr := (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))))
def usfn3155P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ .unit))) (.num (0)))
theorem usfn3155_norm : (reflectRing usfn3155E).toPoly=usfn3155P := by
  exact eq_of_beq (by decide : (reflectRing usfn3155E).toPoly == usfn3155P)

def usfn3156E : RingExpr := (.mul (.int 8) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))
def usfn3156P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem usfn3156_norm : (reflectRing usfn3156E).toPoly=usfn3156P := by
  exact eq_of_beq (by decide : (reflectRing usfn3156E).toPoly == usfn3156P)

def usfn3157E : RingExpr := (.mul (.int 12) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2))))
def usfn3157P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn3157_norm : (reflectRing usfn3157E).toPoly=usfn3157P := by
  exact eq_of_beq (by decide : (reflectRing usfn3157E).toPoly == usfn3157P)

def usfn3158E : RingExpr := (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))
def usfn3158P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.num (0)))
theorem usfn3158_norm : (reflectRing usfn3158E).toPoly=usfn3158P := by
  exact eq_of_beq (by decide : (reflectRing usfn3158E).toPoly == usfn3158P)

def usfn3159E : RingExpr := (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 8) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 4))))) (.add (.mul (.int (-12)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))))))))
def usfn3159P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))
theorem usfn3159_norm : (reflectRing usfn3159E).toPoly=usfn3159P := by
  exact eq_of_beq (by decide : (reflectRing usfn3159E).toPoly == usfn3159P)

def usfn3160E : RingExpr := (.add usfn3158E usfn3159E)
def usfn3160P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn3160_norm : (reflectRing usfn3160E).toPoly=usfn3160P := by
  change (reflectRing usfn3158E).toPoly.combine (reflectRing usfn3159E).toPoly=usfn3160P
  rw [usfn3158_norm, usfn3159_norm]
  exact eq_of_beq (by decide : usfn3158P.combine usfn3159P == usfn3160P)

def usfn3161E : RingExpr := (.add usfn3157E usfn3160E)
def usfn3161P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (12) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))
theorem usfn3161_norm : (reflectRing usfn3161E).toPoly=usfn3161P := by
  change (reflectRing usfn3157E).toPoly.combine (reflectRing usfn3160E).toPoly=usfn3161P
  rw [usfn3157_norm, usfn3160_norm]
  exact eq_of_beq (by decide : usfn3157P.combine usfn3160P == usfn3161P)

def usfn3162E : RingExpr := (.add usfn3156E usfn3161E)
def usfn3162P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (12) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))
theorem usfn3162_norm : (reflectRing usfn3162E).toPoly=usfn3162P := by
  change (reflectRing usfn3156E).toPoly.combine (reflectRing usfn3161E).toPoly=usfn3162P
  rw [usfn3156_norm, usfn3161_norm]
  exact eq_of_beq (by decide : usfn3156P.combine usfn3161P == usfn3162P)

def usfn3163E : RingExpr := (.add usfn2655E usfn3162E)
def usfn3163P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (12) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))
theorem usfn3163_norm : (reflectRing usfn3163E).toPoly=usfn3163P := by
  change (reflectRing usfn2655E).toPoly.combine (reflectRing usfn3162E).toPoly=usfn3163P
  rw [usfn2655_norm, usfn3162_norm]
  exact eq_of_beq (by decide : usfn2655P.combine usfn3162P == usfn3163P)

def usfn3164E : RingExpr := (.add usfn3155E usfn3163E)
def usfn3164P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (12) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))))
theorem usfn3164_norm : (reflectRing usfn3164E).toPoly=usfn3164P := by
  change (reflectRing usfn3155E).toPoly.combine (reflectRing usfn3163E).toPoly=usfn3164P
  rw [usfn3155_norm, usfn3163_norm]
  exact eq_of_beq (by decide : usfn3155P.combine usfn3163P == usfn3164P)

def usfn3165E : RingExpr := (.add usfn655E usfn3164E)
def usfn3165P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,1⟩ .unit))) (.add (12) (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ .unit)) (.num (0))))))))))))))
theorem usfn3165_norm : (reflectRing usfn3165E).toPoly=usfn3165P := by
  change (reflectRing usfn655E).toPoly.combine (reflectRing usfn3164E).toPoly=usfn3165P
  rw [usfn655_norm, usfn3164_norm]
  exact eq_of_beq (by decide : usfn655P.combine usfn3164P == usfn3165P)

def usfn3166E : RingExpr := (.mul usfn52E usfn3165E)
def usfn3166P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (-12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (12) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨8,3⟩ .unit))) (.num (0))))))))))))))
theorem usfn3166_norm : (reflectRing usfn3166E).toPoly=usfn3166P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn3165E).toPoly=usfn3166P
  rw [usfn52_norm, usfn3165_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn3165P == usfn3166P)

def usfn3167E : RingExpr := (.mul usfn382E usfn3166E)
def usfn3167P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (-12) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit)))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ .unit))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,3⟩ .unit))) (.num (0))))))))))))))
theorem usfn3167_norm : (reflectRing usfn3167E).toPoly=usfn3167P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn3166E).toPoly=usfn3167P
  rw [usfn382_norm, usfn3166_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn3166P == usfn3167P)

def usfn3168E : RingExpr := (.mul usfn2E usfn3167E)
def usfn3168P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-12) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))
theorem usfn3168_norm : (reflectRing usfn3168E).toPoly=usfn3168P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn3167E).toPoly=usfn3168P
  rw [usfn2_norm, usfn3167_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn3167P == usfn3168P)

def usfn3169E : RingExpr := (.mul usfn1E usfn3168E)
def usfn3169P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (12) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))
theorem usfn3169_norm : (reflectRing usfn3169E).toPoly=usfn3169P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3168E).toPoly=usfn3169P
  rw [usfn1_norm, usfn3168_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3168P == usfn3169P)

def usfn3170E : RingExpr := (.mul usfn361E usfn3169E)
def usfn3170P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))
theorem usfn3170_norm : (reflectRing usfn3170E).toPoly=usfn3170P := by
  change (reflectRing usfn361E).toPoly.mul (reflectRing usfn3169E).toPoly=usfn3170P
  rw [usfn361_norm, usfn3169_norm]
  exact eq_of_beq (by decide : usfn361P.mul usfn3169P == usfn3170P)

def usfn3171E : RingExpr := (.mul usfn1872E usfn3170E)
def usfn3171P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-24) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.add (24) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit)))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))) (.num (0))))))))))))))
theorem usfn3171_norm : (reflectRing usfn3171E).toPoly=usfn3171P := by
  change (reflectRing usfn1872E).toPoly.mul (reflectRing usfn3170E).toPoly=usfn3171P
  rw [usfn1872_norm, usfn3170_norm]
  exact eq_of_beq (by decide : usfn1872P.mul usfn3170P == usfn3171P)

def usfn3172E : RingExpr := (.mul (.mul (.var 14) (.pow (.var 2) 3)) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.mul (.add (.int (-1)) (.mul (.var 3) (.var 8))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
def usfn3172P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit)))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨14,1⟩ .unit))))))) (.num (0))))))
theorem usfn3172_norm : (reflectRing usfn3172E).toPoly=usfn3172P := by
  exact eq_of_beq (by decide : (reflectRing usfn3172E).toPoly == usfn3172P)

def usfn3173E : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-4)) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int 4) (.mul (.var 9) (.pow (.var 4) 2))) (.add (.mul (.var 0) (.mul (.var 8) (.pow (.var 3) 2))) (.add (.mul (.int (-1)) (.mul (.var 3) (.mul (.var 8) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 9) (.pow (.var 4) 2)))) (.add (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))) (.mul (.int 6) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 2)))))))))))))))))))
def usfn3173P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn3173_norm : (reflectRing usfn3173E).toPoly=usfn3173P := by
  exact eq_of_beq (by decide : (reflectRing usfn3173E).toPoly == usfn3173P)

def usfn3174E : RingExpr := (.mul usfn2182E usfn3173E)
def usfn3174P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-4) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (24) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.add (-16) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (16) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨15,1⟩ .unit))))))) (.num (0))))))))))
theorem usfn3174_norm : (reflectRing usfn3174E).toPoly=usfn3174P := by
  change (reflectRing usfn2182E).toPoly.mul (reflectRing usfn3173E).toPoly=usfn3174P
  rw [usfn2182_norm, usfn3173_norm]
  exact eq_of_beq (by decide : usfn2182P.mul usfn3173P == usfn3174P)

def usfn3175E : RingExpr := (.mul (.mul (.var 16) (.pow (.var 2) 3)) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 3) (.add (.int (-1)) (.mul (.var 3) (.var 8)))))))))))
def usfn3175P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨16,1⟩ .unit)))))))) (.num (0))))
theorem usfn3175_norm : (reflectRing usfn3175E).toPoly=usfn3175P := by
  exact eq_of_beq (by decide : (reflectRing usfn3175E).toPoly == usfn3175P)

def usfn3176E : RingExpr := (.mul (.var 11) (.mul (.var 6) (.pow (.var 2) 2)))
def usfn3176P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨2,2⟩ (.mult ⟨6,1⟩ (.mult ⟨11,1⟩ .unit))) (.num (0)))
theorem usfn3176_norm : (reflectRing usfn3176E).toPoly=usfn3176P := by
  exact eq_of_beq (by decide : (reflectRing usfn3176E).toPoly == usfn3176P)

def usfn3177E : RingExpr := (.int 3)
def usfn3177P : Lean.Grind.CommRing.Poly := (.num (3))
theorem usfn3177_norm : (reflectRing usfn3177E).toPoly=usfn3177P := by
  exact eq_of_beq (by decide : (reflectRing usfn3177E).toPoly == usfn3177P)

def usfn3178E : RingExpr := (.mul (.var 4) (.var 9))
def usfn3178P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))
theorem usfn3178_norm : (reflectRing usfn3178E).toPoly=usfn3178P := by
  exact eq_of_beq (by decide : (reflectRing usfn3178E).toPoly == usfn3178P)

def usfn3179E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))
def usfn3179P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem usfn3179_norm : (reflectRing usfn3179E).toPoly=usfn3179P := by
  exact eq_of_beq (by decide : (reflectRing usfn3179E).toPoly == usfn3179P)

def usfn3180E : RingExpr := (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 8) (.mul (.var 10) (.mul (.var 3) (.mul (.var 9) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))))))))
def usfn3180P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))
theorem usfn3180_norm : (reflectRing usfn3180E).toPoly=usfn3180P := by
  exact eq_of_beq (by decide : (reflectRing usfn3180E).toPoly == usfn3180P)

def usfn3181E : RingExpr := (.add usfn2147E usfn3180E)
def usfn3181P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))
theorem usfn3181_norm : (reflectRing usfn3181E).toPoly=usfn3181P := by
  change (reflectRing usfn2147E).toPoly.combine (reflectRing usfn3180E).toPoly=usfn3181P
  rw [usfn2147_norm, usfn3180_norm]
  exact eq_of_beq (by decide : usfn2147P.combine usfn3180P == usfn3181P)

def usfn3182E : RingExpr := (.add usfn3179E usfn3181E)
def usfn3182P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))
theorem usfn3182_norm : (reflectRing usfn3182E).toPoly=usfn3182P := by
  change (reflectRing usfn3179E).toPoly.combine (reflectRing usfn3181E).toPoly=usfn3182P
  rw [usfn3179_norm, usfn3181_norm]
  exact eq_of_beq (by decide : usfn3179P.combine usfn3181P == usfn3182P)

def usfn3183E : RingExpr := (.add usfn505E usfn3182E)
def usfn3183P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))
theorem usfn3183_norm : (reflectRing usfn3183E).toPoly=usfn3183P := by
  change (reflectRing usfn505E).toPoly.combine (reflectRing usfn3182E).toPoly=usfn3183P
  rw [usfn505_norm, usfn3182_norm]
  exact eq_of_beq (by decide : usfn505P.combine usfn3182P == usfn3183P)

def usfn3184E : RingExpr := (.add usfn3178E usfn3183E)
def usfn3184P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (0)))))))))))))
theorem usfn3184_norm : (reflectRing usfn3184E).toPoly=usfn3184P := by
  change (reflectRing usfn3178E).toPoly.combine (reflectRing usfn3183E).toPoly=usfn3184P
  rw [usfn3178_norm, usfn3183_norm]
  exact eq_of_beq (by decide : usfn3178P.combine usfn3183P == usfn3184P)

def usfn3185E : RingExpr := (.add usfn83E usfn3184E)
def usfn3185P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨9,1⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,1⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨4,1⟩ (.mult ⟨9,1⟩ .unit)) (.num (1)))))))))))))
theorem usfn3185_norm : (reflectRing usfn3185E).toPoly=usfn3185P := by
  change (reflectRing usfn83E).toPoly.combine (reflectRing usfn3184E).toPoly=usfn3185P
  rw [usfn83_norm, usfn3184_norm]
  exact eq_of_beq (by decide : usfn83P.combine usfn3184P == usfn3185P)

def usfn3186E : RingExpr := (.mul usfn52E usfn3185E)
def usfn3186P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.add (1) (.mult ⟨8,3⟩ .unit) (.num (0))))))))))))))
theorem usfn3186_norm : (reflectRing usfn3186E).toPoly=usfn3186P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn3185E).toPoly=usfn3186P
  rw [usfn52_norm, usfn3185_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn3185P == usfn3186P)

def usfn3187E : RingExpr := (.mul usfn382E usfn3186E)
def usfn3187P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit))))) (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ .unit)))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨8,3⟩ .unit)) (.num (0))))))))))))))
theorem usfn3187_norm : (reflectRing usfn3187E).toPoly=usfn3187P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn3186E).toPoly=usfn3187P
  rw [usfn382_norm, usfn3186_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn3186P == usfn3187P)

def usfn3188E : RingExpr := (.mul usfn2E usfn3187E)
def usfn3188P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn3188_norm : (reflectRing usfn3188E).toPoly=usfn3188P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn3187E).toPoly=usfn3188P
  rw [usfn2_norm, usfn3187_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn3187P == usfn3188P)

def usfn3189E : RingExpr := (.mul usfn1E usfn3188E)
def usfn3189P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))
theorem usfn3189_norm : (reflectRing usfn3189E).toPoly=usfn3189P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3188E).toPoly=usfn3189P
  rw [usfn1_norm, usfn3188_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3188P == usfn3189P)

def usfn3190E : RingExpr := (.mul usfn3177E usfn3189E)
def usfn3190P : Lean.Grind.CommRing.Poly := (.add (18) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-24) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (12) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit))))) (.add (6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))
theorem usfn3190_norm : (reflectRing usfn3190E).toPoly=usfn3190P := by
  change (reflectRing usfn3177E).toPoly.mul (reflectRing usfn3189E).toPoly=usfn3190P
  rw [usfn3177_norm, usfn3189_norm]
  exact eq_of_beq (by decide : usfn3177P.mul usfn3189P == usfn3190P)

def usfn3191E : RingExpr := (.mul usfn3176E usfn3190E)
def usfn3191P : Lean.Grind.CommRing.Poly := (.add (18) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-6) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-12) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-6) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-6) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (6) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (3) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (3) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.num (0))))))))))))))
theorem usfn3191_norm : (reflectRing usfn3191E).toPoly=usfn3191P := by
  change (reflectRing usfn3176E).toPoly.mul (reflectRing usfn3190E).toPoly=usfn3191P
  rw [usfn3176_norm, usfn3190_norm]
  exact eq_of_beq (by decide : usfn3176P.mul usfn3190P == usfn3191P)

def usfn3192E : RingExpr := (.mul (.mul (.var 12) (.mul (.var 6) (.pow (.var 2) 2))) (.mul (.int 12) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 3) (.mul (.pow (.var 4) 2) (.add (.mul (.var 0) (.pow (.var 3) 2)) (.add (.mul (.var 10) (.var 9)) (.add (.mul (.int (-1)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 9))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 2))))) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.mul (.var 9) (.pow (.var 3) 3))))))))))))))))
def usfn3192P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit)))))))))) (.add (-12) (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨10,1⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (12) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.num (0)))))))
theorem usfn3192_norm : (reflectRing usfn3192E).toPoly=usfn3192P := by
  exact eq_of_beq (by decide : (reflectRing usfn3192E).toPoly == usfn3192P)

#print axioms usfn3192_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
