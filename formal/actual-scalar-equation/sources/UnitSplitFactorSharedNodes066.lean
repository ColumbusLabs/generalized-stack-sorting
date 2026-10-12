import UnitSplitFactorSharedNodes065
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn3603E : RingExpr := (.int (-12))
def usfn3603P : Lean.Grind.CommRing.Poly := (.num (-12))
theorem usfn3603_norm : (reflectRing usfn3603E).toPoly=usfn3603P := by
  exact eq_of_beq (by decide : (reflectRing usfn3603E).toPoly == usfn3603P)

def usfn3604E : RingExpr := (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 3) (.mul (.var 7) (.mul (.var 10) (.var 8)))) (.add (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))))))
def usfn3604P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (3) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ .unit))) (.num (0))))))))
theorem usfn3604_norm : (reflectRing usfn3604E).toPoly=usfn3604P := by
  exact eq_of_beq (by decide : (reflectRing usfn3604E).toPoly == usfn3604P)

def usfn3605E : RingExpr := (.mul usfn102E usfn3604E)
def usfn3605P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit)))) (.add (3) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0))))))))
theorem usfn3605_norm : (reflectRing usfn3605E).toPoly=usfn3605P := by
  change (reflectRing usfn102E).toPoly.mul (reflectRing usfn3604E).toPoly=usfn3605P
  rw [usfn102_norm, usfn3604_norm]
  exact eq_of_beq (by decide : usfn102P.mul usfn3604P == usfn3605P)

def usfn3606E : RingExpr := (.mul usfn3E usfn3605E)
def usfn3606P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (3) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-1) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0))))))))
theorem usfn3606_norm : (reflectRing usfn3606E).toPoly=usfn3606P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn3605E).toPoly=usfn3606P
  rw [usfn3_norm, usfn3605_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn3605P == usfn3606P)

def usfn3607E : RingExpr := (.mul usfn382E usfn3606E)
def usfn3607P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0))))))))
theorem usfn3607_norm : (reflectRing usfn3607E).toPoly=usfn3607P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn3606E).toPoly=usfn3607P
  rw [usfn382_norm, usfn3606_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn3606P == usfn3607P)

def usfn3608E : RingExpr := (.mul usfn1E usfn3607E)
def usfn3608P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (2) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn3608_norm : (reflectRing usfn3608E).toPoly=usfn3608P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3607E).toPoly=usfn3608P
  rw [usfn1_norm, usfn3607_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3607P == usfn3608P)

def usfn3609E : RingExpr := (.mul usfn3603E usfn3608E)
def usfn3609P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (72) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-24) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-36) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (12) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn3609_norm : (reflectRing usfn3609E).toPoly=usfn3609P := by
  change (reflectRing usfn3603E).toPoly.mul (reflectRing usfn3608E).toPoly=usfn3609P
  rw [usfn3603_norm, usfn3608_norm]
  exact eq_of_beq (by decide : usfn3603P.mul usfn3608P == usfn3609P)

def usfn3610E : RingExpr := (.mul usfn3602E usfn3609E)
def usfn3610P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (72) (.mult ⟨1,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))))) (.add (-24) (.mult ⟨1,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-36) (.mult ⟨1,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (12) (.mult ⟨1,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))))) (.num (0))))))))
theorem usfn3610_norm : (reflectRing usfn3610E).toPoly=usfn3610P := by
  change (reflectRing usfn3602E).toPoly.mul (reflectRing usfn3609E).toPoly=usfn3610P
  rw [usfn3602_norm, usfn3609_norm]
  exact eq_of_beq (by decide : usfn3602P.mul usfn3609P == usfn3610P)

def usfn3611E : RingExpr := (.mul (.mul (.var 5) (.mul (.pow (.var 1) 2) (.pow (.var 2) 2))) (.mul (.int 8) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def usfn3611P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (-8) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))))) (.num (0))))
theorem usfn3611_norm : (reflectRing usfn3611E).toPoly=usfn3611P := by
  exact eq_of_beq (by decide : (reflectRing usfn3611E).toPoly == usfn3611P)

def usfn3612E : RingExpr := (.mul (.pow (.var 1) 2) (.pow (.var 2) 2))
def usfn3612P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ .unit)) (.num (0)))
theorem usfn3612_norm : (reflectRing usfn3612E).toPoly=usfn3612P := by
  exact eq_of_beq (by decide : (reflectRing usfn3612E).toPoly == usfn3612P)

def usfn3613E : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.add (.mul (.int 3) (.var 10)) (.add (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.var 4))))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.var 8)))))) (.add (.mul (.int 12) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))))))))))))))
def usfn3613P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (12) (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-3) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (3) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn3613_norm : (reflectRing usfn3613E).toPoly=usfn3613P := by
  exact eq_of_beq (by decide : (reflectRing usfn3613E).toPoly == usfn3613P)

def usfn3614E : RingExpr := (.mul usfn3603E usfn3613E)
def usfn3614P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-144) (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (36) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (72) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-36) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (12) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn3614_norm : (reflectRing usfn3614E).toPoly=usfn3614P := by
  change (reflectRing usfn3603E).toPoly.mul (reflectRing usfn3613E).toPoly=usfn3614P
  rw [usfn3603_norm, usfn3613_norm]
  exact eq_of_beq (by decide : usfn3603P.mul usfn3613P == usfn3614P)

def usfn3615E : RingExpr := (.mul usfn3612E usfn3614E)
def usfn3615P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (-144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (36) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))))) (.add (72) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-36) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (12) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))))) (.num (0))))))))
theorem usfn3615_norm : (reflectRing usfn3615E).toPoly=usfn3615P := by
  change (reflectRing usfn3612E).toPoly.mul (reflectRing usfn3614E).toPoly=usfn3615P
  rw [usfn3612_norm, usfn3614_norm]
  exact eq_of_beq (by decide : usfn3612P.mul usfn3614P == usfn3615P)

def usfn3616E : RingExpr := (.mul (.mul (.var 5) (.mul (.var 2) (.pow (.var 1) 2))) (.mul (.int (-2)) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def usfn3616P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (4) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (8) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))))) (.add (-2) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.num (0))))))
theorem usfn3616_norm : (reflectRing usfn3616E).toPoly=usfn3616P := by
  exact eq_of_beq (by decide : (reflectRing usfn3616E).toPoly == usfn3616P)

def usfn3617E : RingExpr := (.mul (.var 2) (.pow (.var 1) 2))
def usfn3617P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ .unit)) (.num (0)))
theorem usfn3617_norm : (reflectRing usfn3617E).toPoly=usfn3617P := by
  exact eq_of_beq (by decide : (reflectRing usfn3617E).toPoly == usfn3617P)

def usfn3618E : RingExpr := (.mul (.var 3) (.var 4))
def usfn3618P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit)) (.num (0)))
theorem usfn3618_norm : (reflectRing usfn3618E).toPoly=usfn3618P := by
  exact eq_of_beq (by decide : (reflectRing usfn3618E).toPoly == usfn3618P)

def usfn3619E : RingExpr := (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))
def usfn3619P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)) (.num (0)))
theorem usfn3619_norm : (reflectRing usfn3619E).toPoly=usfn3619P := by
  exact eq_of_beq (by decide : (reflectRing usfn3619E).toPoly == usfn3619P)

def usfn3620E : RingExpr := (.mul (.var 7) (.mul (.var 10) (.var 8)))
def usfn3620P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn3620_norm : (reflectRing usfn3620E).toPoly=usfn3620P := by
  exact eq_of_beq (by decide : (reflectRing usfn3620E).toPoly == usfn3620P)

def usfn3621E : RingExpr := (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 3) (.var 4))))
def usfn3621P : Lean.Grind.CommRing.Poly := (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn3621_norm : (reflectRing usfn3621E).toPoly=usfn3621P := by
  exact eq_of_beq (by decide : (reflectRing usfn3621E).toPoly == usfn3621P)

def usfn3622E : RingExpr := (.mul (.int 8) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.pow (.var 4) 2))))))
def usfn3622P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn3622_norm : (reflectRing usfn3622E).toPoly=usfn3622P := by
  exact eq_of_beq (by decide : (reflectRing usfn3622E).toPoly == usfn3622P)

def usfn3623E : RingExpr := (.mul (.int (-16)) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))
def usfn3623P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn3623_norm : (reflectRing usfn3623E).toPoly=usfn3623P := by
  exact eq_of_beq (by decide : (reflectRing usfn3623E).toPoly == usfn3623P)

def usfn3624E : RingExpr := (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))))
def usfn3624P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn3624_norm : (reflectRing usfn3624E).toPoly=usfn3624P := by
  exact eq_of_beq (by decide : (reflectRing usfn3624E).toPoly == usfn3624P)

def usfn3625E : RingExpr := (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.mul (.int 32) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4)))))))))))
def usfn3625P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn3625_norm : (reflectRing usfn3625E).toPoly=usfn3625P := by
  exact eq_of_beq (by decide : (reflectRing usfn3625E).toPoly == usfn3625P)

def usfn3626E : RingExpr := (.add usfn3624E usfn3625E)
def usfn3626P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn3626_norm : (reflectRing usfn3626E).toPoly=usfn3626P := by
  change (reflectRing usfn3624E).toPoly.combine (reflectRing usfn3625E).toPoly=usfn3626P
  rw [usfn3624_norm, usfn3625_norm]
  exact eq_of_beq (by decide : usfn3624P.combine usfn3625P == usfn3626P)

def usfn3627E : RingExpr := (.add usfn3623E usfn3626E)
def usfn3627P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn3627_norm : (reflectRing usfn3627E).toPoly=usfn3627P := by
  change (reflectRing usfn3623E).toPoly.combine (reflectRing usfn3626E).toPoly=usfn3627P
  rw [usfn3623_norm, usfn3626_norm]
  exact eq_of_beq (by decide : usfn3623P.combine usfn3626P == usfn3627P)

def usfn3628E : RingExpr := (.add usfn3622E usfn3627E)
def usfn3628P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn3628_norm : (reflectRing usfn3628E).toPoly=usfn3628P := by
  change (reflectRing usfn3622E).toPoly.combine (reflectRing usfn3627E).toPoly=usfn3628P
  rw [usfn3622_norm, usfn3627_norm]
  exact eq_of_beq (by decide : usfn3622P.combine usfn3627P == usfn3628P)

def usfn3629E : RingExpr := (.add usfn3621E usfn3628E)
def usfn3629P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))
theorem usfn3629_norm : (reflectRing usfn3629E).toPoly=usfn3629P := by
  change (reflectRing usfn3621E).toPoly.combine (reflectRing usfn3628E).toPoly=usfn3629P
  rw [usfn3621_norm, usfn3628_norm]
  exact eq_of_beq (by decide : usfn3621P.combine usfn3628P == usfn3629P)

def usfn3630E : RingExpr := (.add usfn3620E usfn3629E)
def usfn3630P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))
theorem usfn3630_norm : (reflectRing usfn3630E).toPoly=usfn3630P := by
  change (reflectRing usfn3620E).toPoly.combine (reflectRing usfn3629E).toPoly=usfn3630P
  rw [usfn3620_norm, usfn3629_norm]
  exact eq_of_beq (by decide : usfn3620P.combine usfn3629P == usfn3630P)

def usfn3631E : RingExpr := (.add usfn3619E usfn3630E)
def usfn3631P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))
theorem usfn3631_norm : (reflectRing usfn3631E).toPoly=usfn3631P := by
  change (reflectRing usfn3619E).toPoly.combine (reflectRing usfn3630E).toPoly=usfn3631P
  rw [usfn3619_norm, usfn3630_norm]
  exact eq_of_beq (by decide : usfn3619P.combine usfn3630P == usfn3631P)

def usfn3632E : RingExpr := (.add usfn3618E usfn3631E)
def usfn3632P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit)) (.num (0)))))))))))))
theorem usfn3632_norm : (reflectRing usfn3632E).toPoly=usfn3632P := by
  change (reflectRing usfn3618E).toPoly.combine (reflectRing usfn3631E).toPoly=usfn3632P
  rw [usfn3618_norm, usfn3631_norm]
  exact eq_of_beq (by decide : usfn3618P.combine usfn3631P == usfn3632P)

def usfn3633E : RingExpr := (.mul usfn133E usfn3632E)
def usfn3633P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ .unit))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.num (0)))))))))))))
theorem usfn3633_norm : (reflectRing usfn3633E).toPoly=usfn3633P := by
  change (reflectRing usfn133E).toPoly.mul (reflectRing usfn3632E).toPoly=usfn3633P
  rw [usfn133_norm, usfn3632_norm]
  exact eq_of_beq (by decide : usfn133P.mul usfn3632P == usfn3633P)

def usfn3634E : RingExpr := (.mul usfn102E usfn3633E)
def usfn3634P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit)))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0)))))))))))))
theorem usfn3634_norm : (reflectRing usfn3634E).toPoly=usfn3634P := by
  change (reflectRing usfn102E).toPoly.mul (reflectRing usfn3633E).toPoly=usfn3634P
  rw [usfn102_norm, usfn3633_norm]
  exact eq_of_beq (by decide : usfn102P.mul usfn3633P == usfn3634P)

def usfn3635E : RingExpr := (.mul usfn3E usfn3634E)
def usfn3635P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-6) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))))))))))))
theorem usfn3635_norm : (reflectRing usfn3635E).toPoly=usfn3635P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn3634E).toPoly=usfn3635P
  rw [usfn3_norm, usfn3634_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn3634P == usfn3635P)

def usfn3636E : RingExpr := (.mul usfn382E usfn3635E)
def usfn3636P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-16) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))))))))))))
theorem usfn3636_norm : (reflectRing usfn3636E).toPoly=usfn3636P := by
  change (reflectRing usfn382E).toPoly.mul (reflectRing usfn3635E).toPoly=usfn3636P
  rw [usfn382_norm, usfn3635_norm]
  exact eq_of_beq (by decide : usfn382P.mul usfn3635P == usfn3636P)

def usfn3637E : RingExpr := (.mul usfn1E usfn3636E)
def usfn3637P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-16) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (1) (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (1) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))))))
theorem usfn3637_norm : (reflectRing usfn3637E).toPoly=usfn3637P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3636E).toPoly=usfn3637P
  rw [usfn1_norm, usfn3636_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3636P == usfn3637P)

def usfn3638E : RingExpr := (.mul usfn3177E usfn3637E)
def usfn3638P : Lean.Grind.CommRing.Poly := (.add (96) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-48) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-12) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-18) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (3) (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (3) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))))))
theorem usfn3638_norm : (reflectRing usfn3638E).toPoly=usfn3638P := by
  change (reflectRing usfn3177E).toPoly.mul (reflectRing usfn3637E).toPoly=usfn3638P
  rw [usfn3177_norm, usfn3637_norm]
  exact eq_of_beq (by decide : usfn3177P.mul usfn3637P == usfn3638P)

def usfn3639E : RingExpr := (.mul usfn3617E usfn3638E)
def usfn3639P : Lean.Grind.CommRing.Poly := (.add (96) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (-48) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))))) (.add (-6) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-12) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))))) (.add (-18) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (3) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (3) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))))) (.num (0)))))))))))))
theorem usfn3639_norm : (reflectRing usfn3639E).toPoly=usfn3639P := by
  change (reflectRing usfn3617E).toPoly.mul (reflectRing usfn3638E).toPoly=usfn3639P
  rw [usfn3617_norm, usfn3638_norm]
  exact eq_of_beq (by decide : usfn3617P.mul usfn3638P == usfn3639P)

def usfn3640E : RingExpr := (.mul (.mul (.var 5) (.pow (.var 1) 2)) (.mul (.int (-4)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def usfn3640P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (4) (.mult ⟨1,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.num (0))))
theorem usfn3640_norm : (reflectRing usfn3640E).toPoly=usfn3640P := by
  exact eq_of_beq (by decide : (reflectRing usfn3640E).toPoly == usfn3640P)

def usfn3641E : RingExpr := (.pow (.var 1) 2)
def usfn3641P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,2⟩ .unit) (.num (0)))
theorem usfn3641_norm : (reflectRing usfn3641E).toPoly=usfn3641P := by
  exact eq_of_beq (by decide : (reflectRing usfn3641E).toPoly == usfn3641P)

def usfn3642E : RingExpr := (.mul (.int (-1)) (.var 10))
def usfn3642P : Lean.Grind.CommRing.Poly := (.add (-1) (.mult ⟨10,1⟩ .unit) (.num (0)))
theorem usfn3642_norm : (reflectRing usfn3642E).toPoly=usfn3642P := by
  exact eq_of_beq (by decide : (reflectRing usfn3642E).toPoly == usfn3642P)

def usfn3643E : RingExpr := (.mul (.int (-2)) (.mul (.var 3) (.pow (.var 4) 2)))
def usfn3643P : Lean.Grind.CommRing.Poly := (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.num (0)))
theorem usfn3643_norm : (reflectRing usfn3643E).toPoly=usfn3643P := by
  exact eq_of_beq (by decide : (reflectRing usfn3643E).toPoly == usfn3643P)

def usfn3644E : RingExpr := (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 16) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4))))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))
def usfn3644P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))
theorem usfn3644_norm : (reflectRing usfn3644E).toPoly=usfn3644P := by
  exact eq_of_beq (by decide : (reflectRing usfn3644E).toPoly == usfn3644P)

def usfn3645E : RingExpr := (.add usfn426E usfn3644E)
def usfn3645P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))
theorem usfn3645_norm : (reflectRing usfn3645E).toPoly=usfn3645P := by
  change (reflectRing usfn426E).toPoly.combine (reflectRing usfn3644E).toPoly=usfn3645P
  rw [usfn426_norm, usfn3644_norm]
  exact eq_of_beq (by decide : usfn426P.combine usfn3644P == usfn3645P)

def usfn3646E : RingExpr := (.add usfn843E usfn3645E)
def usfn3646P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))
theorem usfn3646_norm : (reflectRing usfn3646E).toPoly=usfn3646P := by
  change (reflectRing usfn843E).toPoly.combine (reflectRing usfn3645E).toPoly=usfn3646P
  rw [usfn843_norm, usfn3645_norm]
  exact eq_of_beq (by decide : usfn843P.combine usfn3645P == usfn3646P)

def usfn3647E : RingExpr := (.add usfn3643E usfn3646E)
def usfn3647P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.num (0)))))))))
theorem usfn3647_norm : (reflectRing usfn3647E).toPoly=usfn3647P := by
  change (reflectRing usfn3643E).toPoly.combine (reflectRing usfn3646E).toPoly=usfn3647P
  rw [usfn3643_norm, usfn3646_norm]
  exact eq_of_beq (by decide : usfn3643P.combine usfn3646P == usfn3647P)

def usfn3648E : RingExpr := (.add usfn3642E usfn3647E)
def usfn3648P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.add (-1) (.mult ⟨10,1⟩ .unit) (.num (0))))))))))
theorem usfn3648_norm : (reflectRing usfn3648E).toPoly=usfn3648P := by
  change (reflectRing usfn3642E).toPoly.combine (reflectRing usfn3647E).toPoly=usfn3648P
  rw [usfn3642_norm, usfn3647_norm]
  exact eq_of_beq (by decide : usfn3642P.combine usfn3647P == usfn3648P)

def usfn3649E : RingExpr := (.mul usfn133E usfn3648E)
def usfn3649P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (-1) (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)) (.num (0))))))))))
theorem usfn3649_norm : (reflectRing usfn3649E).toPoly=usfn3649P := by
  change (reflectRing usfn133E).toPoly.mul (reflectRing usfn3648E).toPoly=usfn3649P
  rw [usfn133_norm, usfn3648_norm]
  exact eq_of_beq (by decide : usfn133P.mul usfn3648P == usfn3649P)

def usfn3650E : RingExpr := (.mul usfn409E usfn3649E)
def usfn3650P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))
theorem usfn3650_norm : (reflectRing usfn3650E).toPoly=usfn3650P := by
  change (reflectRing usfn409E).toPoly.mul (reflectRing usfn3649E).toPoly=usfn3650P
  rw [usfn409_norm, usfn3649_norm]
  exact eq_of_beq (by decide : usfn409P.mul usfn3649P == usfn3650P)

def usfn3651E : RingExpr := (.mul usfn102E usfn3650E)
def usfn3651P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (16) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit))) (.num (0))))))))))
theorem usfn3651_norm : (reflectRing usfn3651E).toPoly=usfn3651P := by
  change (reflectRing usfn102E).toPoly.mul (reflectRing usfn3650E).toPoly=usfn3651P
  rw [usfn102_norm, usfn3650_norm]
  exact eq_of_beq (by decide : usfn102P.mul usfn3650P == usfn3651P)

def usfn3652E : RingExpr := (.mul usfn3E usfn3651E)
def usfn3652P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (16) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))) (.num (0))))))))))
theorem usfn3652_norm : (reflectRing usfn3652E).toPoly=usfn3652P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn3651E).toPoly=usfn3652P
  rw [usfn3_norm, usfn3651_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn3651P == usfn3652P)

def usfn3653E : RingExpr := (.mul usfn1E usfn3652E)
def usfn3653P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (16) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-1) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0))))))))))
theorem usfn3653_norm : (reflectRing usfn3653E).toPoly=usfn3653P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3652E).toPoly=usfn3653P
  rw [usfn1_norm, usfn3652_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3652P == usfn3653P)

def usfn3654E : RingExpr := (.mul usfn3177E usfn3653E)
def usfn3654P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (48) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (12) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-24) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-6) (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-6) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-3) (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.num (0))))))))))
theorem usfn3654_norm : (reflectRing usfn3654E).toPoly=usfn3654P := by
  change (reflectRing usfn3177E).toPoly.mul (reflectRing usfn3653E).toPoly=usfn3654P
  rw [usfn3177_norm, usfn3653_norm]
  exact eq_of_beq (by decide : usfn3177P.mul usfn3653P == usfn3654P)

def usfn3655E : RingExpr := (.mul usfn3641E usfn3654E)
def usfn3655P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (48) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (6) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (12) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-24) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨1,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-6) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-3) (.mult ⟨1,2⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.num (0))))))))))
theorem usfn3655_norm : (reflectRing usfn3655E).toPoly=usfn3655P := by
  change (reflectRing usfn3641E).toPoly.mul (reflectRing usfn3654E).toPoly=usfn3655P
  rw [usfn3641_norm, usfn3654_norm]
  exact eq_of_beq (by decide : usfn3641P.mul usfn3654P == usfn3655P)

def usfn3656E : RingExpr := (.mul (.mul (.var 1) (.pow (.var 2) 5)) (.mul (.int 24) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def usfn3656P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,5⟩ (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (-24) (.mult ⟨1,1⟩ (.mult ⟨2,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.num (0))))
theorem usfn3656_norm : (reflectRing usfn3656E).toPoly=usfn3656P := by
  exact eq_of_beq (by decide : (reflectRing usfn3656E).toPoly == usfn3656P)

def usfn3657E : RingExpr := (.mul (.mul (.var 5) (.mul (.var 1) (.pow (.var 2) 4))) (.mul (.int 8) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))
def usfn3657P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.num (0))))
theorem usfn3657_norm : (reflectRing usfn3657E).toPoly=usfn3657P := by
  exact eq_of_beq (by decide : (reflectRing usfn3657E).toPoly == usfn3657P)

def usfn3658E : RingExpr := (.mul (.var 1) (.pow (.var 2) 4))
def usfn3658P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ .unit)) (.num (0)))
theorem usfn3658_norm : (reflectRing usfn3658E).toPoly=usfn3658P := by
  exact eq_of_beq (by decide : (reflectRing usfn3658E).toPoly == usfn3658P)

def usfn3659E : RingExpr := (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.var 7) (.mul (.var 10) (.var 8))) (.add (.mul (.int 4) (.mul (.var 10) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))) (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))))))))))))
def usfn3659P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit)))) (.add (1) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0))))))))
theorem usfn3659_norm : (reflectRing usfn3659E).toPoly=usfn3659P := by
  exact eq_of_beq (by decide : (reflectRing usfn3659E).toPoly == usfn3659P)

def usfn3660E : RingExpr := (.mul usfn3E usfn3659E)
def usfn3660P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (1) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0))))))))
theorem usfn3660_norm : (reflectRing usfn3660E).toPoly=usfn3660P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn3659E).toPoly=usfn3660P
  rw [usfn3_norm, usfn3659_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn3659P == usfn3660P)

def usfn3661E : RingExpr := (.mul usfn1E usfn3660E)
def usfn3661P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (1) (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn3661_norm : (reflectRing usfn3661E).toPoly=usfn3661P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn3660E).toPoly=usfn3661P
  rw [usfn1_norm, usfn3660_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn3660P == usfn3661P)

def usfn3662E : RingExpr := (.mul usfn3603E usfn3661E)
def usfn3662P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-48) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-12) (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))) (.add (24) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))))
theorem usfn3662_norm : (reflectRing usfn3662E).toPoly=usfn3662P := by
  change (reflectRing usfn3603E).toPoly.mul (reflectRing usfn3661E).toPoly=usfn3662P
  rw [usfn3603_norm, usfn3661_norm]
  exact eq_of_beq (by decide : usfn3603P.mul usfn3661P == usfn3662P)

def usfn3663E : RingExpr := (.mul usfn3658E usfn3662E)
def usfn3663P : Lean.Grind.CommRing.Poly := (.add (-96) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))))) (.add (-48) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.add (-12) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (24) (.mult ⟨1,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))))) (.num (0))))))))
theorem usfn3663_norm : (reflectRing usfn3663E).toPoly=usfn3663P := by
  change (reflectRing usfn3658E).toPoly.mul (reflectRing usfn3662E).toPoly=usfn3663P
  rw [usfn3658_norm, usfn3662_norm]
  exact eq_of_beq (by decide : usfn3658P.mul usfn3662P == usfn3663P)

def usfn3664E : RingExpr := (.mul (.mul (.var 5) (.mul (.var 1) (.pow (.var 2) 3))) (.mul (.int (-8)) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.add (.int (-1)) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))
def usfn3664P : Lean.Grind.CommRing.Poly := (.add (-32) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit)))))))))) (.add (16) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,6⟩ (.mult ⟨9,2⟩ (.mult ⟨10,4⟩ .unit))))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))))) (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,3⟩ .unit)))))))) (.num (0))))))
theorem usfn3664_norm : (reflectRing usfn3664E).toPoly=usfn3664P := by
  exact eq_of_beq (by decide : (reflectRing usfn3664E).toPoly == usfn3664P)

def usfn3665E : RingExpr := (.mul (.var 1) (.pow (.var 2) 3))
def usfn3665P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ .unit)) (.num (0)))
theorem usfn3665_norm : (reflectRing usfn3665E).toPoly=usfn3665P := by
  exact eq_of_beq (by decide : (reflectRing usfn3665E).toPoly == usfn3665P)

def usfn3666E : RingExpr := (.int 6)
def usfn3666P : Lean.Grind.CommRing.Poly := (.num (6))
theorem usfn3666_norm : (reflectRing usfn3666E).toPoly=usfn3666P := by
  exact eq_of_beq (by decide : (reflectRing usfn3666E).toPoly == usfn3666P)

def usfn3667E : RingExpr := (.mul (.int 4) (.mul (.var 3) (.var 4)))
def usfn3667P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit)) (.num (0)))
theorem usfn3667_norm : (reflectRing usfn3667E).toPoly=usfn3667P := by
  exact eq_of_beq (by decide : (reflectRing usfn3667E).toPoly == usfn3667P)

def usfn3668E : RingExpr := (.mul (.int (-14)) (.mul (.var 10) (.mul (.var 3) (.var 4))))
def usfn3668P : Lean.Grind.CommRing.Poly := (.add (-14) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn3668_norm : (reflectRing usfn3668E).toPoly=usfn3668P := by
  exact eq_of_beq (by decide : (reflectRing usfn3668E).toPoly == usfn3668P)

def usfn3669E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))
def usfn3669P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem usfn3669_norm : (reflectRing usfn3669E).toPoly=usfn3669P := by
  exact eq_of_beq (by decide : (reflectRing usfn3669E).toPoly == usfn3669P)

def usfn3670E : RingExpr := (.mul (.int 8) (.mul (.var 0) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))
def usfn3670P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0)))
theorem usfn3670_norm : (reflectRing usfn3670E).toPoly=usfn3670P := by
  exact eq_of_beq (by decide : (reflectRing usfn3670E).toPoly == usfn3670P)

def usfn3671E : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))))
def usfn3671P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn3671_norm : (reflectRing usfn3671E).toPoly=usfn3671P := by
  exact eq_of_beq (by decide : (reflectRing usfn3671E).toPoly == usfn3671P)

def usfn3672E : RingExpr := (.add (.mul (.int (-2)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.mul (.int 8) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))))))
def usfn3672P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn3672_norm : (reflectRing usfn3672E).toPoly=usfn3672P := by
  exact eq_of_beq (by decide : (reflectRing usfn3672E).toPoly == usfn3672P)

def usfn3673E : RingExpr := (.add usfn3671E usfn3672E)
def usfn3673P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn3673_norm : (reflectRing usfn3673E).toPoly=usfn3673P := by
  change (reflectRing usfn3671E).toPoly.combine (reflectRing usfn3672E).toPoly=usfn3673P
  rw [usfn3671_norm, usfn3672_norm]
  exact eq_of_beq (by decide : usfn3671P.combine usfn3672P == usfn3673P)

def usfn3674E : RingExpr := (.add usfn3623E usfn3673E)
def usfn3674P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn3674_norm : (reflectRing usfn3674E).toPoly=usfn3674P := by
  change (reflectRing usfn3623E).toPoly.combine (reflectRing usfn3673E).toPoly=usfn3674P
  rw [usfn3623_norm, usfn3673_norm]
  exact eq_of_beq (by decide : usfn3623P.combine usfn3673P == usfn3674P)

def usfn3675E : RingExpr := (.add usfn3622E usfn3674E)
def usfn3675P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))
theorem usfn3675_norm : (reflectRing usfn3675E).toPoly=usfn3675P := by
  change (reflectRing usfn3622E).toPoly.combine (reflectRing usfn3674E).toPoly=usfn3675P
  rw [usfn3622_norm, usfn3674_norm]
  exact eq_of_beq (by decide : usfn3622P.combine usfn3674P == usfn3675P)

def usfn3676E : RingExpr := (.add usfn3670E usfn3675E)
def usfn3676P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))
theorem usfn3676_norm : (reflectRing usfn3676E).toPoly=usfn3676P := by
  change (reflectRing usfn3670E).toPoly.combine (reflectRing usfn3675E).toPoly=usfn3676P
  rw [usfn3670_norm, usfn3675_norm]
  exact eq_of_beq (by decide : usfn3670P.combine usfn3675P == usfn3676P)

def usfn3677E : RingExpr := (.add usfn3669E usfn3676E)
def usfn3677P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))
theorem usfn3677_norm : (reflectRing usfn3677E).toPoly=usfn3677P := by
  change (reflectRing usfn3669E).toPoly.combine (reflectRing usfn3676E).toPoly=usfn3677P
  rw [usfn3669_norm, usfn3676_norm]
  exact eq_of_beq (by decide : usfn3669P.combine usfn3676P == usfn3677P)

def usfn3678E : RingExpr := (.add usfn3668E usfn3677E)
def usfn3678P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-14) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))
theorem usfn3678_norm : (reflectRing usfn3678E).toPoly=usfn3678P := by
  change (reflectRing usfn3668E).toPoly.combine (reflectRing usfn3677E).toPoly=usfn3678P
  rw [usfn3668_norm, usfn3677_norm]
  exact eq_of_beq (by decide : usfn3668P.combine usfn3677P == usfn3678P)

def usfn3679E : RingExpr := (.add usfn3620E usfn3678E)
def usfn3679P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-14) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))))
theorem usfn3679_norm : (reflectRing usfn3679E).toPoly=usfn3679P := by
  change (reflectRing usfn3620E).toPoly.combine (reflectRing usfn3678E).toPoly=usfn3679P
  rw [usfn3620_norm, usfn3678_norm]
  exact eq_of_beq (by decide : usfn3620P.combine usfn3678P == usfn3679P)

def usfn3680E : RingExpr := (.add usfn3667E usfn3679E)
def usfn3680P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-14) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit)) (.num (0))))))))))))))
theorem usfn3680_norm : (reflectRing usfn3680E).toPoly=usfn3680P := by
  change (reflectRing usfn3667E).toPoly.combine (reflectRing usfn3679E).toPoly=usfn3680P
  rw [usfn3667_norm, usfn3679_norm]
  exact eq_of_beq (by decide : usfn3667P.combine usfn3679P == usfn3680P)

def usfn3681E : RingExpr := (.mul usfn133E usfn3680E)
def usfn3681P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ .unit)))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-14) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ .unit))) (.num (0))))))))))))))
theorem usfn3681_norm : (reflectRing usfn3681E).toPoly=usfn3681P := by
  change (reflectRing usfn133E).toPoly.mul (reflectRing usfn3680E).toPoly=usfn3681P
  rw [usfn133_norm, usfn3680_norm]
  exact eq_of_beq (by decide : usfn133P.mul usfn3680P == usfn3681P)

def usfn3682E : RingExpr := (.mul usfn102E usfn3681E)
def usfn3682P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (-2) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,6⟩ (.mult ⟨9,1⟩ (.mult ⟨10,4⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))))) (.add (-14) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,3⟩ .unit)))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,3⟩ .unit))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,2⟩ .unit)))) (.num (0))))))))))))))
theorem usfn3682_norm : (reflectRing usfn3682E).toPoly=usfn3682P := by
  change (reflectRing usfn102E).toPoly.mul (reflectRing usfn3681E).toPoly=usfn3682P
  rw [usfn102_norm, usfn3681_norm]
  exact eq_of_beq (by decide : usfn102P.mul usfn3681P == usfn3682P)

#print axioms usfn3682_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
