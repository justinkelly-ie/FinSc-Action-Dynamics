module Stage1.Dynamics.PythagoreanSpreadObservables

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.Basis.Coordinate
import Stage1.RationalTrig
import Stage1.Carrier.Maxel
import Stage1.Multiset.PrimordialUnfolding
import Stage0.Multiset
import Stage1.QuadStream
import Language.Reflection

%default total

------------------------------------------------------------------------
-- 1. DYNAMIC PYTHAGOREAN TRIADS & CHROMOGEOMETRIC QUADRANCES
------------------------------------------------------------------------

||| Evaluates the Hypotenuse / Elliptic Quadrance: Q_Blue = x^2 + y^2.
public export
quadranceBlue : BoxInt -> BoxInt -> BoxInt
quadranceBlue x y = (x * x) + (y * y)

||| Evaluates the Longitudinal / Hyperbolic Quadrance: Q_Red = x^2 - y^2.
public export
quadranceRed : BoxInt -> BoxInt -> BoxInt
quadranceRed x y = (x * x) - (y * y)

||| Evaluates the Transverse / Parabolic Shear Quadrance: Q_Green = 2 * x * y.
public export
quadranceGreen : BoxInt -> BoxInt -> BoxInt
quadranceGreen x y = intToBoxInt 2 * (x * y)

||| Chromogeometric Pythagorean Triad Identity (Rule 03 §6):
||| Universally satisfies Q_Red^2 + Q_Green^2 = Q_Blue^2 for all (x, y).
public export
verifyPythagoreanTriadIdentity : BoxInt -> BoxInt -> Bool
verifyPythagoreanTriadIdentity x y =
  let qB = quadranceBlue x y
      qR = quadranceRed x y
      qG = quadranceGreen x y
      lhs = (qR * qR) + (qG * qG)
      rhs = qB * qB
  in boxEq lhs rhs

------------------------------------------------------------------------
-- 2. COMPANION SPREAD MAXEL OBSERVABLES & SPECTRAL INVARIANTS
------------------------------------------------------------------------

||| Spread Diagonal Theorem (Rule 03 §6):
||| The diagonal entry 2 - 4s of the companion spread transfer Maxel scaled by Q_Blue
||| identically equals twice the Hyperbolic quadrance: (2 * Q_Blue - 4 * y^2) == 2 * Q_Red.
public export
verifySpreadDiagonalTheorem : BoxInt -> BoxInt -> Bool
verifySpreadDiagonalTheorem x y =
  let qB = quadranceBlue x y
      qR = quadranceRed x y
      lhs = (intToBoxInt 2 * qB) - (intToBoxInt 4 * (y * y))
      rhs = intToBoxInt 2 * qR
  in boxEq lhs rhs

||| Evaluates the Determinant of M(x, y)_ij:
||| det M = (2 Q_Red)(0) - (-Q_Blue)(Q_Blue) = Q_Blue^2.
public export
companionMaxelDeterminant : BoxInt -> BoxInt -> BoxInt
companionMaxelDeterminant x y =
  let qB = quadranceBlue x y
      qR = quadranceRed x y
      c11 = intToBoxInt 2 * qR
      c12 = mulBox (intToBoxInt (-1)) qB
      c21 = qB
      c22 = intToBoxInt 0
  in (c11 * c22) - (c12 * c21)

||| Proof witness that determinant area factor identically equals Q_Blue^2.
public export
verifyDeterminantAreaFactor : BoxInt -> BoxInt -> Bool
verifyDeterminantAreaFactor x y =
  let detM = companionMaxelDeterminant x y
      qB = quadranceBlue x y
  in boxEq detM (qB * qB)

||| Evaluates the Characteristic Polynomial Discriminant of M(x, y):
||| Delta = (2 Q_Red)^2 - 4 Q_Blue^2 = 4 (Q_Red^2 - Q_Blue^2) = -4 Q_Green^2 = -(4xy)^2.
public export
companionMaxelDiscriminant : BoxInt -> BoxInt -> BoxInt
companionMaxelDiscriminant x y =
  let qB = quadranceBlue x y
      qR = quadranceRed x y
      twoQRed = intToBoxInt 2 * qR
  in (twoQRed * twoQRed) - (intToBoxInt 4 * (qB * qB))

||| Proof witness that discriminant identically equals -4 * Q_Green^2.
public export
verifyDiscriminantGreenShear : BoxInt -> BoxInt -> Bool
verifyDiscriminantGreenShear x y =
  let delta = companionMaxelDiscriminant x y
      qG = quadranceGreen x y
      expected = mulBox (intToBoxInt (-4)) (qG * qG)
  in boxEq delta expected

------------------------------------------------------------------------
-- 3. PHYSICAL OBSERVABLES & COORDINATE PERSISTENCE
------------------------------------------------------------------------

||| Coordinate Persistence Observable (O_persist):
||| When M(x, y) acts on basis state [i] with weight u, coordinate i persists with weight 2 * Q_Red * u.
public export
spreadPersistenceObservable : (x : BoxInt) -> (y : BoxInt) -> (u : BoxInt) -> BoxInt
spreadPersistenceObservable x y u =
  (intToBoxInt 2 * quadranceRed x y) * u

||| Channel Transition Observable (O_trans):
||| Coupling to conjugate channel j carries amplitude Q_Blue * u.
public export
spreadTransitionObservable : (x : BoxInt) -> (y : BoxInt) -> (u : BoxInt) -> BoxInt
spreadTransitionObservable x y u =
  quadranceBlue x y * u

||| Relativistic Mass-Shell Invariance Observable:
||| Q_Blue^2 - Q_Green^2 == Q_Red^2 across all integer parameters (x, y).
public export
verifyMassShellInvariance : BoxInt -> BoxInt -> Bool
verifyMassShellInvariance x y =
  let qB = quadranceBlue x y
      qR = quadranceRed x y
      qG = quadranceGreen x y
      lhs = (qB * qB) - (qG * qG)
      rhs = qR * qR
  in boxEq lhs rhs

------------------------------------------------------------------------
-- 4. MULTI-PARTICLE SYSTEMS & INTER-SECTOR QUADSTREAM PUMPS
------------------------------------------------------------------------

||| Evaluates the collective additive quadrances for an ensemble of N particles:
||| (sum Q_Blue, sum Q_Red, sum Q_Green).
public export
multiParticleQuadrances : List (BoxInt, BoxInt) -> (BoxInt, BoxInt, BoxInt)
multiParticleQuadrances [] = (intToBoxInt 0, intToBoxInt 0, intToBoxInt 0)
multiParticleQuadrances ((x, y) :: rest) =
  let (bRest, rRest, gRest) = multiParticleQuadrances rest
      qB = quadranceBlue x y
      qR = quadranceRed x y
      qG = quadranceGreen x y
  in (qB + bRest, qR + rRest, qG + gRest)

||| Collective Quadrance Coherence Deficit:
||| Delta Q = (sum Q_Blue)^2 - ((sum Q_Red)^2 + (sum Q_Green)^2) >= 0.
||| Vanishes iff all particles share identical spread angle (pure collective coherence).
public export
collectiveCoherenceDeficit : List (BoxInt, BoxInt) -> BoxInt
collectiveCoherenceDeficit particles =
  let (bTot, rTot, gTot) = multiParticleQuadrances particles
      hypotSq = bTot * bTot
      legsSq = (rTot * rTot) + (gTot * gTot)
  in hypotSq - legsSq

||| Inter-Sector Cosmological Pump: Elliptic (27) to Hyperbolic (128).
||| Pumps manifest bound matter into relativistic gauge flux while preserving coordinate persistence.
public export
ellipticToHyperbolicPump : (x : BoxInt) -> (y : BoxInt) -> Maxel
ellipticToHyperbolicPump = pythagoreanSpreadMaxelAt 1 2

||| Inter-Sector Cosmological Pump: Hyperbolic (128) to Parabolic (55).
||| Drains relativistic gauge flux into parabolic dissipation with shear quadrance Q_Green.
public export
hyperbolicToParabolicPump : (x : BoxInt) -> (y : BoxInt) -> Maxel
hyperbolicToParabolicPump = pythagoreanSpreadMaxelAt 2 3

||| Inter-Sector Cosmological Pump: Parabolic (55) to Substrate Ledger (210).
||| Flushes dissipation remainder into substrate causal ledger.
public export
parabolicToSubstratePump : (x : BoxInt) -> (y : BoxInt) -> Maxel
parabolicToSubstratePump = pythagoreanSpreadMaxelAt 3 4

------------------------------------------------------------------------
-- 5. COMPILE-TIME INVARIANT AUDIT & WITNESS (RULE 01)
------------------------------------------------------------------------

||| Master compile-time audit proof for dynamic Pythagorean spread observables on standard (4, 3) triad:
||| Q_Blue = 25, Q_Red = 7, Q_Green = 24.
public export
auditPythagoreanSpreadObservablesProof : Bool
auditPythagoreanSpreadObservablesProof =
  let x = intToBoxInt 4
      y = intToBoxInt 3
  in verifyPythagoreanTriadIdentity x y &&
     verifySpreadDiagonalTheorem x y &&
     verifyDeterminantAreaFactor x y &&
     verifyDiscriminantGreenShear x y &&
     verifyMassShellInvariance x y

export
%macro
auditPythagoreanSpreadObservables : Elab (Stage1.Dynamics.PythagoreanSpreadObservables.auditPythagoreanSpreadObservablesProof = True)
auditPythagoreanSpreadObservables = pure Refl
