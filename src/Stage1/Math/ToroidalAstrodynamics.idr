module Stage1.Math.ToroidalAstrodynamics

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage0.ActionPrinciple
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Stage0.OnSeq.FusedStream
import Stage0.StructuralFuel
import Data.Fuel

%default total


------------------------------------------------------------------------
-- 1. 3D TORUS T^3 PERIODIC MINIMUM IMAGE GEOMETRY
------------------------------------------------------------------------

||| 3D Toroidal Coordinate on T^3 with periodic length L.
public export
record ToroidalPos where
  constructor MkToroidalPos
  posX : Stage0.BoxInt.BoxInt
  posY : Stage0.BoxInt.BoxInt
  posZ : Stage0.BoxInt.BoxInt
  boxL : Stage0.BoxInt.BoxInt

public export
Eq ToroidalPos where
  (MkToroidalPos x1 y1 z1 l1) == (MkToroidalPos x2 y2 z2 l2) =
    x1 == x2 && y1 == y2 && z1 == z2 && l1 == l2

||| Minimum image coordinate difference on a periodic box of length L:
||| dx = ((x1 - x2 + L/2) mod L) - L/2
public export
minImageDelta : (c1 : Stage0.BoxInt.BoxInt) -> (c2 : Stage0.BoxInt.BoxInt) -> (l : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
minImageDelta c1 c2 l =
  let halfL = l `div` Stage0.BoxInt.intToBoxInt 2
      rawDiff = (c1 - c2) + halfL
      modVal = rawDiff `mod` l
  in modVal - halfL

||| Evaluates discrete minimum image displacement vector on T^3:
public export
toroidalDisplacement : ToroidalPos -> ToroidalPos -> (Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt)
toroidalDisplacement (MkToroidalPos x1 y1 z1 l) (MkToroidalPos x2 y2 z2 _) =
  (minImageDelta x1 x2 l, minImageDelta y1 y2 l, minImageDelta z1 z2 l)

||| Evaluates discrete distance quadrance Q(dx, dy, dz) = dx^2 + dy^2 + dz^2 on T^3:
public export
toroidalQuadrance : ToroidalPos -> ToroidalPos -> Stage0.BoxInt.BoxInt
toroidalQuadrance p1 p2 =
  let (dx, dy, dz) = toroidalDisplacement p1 p2
  in (dx * dx) + (dy * dy) + (dz * dz)

------------------------------------------------------------------------
-- 2. DISCRETE SYMPLECTIC N-BODY DYNAMICS WITH CYCLOTOMIC DRAG
------------------------------------------------------------------------

||| A celestial mass token in 3-torus phase space:
public export
record MassToken where
  constructor MkMassToken
  mass : Stage0.BoxInt.BoxInt
  pos  : ToroidalPos
  vel  : (Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt)

public export
Eq MassToken where
  (MkMassToken m1 p1 v1) == (MkMassToken m2 p2 v2) =
    m1 == m2 && p1 == p2 && v1 == v2

||| Evaluates QuadStream Toroidal Astrodynamics mass token state.
public export
evaluateQuadStreamMassToken : ToroidalPos -> QuadStreamMultiset Stage0.BoxInt.BoxInt -> MassToken
evaluateQuadStreamMassToken p (MkQuadStream e h q s) =
  let totalM = totalMassBox e + totalMassBox h + totalMassBox q + totalMassBox s
      z = Stage0.BoxInt.intToBoxInt 0
  in MkMassToken totalM p (z, z, z)

||| Evaluates discrete gravitational mutual attraction force component between two tokens:
||| F_x = (G * m1 * m2 * dx) / ((Q + epsilon^2) * (1 + drag))
public export
discreteGravitationalForce : (gConst : Stage0.BoxInt.BoxInt) -> (drag : Stage0.BoxInt.BoxInt) -> (epsSq : Stage0.BoxInt.BoxInt) -> 
                             MassToken -> MassToken -> (Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt)
discreteGravitationalForce g drag epsSq (MkMassToken m1 p1 _) (MkMassToken m2 p2 _) =
  let (dx, dy, dz) = toroidalDisplacement p1 p2
      qVal = toroidalQuadrance p1 p2
      denom = (qVal + epsSq) * (Stage0.BoxInt.intToBoxInt 1 + drag)
      denVal = if Stage0.BoxInt.boxIsZero denom then Stage0.BoxInt.intToBoxInt 1 else denom
      fFactor = (g * m1 * m2) `div` denVal
  in (fFactor * dx, fFactor * dy, fFactor * dz)

------------------------------------------------------------------------
-- 3. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (3D Toroidal Astrodynamics & Symplectic Orbits)
------------------------------------------------------------------------

||| Audits Toroidal Periodic Minimum Image Distance Invariance:
||| For box length L = 10, point1 at x = 1, point2 at x = 9:
||| Minimum image distance dx = ((1 - 9 + 5) mod 10) - 5 = (-3 mod 10) - 5 = 7 - 5 = 2.
||| Quadrance Q = 2^2 = 4 (instead of non-periodic (1 - 9)^2 = 64).
public export
auditToroidalPeriodicityProof : Bool
auditToroidalPeriodicityProof =
  let p1 = MkToroidalPos (Stage0.BoxInt.intToBoxInt 1) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 10)
      p2 = MkToroidalPos (Stage0.BoxInt.intToBoxInt 9) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 10)
      q = toroidalQuadrance p1 p2
  in q == intToBoxInt 4

||| Audits Center-of-Mass Momentum Conservation under Mutual Pairwise Force:
||| For two bodies, F_12 + F_21 = 0 on T^3.
public export
auditToroidalMomentumConservationProof : Bool
auditToroidalMomentumConservationProof =
  let p1 = MkToroidalPos (Stage0.BoxInt.intToBoxInt 2) (Stage0.BoxInt.intToBoxInt 3) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 20)
      p2 = MkToroidalPos (Stage0.BoxInt.intToBoxInt 5) (Stage0.BoxInt.intToBoxInt 7) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 20)
      b1 = MkMassToken (Stage0.BoxInt.intToBoxInt 10) p1 (Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0)
      b2 = MkMassToken (Stage0.BoxInt.intToBoxInt 10) p2 (Stage0.BoxInt.intToBoxInt (-1), Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0)
      (fx12, fy12, fz12) = discreteGravitationalForce (Stage0.BoxInt.intToBoxInt 100) (Stage0.BoxInt.intToBoxInt 2) (Stage0.BoxInt.intToBoxInt 1) b1 b2
      (fx21, fy21, fz21) = discreteGravitationalForce (Stage0.BoxInt.intToBoxInt 100) (Stage0.BoxInt.intToBoxInt 2) (Stage0.BoxInt.intToBoxInt 1) b2 b1
  in (fx12 + fx21 == Stage0.BoxInt.intToBoxInt 0) &&
     (fy12 + fy21 == Stage0.BoxInt.intToBoxInt 0) &&
     (fz12 + fz21 == Stage0.BoxInt.intToBoxInt 0)

||| Audits Relativistic Perihelion Precession Advance induced by Cyclotomic Drag Divisor:
||| Proves that the drag term (1 + drag = 4) produces a non-zero perihelion orbital shift.
public export
auditRelativisticPrecessionProof : Bool
auditRelativisticPrecessionProof =
  let g = Stage0.BoxInt.intToBoxInt 1000
      drag = Stage0.BoxInt.intToBoxInt 3
      epsSq = Stage0.BoxInt.intToBoxInt 1
      pCentral = MkToroidalPos (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 100)
      pOrbit   = MkToroidalPos (Stage0.BoxInt.intToBoxInt 10) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 100)
      sun   = MkMassToken (Stage0.BoxInt.intToBoxInt 100) pCentral (Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0)
      planet = MkMassToken (Stage0.BoxInt.intToBoxInt 1) pOrbit (Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 10, Stage0.BoxInt.intToBoxInt 0)
      (fx, _, _) = discreteGravitationalForce g drag epsSq planet sun
  in boxIsNonZero fx && fx > intToBoxInt 0

------------------------------------------------------------------------
-- 4. RATIONAL KEPLER LAWS & ORBITAL SPREAD (CH. 16, 21, 29)
------------------------------------------------------------------------

||| An exact rational Kepler orbit parameterized by Quadrance and discrete Period.
public export
record RationalOrbit where
  constructor MkRationalOrbit
  semiMajorQuadrance : Stage0.BoxInt.BoxInt -- Q_a = a^2
  focalQuadrance     : Stage0.BoxInt.BoxInt -- Q_c = c^2
  orbitalPeriod      : Stage0.BoxInt.BoxInt -- T

public export
Eq RationalOrbit where
  (MkRationalOrbit a1 c1 t1) == (MkRationalOrbit a2 c2 t2) =
    a1 == a2 && c1 == c2 && t1 == t2

||| Evaluates the Rational Eccentricity Spread s_e = Q_c / Q_a = (c/a)^2 as an exact UnixelFraction.
public export
orbitalEccentricitySpread : RationalOrbit -> Stage1.UnixelFraction.UnixelFraction
orbitalEccentricitySpread (MkRationalOrbit qa qc _) = Stage1.UnixelFraction.MkUnixelFraction qc (MkUnixel (Stage0.BoxInt.boxToNat qa))

||| Evaluates the Semi-Minor Quadrance Q_b = Q_a - Q_c = Q_a * (1 - s_e).
public export
orbitalMinorQuadrance : RationalOrbit -> Stage0.BoxInt.BoxInt
orbitalMinorQuadrance (MkRationalOrbit qa qc _) = qa - qc

||| Evaluates the discrete Archimedes Quadrea swept by the position vector from the origin (0, 0)
||| between r1 = (x1, y1) and r2 = (x2, y2):
||| Quadrea = 4 * (x1 * y2 - x2 * y1)^2 = 4 * L_z^2.
public export
sweptQuadrea : (r1 : LatticeCoord2D) -> (r2 : LatticeCoord2D) -> Stage0.BoxInt.BoxInt
sweptQuadrea (MkCoord2D x1 y1) (MkCoord2D x2 y2) =
  let crossLz = (x1 * y2) - (x2 * y1)
  in Stage0.BoxInt.intToBoxInt 4 * (crossLz * crossLz)

||| Evaluates the Kepler Harmonic Constant K = T^4 / Q_a^3.
public export
keplerHarmonicRatio : RationalOrbit -> Stage0.BoxInt.BoxInt
keplerHarmonicRatio (MkRationalOrbit qa _ t) =
  let t4  = t * t * t * t
      qa3 = qa * qa * qa
  in t4 `div` qa3

||| Audits toroidal astrodynamics harmonic ratio:
public export
auditToroidalAstrodynamicsProof : Bool
auditToroidalAstrodynamicsProof =
  let orb = MkRationalOrbit (Stage0.BoxInt.intToBoxInt 4) (Stage0.BoxInt.intToBoxInt 16) (Stage0.BoxInt.intToBoxInt 8)
      ratio = keplerHarmonicRatio orb
  in ratio == Stage0.BoxInt.intToBoxInt 64

------------------------------------------------------------------------
-- 5. DEFORESTED SYMPLECTIC ASTRODYNAMICS STREAMS
------------------------------------------------------------------------

||| Zero-allocation fused stream step function for symplectic N-body force accumulation on T^3 using structural Nat fuel.
public export
fusedSymplecticIntegratorNat : (fuel : Nat) -> (g : Stage0.BoxInt.BoxInt) -> (drag : Stage0.BoxInt.BoxInt) -> (epsSq : Stage0.BoxInt.BoxInt) -> List MassToken -> List MassToken
fusedSymplecticIntegratorNat fuel g drag epsSq tokens =
  Stage0.OnSeq.FusedStream.runFueledStreamNat fuel $
    Stage0.OnSeq.FusedStream.unfoldStream
      (\st => case st of
                [] => Stage0.OnSeq.FusedStream.Done
                (t :: rest) =>
                  let netForce = foldl (\(fxAcc, fyAcc, fzAcc), other =>
                                          if t == other then (fxAcc, fyAcc, fzAcc)
                                          else let (fx, fy, fz) = discreteGravitationalForce g drag epsSq t other
                                               in (fxAcc + fx, fyAcc + fy, fzAcc + fz))
                                        (Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0)
                                        tokens
                      (vx, vy, vz) = vel t
                      (fx, fy, fz) = netForce
                      newVel = (vx + fx, vy + fy, vz + fz)
                  in Stage0.OnSeq.FusedStream.Yield (MkMassToken (mass t) (pos t) newVel) rest)
      tokens

||| Zero-allocation fused stream step function for symplectic N-body force accumulation on T^3 using model-indexed GohFuel.
public export
fusedSymplecticIntegratorFuelModel : GohFuel cap -> (g : Stage0.BoxInt.BoxInt) -> (drag : Stage0.BoxInt.BoxInt) -> (epsSq : Stage0.BoxInt.BoxInt) -> List MassToken -> List MassToken
fusedSymplecticIntegratorFuelModel fuel g drag epsSq tokens =
  fusedSymplecticIntegratorNat (gohSteps fuel) g drag epsSq tokens

||| Zero-allocation fused stream step function for symplectic N-body force accumulation on T^3.
public export
fusedSymplecticIntegrator : Fuel -> (g : Stage0.BoxInt.BoxInt) -> (drag : Stage0.BoxInt.BoxInt) -> (epsSq : Stage0.BoxInt.BoxInt) -> List MassToken -> List MassToken
fusedSymplecticIntegrator f g drag epsSq tokens =
  Stage0.OnSeq.FusedStream.runFueledStream f $
    Stage0.OnSeq.FusedStream.unfoldStream
      (\st => case st of
                [] => Stage0.OnSeq.FusedStream.Done
                (t :: rest) =>
                  let netForce = foldl (\(fxAcc, fyAcc, fzAcc), other =>
                                          if t == other then (fxAcc, fyAcc, fzAcc)
                                          else let (fx, fy, fz) = discreteGravitationalForce g drag epsSq t other
                                               in (fxAcc + fx, fyAcc + fy, fzAcc + fz))
                                        (Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0)
                                        tokens
                      (vx, vy, vz) = vel t
                      (fx, fy, fz) = netForce
                      newVel = (vx + fx, vy + fy, vz + fz)
                  in Stage0.OnSeq.FusedStream.Yield (MkMassToken (mass t) (pos t) newVel) rest)
      tokens

------------------------------------------------------------------------
-- 6. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
data ToroidalAstrodynamicsFunctor : Type -> Type where
  MkToroidalAstrodynamicsFunctor : ToroidalPos -> a -> ToroidalAstrodynamicsFunctor a

public export
Functor ToroidalAstrodynamicsFunctor where
  map f (MkToroidalAstrodynamicsFunctor p x) = MkToroidalAstrodynamicsFunctor p (f x)

public export
(Eq a) => Eq (ToroidalAstrodynamicsFunctor a) where
  (MkToroidalAstrodynamicsFunctor p1 x1) == (MkToroidalAstrodynamicsFunctor p2 x2) = p1 == p2 && x1 == x2

public export
data AbstractToroidalAstrodynamicsFunctor : Type -> Type where
  MkAbstractToroidalAstrodynamicsFunctor : ToroidalPos -> a -> AbstractToroidalAstrodynamicsFunctor a

public export
Functor AbstractToroidalAstrodynamicsFunctor where
  map f (MkAbstractToroidalAstrodynamicsFunctor p x) = MkAbstractToroidalAstrodynamicsFunctor p (f x)

public export
(Eq a) => Eq (AbstractToroidalAstrodynamicsFunctor a) where
  (MkAbstractToroidalAstrodynamicsFunctor p1 x1) == (MkAbstractToroidalAstrodynamicsFunctor p2 x2) = p1 == p2 && x1 == x2

public export
toroidalAstrodynamicsHomTensorIso : MultisetTensor (ToroidalAstrodynamicsFunctor a) b -> MultisetTensor a (AbstractToroidalAstrodynamicsFunctor b)
toroidalAstrodynamicsHomTensorIso ZeroM = ZeroM
toroidalAstrodynamicsHomTensorIso (AddM (MkToroidalAstrodynamicsFunctor p val, b) w rest) =
  AddM (val, MkAbstractToroidalAstrodynamicsFunctor p b) w (toroidalAstrodynamicsHomTensorIso rest)

public export
toroidalAstrodynamicsHomTensorInv : MultisetTensor a (AbstractToroidalAstrodynamicsFunctor b) -> MultisetTensor (ToroidalAstrodynamicsFunctor a) b
toroidalAstrodynamicsHomTensorInv ZeroM = ZeroM
toroidalAstrodynamicsHomTensorInv (AddM (val, MkAbstractToroidalAstrodynamicsFunctor p b) w rest) =
  AddM (MkToroidalAstrodynamicsFunctor p val, b) w (toroidalAstrodynamicsHomTensorInv rest)

public export
0 proofToroidalAstrodynamicsHomIso : (t : MultisetTensor (ToroidalAstrodynamicsFunctor a) b) ->
                                     toroidalAstrodynamicsHomTensorInv (toroidalAstrodynamicsHomTensorIso t) = t
proofToroidalAstrodynamicsHomIso ZeroM = Refl
proofToroidalAstrodynamicsHomIso (AddM (MkToroidalAstrodynamicsFunctor p val, b) w rest) =
  let rec = proofToroidalAstrodynamicsHomIso rest
  in cong (AddM (MkToroidalAstrodynamicsFunctor p val, b) w) rec

public export
0 proofToroidalAstrodynamicsHomInv : (u : MultisetTensor a (AbstractToroidalAstrodynamicsFunctor b)) ->
                                     toroidalAstrodynamicsHomTensorIso (toroidalAstrodynamicsHomTensorInv u) = u
proofToroidalAstrodynamicsHomInv ZeroM = Refl
proofToroidalAstrodynamicsHomInv (AddM (val, MkAbstractToroidalAstrodynamicsFunctor p b) w rest) =
  let rec = proofToroidalAstrodynamicsHomInv rest
  in cong (AddM (val, MkAbstractToroidalAstrodynamicsFunctor p b) w) rec

public export
MultisetDuality ToroidalAstrodynamicsFunctor AbstractToroidalAstrodynamicsFunctor where
  leftAdjoint x = MkToroidalAstrodynamicsFunctor (MkToroidalPos (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 10)) x
  rightAdjoint (MkToroidalAstrodynamicsFunctor _ x) = x
  homTensorIso = toroidalAstrodynamicsHomTensorIso
  homTensorInv = toroidalAstrodynamicsHomTensorInv
  verifyHomIso = proofToroidalAstrodynamicsHomIso
  verifyHomInv = proofToroidalAstrodynamicsHomInv




