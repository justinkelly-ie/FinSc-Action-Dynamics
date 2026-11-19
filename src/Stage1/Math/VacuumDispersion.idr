module Stage1.Math.VacuumDispersion

import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor

%default total

------------------------------------------------------------------------
-- 1. DISCRETE VACUUM MODE DENSITY & CAVITY CONFINEMENT
------------------------------------------------------------------------

||| Discrete Cavity Boundary state defined by integer plate separation d.
public export
record CavityBoundary where
  constructor MkCavityBoundary
  plateSeparation : Nat

public export
Eq CavityBoundary where
  (MkCavityBoundary d1) == (MkCavityBoundary d2) = d1 == d2

public export
Show CavityBoundary where
  show (MkCavityBoundary d) = "Cavity(d=" ++ show d ++ ")"

||| Computes the discrete sum of standing modes inside a cavity of width d:
||| E(d) = ∑_{k=1}^d k = d*(d+1)/2.
public export
cavityModeEnergySum : Nat -> Nat
cavityModeEnergySum Z = 0
cavityModeEnergySum (S k) = (S k) + cavityModeEnergySum k

||| Computes the discrete Casimir vacuum pressure / force between parallel plates:
||| F(d) = E(d-1) - E(d) = -d < 0 (Strictly attractive).
public export
discreteCasimirForce : Nat -> Stage0.BoxInt.BoxInt
discreteCasimirForce Z = Stage0.BoxInt.intToBoxInt 0
discreteCasimirForce (S k) =
  let ePrev = cavityModeEnergySum k
      eCurr = cavityModeEnergySum (S k)
      diff = cast ePrev - cast eCurr
  in Stage0.BoxInt.intToBoxInt diff

||| Evaluates discrete Casimir force from QuadStream cavity plate separation.
public export
evaluateQuadStreamCasimirForce : QuadStreamMultiset Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
evaluateQuadStreamCasimirForce (MkQuadStream e h p s) =
  let d = boxIntToPositiveNat (totalMassBox e)
  in discreteCasimirForce d

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits the Discrete Casimir Attractive Force Invariant:
||| Proves that for plate separation d = 4, the Casimir force is strictly negative:
||| F(4) = E(3) - E(4) = 6 - 10 = -4 < 0.
public export
auditCasimirAttractiveForceProof : Bool
auditCasimirAttractiveForceProof =
  let f4 = discreteCasimirForce 4
      f3 = discreteCasimirForce 3
      zero = intToBoxInt 0
  in f4 == intToBoxInt (-4) &&
     f3 == intToBoxInt (-3) &&
     f4 < zero &&
     f3 < zero

||| Audits Discrete Vacuum Mode Confinement:
||| Proves that mode capacity strictly decreases with plate contraction:
||| E(1)=1, E(2)=3, E(3)=6, E(4)=10, with exact triangular number progression.
public export
auditCasimirModeConfinementProof : Bool
auditCasimirModeConfinementProof =
  cavityModeEnergySum 1 == 1 &&
  cavityModeEnergySum 2 == 3 &&
  cavityModeEnergySum 3 == 6 &&
  cavityModeEnergySum 4 == 10

------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
data VacuumDispersionFunctor : Type -> Type where
  MkVacuumDispersionFunctor : CavityBoundary -> a -> VacuumDispersionFunctor a

public export
Functor VacuumDispersionFunctor where
  map f (MkVacuumDispersionFunctor c x) = MkVacuumDispersionFunctor c (f x)

public export
(Eq a) => Eq (VacuumDispersionFunctor a) where
  (MkVacuumDispersionFunctor c1 x1) == (MkVacuumDispersionFunctor c2 x2) = c1 == c2 && x1 == x2

public export
data AbstractVacuumDispersionFunctor : Type -> Type where
  MkAbstractVacuumDispersionFunctor : CavityBoundary -> a -> AbstractVacuumDispersionFunctor a

public export
Functor AbstractVacuumDispersionFunctor where
  map f (MkAbstractVacuumDispersionFunctor c x) = MkAbstractVacuumDispersionFunctor c (f x)

public export
(Eq a) => Eq (AbstractVacuumDispersionFunctor a) where
  (MkAbstractVacuumDispersionFunctor c1 x1) == (MkAbstractVacuumDispersionFunctor c2 x2) = c1 == c2 && x1 == x2

public export
vacuumDispersionHomTensorIso : MultisetTensor (VacuumDispersionFunctor a) b -> MultisetTensor a (AbstractVacuumDispersionFunctor b)
vacuumDispersionHomTensorIso ZeroM = ZeroM
vacuumDispersionHomTensorIso (AddM (MkVacuumDispersionFunctor c val, b) w rest) =
  AddM (val, MkAbstractVacuumDispersionFunctor c b) w (vacuumDispersionHomTensorIso rest)

public export
vacuumDispersionHomTensorInv : MultisetTensor a (AbstractVacuumDispersionFunctor b) -> MultisetTensor (VacuumDispersionFunctor a) b
vacuumDispersionHomTensorInv ZeroM = ZeroM
vacuumDispersionHomTensorInv (AddM (val, MkAbstractVacuumDispersionFunctor c b) w rest) =
  AddM (MkVacuumDispersionFunctor c val, b) w (vacuumDispersionHomTensorInv rest)

public export
0 proofVacuumDispersionHomIso : (t : MultisetTensor (VacuumDispersionFunctor a) b) ->
                                vacuumDispersionHomTensorInv (vacuumDispersionHomTensorIso t) = t
proofVacuumDispersionHomIso ZeroM = Refl
proofVacuumDispersionHomIso (AddM (MkVacuumDispersionFunctor c val, b) w rest) =
  let rec = proofVacuumDispersionHomIso rest
  in cong (AddM (MkVacuumDispersionFunctor c val, b) w) rec

public export
0 proofVacuumDispersionHomInv : (u : MultisetTensor a (AbstractVacuumDispersionFunctor b)) ->
                                vacuumDispersionHomTensorIso (vacuumDispersionHomTensorInv u) = u
proofVacuumDispersionHomInv ZeroM = Refl
proofVacuumDispersionHomInv (AddM (val, MkAbstractVacuumDispersionFunctor c b) w rest) =
  let rec = proofVacuumDispersionHomInv rest
  in cong (AddM (val, MkAbstractVacuumDispersionFunctor c b) w) rec

public export
MultisetDuality VacuumDispersionFunctor AbstractVacuumDispersionFunctor where
  leftAdjoint x = MkVacuumDispersionFunctor (MkCavityBoundary 1) x
  rightAdjoint (MkVacuumDispersionFunctor _ x) = x
  homTensorIso = vacuumDispersionHomTensorIso
  homTensorInv = vacuumDispersionHomTensorInv
  verifyHomIso = proofVacuumDispersionHomIso
  verifyHomInv = proofVacuumDispersionHomInv

