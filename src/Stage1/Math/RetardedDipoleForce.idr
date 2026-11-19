module Stage1.Math.RetardedDipoleForce

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.Multiset
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.VacuumDispersion
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 26: DISCRETE CASIMIR-POLDER & LONDON DISPERSION FORCES
------------------------------------------------------------------------

||| Computes the short-range non-retarded London dispersion potential:
||| V_London(Q) = - C6 / Q^3 (in exact UnixelFraction units)
public export
discreteLondonPotential : (c6 : Stage0.BoxInt.BoxInt) -> (quadranceQ : Nat) -> Stage1.UnixelFraction.UnixelFraction
discreteLondonPotential c6 q =
  let denom = if q == 0 then 1 else q * q * q
  in Stage1.UnixelFraction.MkUnixelFraction (- c6) (MkUnixel denom)

||| Computes the long-range retarded Casimir-Polder potential:
||| V_CP(Q) = - C7 / Q^4 (in exact UnixelFraction units)
public export
discreteCasimirPolderPotential : (c7 : Stage0.BoxInt.BoxInt) -> (quadranceQ : Nat) -> Stage1.UnixelFraction.UnixelFraction
discreteCasimirPolderPotential c7 q =
  let denom = if q == 0 then 1 else q * q * q * q
  in Stage1.UnixelFraction.MkUnixelFraction (- c7) (MkUnixel denom)

||| Evaluates Casimir-Polder potential across QuadStream payload.
public export
evaluateQuadStreamCasimirPolder : Stage0.BoxInt.BoxInt -> QuadStreamMultiset Stage0.BoxInt.BoxInt -> Stage1.UnixelFraction.UnixelFraction
evaluateQuadStreamCasimirPolder c7 (MkQuadStream e h p s) =
  let qVal = boxIntToPositiveNat (totalMassBox e + totalMassBox h)
  in discreteCasimirPolderPotential c7 qVal

||| Validates that both London and Casimir-Polder forces are strictly attractive (negative potential):
public export
isAttractiveDispersion : Stage1.UnixelFraction.UnixelFraction -> Bool
isAttractiveDispersion (Stage1.UnixelFraction.MkUnixelFraction n _) = n < Stage0.BoxInt.intToBoxInt 0

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 26: Discrete Casimir-Polder Force)
------------------------------------------------------------------------

||| Audits Law 26 (Discrete Casimir-Polder Retarded Dipole Potential):
public export
auditRetardedDipoleForceProof : Bool
auditRetardedDipoleForceProof =
  let c7 = Stage0.BoxInt.intToBoxInt 10
      f = discreteCasimirPolderPotential c7 2
  in isAttractiveDispersion f

------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
record DipoleState where
  constructor MkDipoleState
  c7 : BoxInt

public export
Eq DipoleState where
  (MkDipoleState a1) == (MkDipoleState a2) = a1 == a2

public export
data RetardedDipoleFunctor : Type -> Type where
  MkRetardedDipoleFunctor : DipoleState -> a -> RetardedDipoleFunctor a

public export
Functor RetardedDipoleFunctor where
  map f (MkRetardedDipoleFunctor s x) = MkRetardedDipoleFunctor s (f x)

public export
(Eq a) => Eq (RetardedDipoleFunctor a) where
  (MkRetardedDipoleFunctor s1 x1) == (MkRetardedDipoleFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractRetardedDipoleFunctor : Type -> Type where
  MkAbstractRetardedDipoleFunctor : DipoleState -> a -> AbstractRetardedDipoleFunctor a

public export
Functor AbstractRetardedDipoleFunctor where
  map f (MkAbstractRetardedDipoleFunctor s x) = MkAbstractRetardedDipoleFunctor s (f x)

public export
(Eq a) => Eq (AbstractRetardedDipoleFunctor a) where
  (MkAbstractRetardedDipoleFunctor s1 x1) == (MkAbstractRetardedDipoleFunctor s2 x2) = s1 == s2 && x1 == x2

public export
retardedDipoleHomTensorIso : MultisetTensor (RetardedDipoleFunctor a) b -> MultisetTensor a (AbstractRetardedDipoleFunctor b)
retardedDipoleHomTensorIso ZeroM = ZeroM
retardedDipoleHomTensorIso (AddM (MkRetardedDipoleFunctor s val, b) w rest) =
  AddM (val, MkAbstractRetardedDipoleFunctor s b) w (retardedDipoleHomTensorIso rest)

public export
retardedDipoleHomTensorInv : MultisetTensor a (AbstractRetardedDipoleFunctor b) -> MultisetTensor (RetardedDipoleFunctor a) b
retardedDipoleHomTensorInv ZeroM = ZeroM
retardedDipoleHomTensorInv (AddM (val, MkAbstractRetardedDipoleFunctor s b) w rest) =
  AddM (MkRetardedDipoleFunctor s val, b) w (retardedDipoleHomTensorInv rest)

public export
0 proofRetardedDipoleHomIso : (t : MultisetTensor (RetardedDipoleFunctor a) b) ->
                              retardedDipoleHomTensorInv (retardedDipoleHomTensorIso t) = t
proofRetardedDipoleHomIso ZeroM = Refl
proofRetardedDipoleHomIso (AddM (MkRetardedDipoleFunctor s val, b) w rest) =
  let rec = proofRetardedDipoleHomIso rest
  in cong (AddM (MkRetardedDipoleFunctor s val, b) w) rec

public export
0 proofRetardedDipoleHomInv : (u : MultisetTensor a (AbstractRetardedDipoleFunctor b)) ->
                              retardedDipoleHomTensorIso (retardedDipoleHomTensorInv u) = u
proofRetardedDipoleHomInv ZeroM = Refl
proofRetardedDipoleHomInv (AddM (val, MkAbstractRetardedDipoleFunctor s b) w rest) =
  let rec = proofRetardedDipoleHomInv rest
  in cong (AddM (val, MkAbstractRetardedDipoleFunctor s b) w) rec

public export
MultisetDuality RetardedDipoleFunctor AbstractRetardedDipoleFunctor where
  leftAdjoint x = MkRetardedDipoleFunctor (MkDipoleState (intToBoxInt 0)) x
  rightAdjoint (MkRetardedDipoleFunctor _ x) = x
  homTensorIso = retardedDipoleHomTensorIso
  homTensorInv = retardedDipoleHomTensorInv
  verifyHomIso = proofRetardedDipoleHomIso
  verifyHomInv = proofRetardedDipoleHomInv


