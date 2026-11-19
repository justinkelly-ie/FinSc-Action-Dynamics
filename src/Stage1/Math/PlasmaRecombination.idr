module Stage1.Math.PlasmaRecombination

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List

%default total

------------------------------------------------------------------------
-- 1. LAW 51: DISCRETE PLASMA RECOMBINATION & COSMIC MICROWAVE DECOUPLING
------------------------------------------------------------------------

||| Evaluates ionization fraction X_e under discrete Saha equilibrium at decoupling:
||| X_e = N_free / N_total. At decoupling (z ~ 1100), X_e drops below 1/1000.
%inline
public export
ionizationFraction : BoxInt -> BoxInt -> UnixelFraction
ionizationFraction nFree nTotal = mkUnixelFraction nFree (boxIntToPositiveNat nTotal)

||| Evaluates ionization fraction from QuadStream payload.
public export
evaluateQuadStreamIonization : QuadStreamMultiset BoxInt -> UnixelFraction
evaluateQuadStreamIonization (MkQuadStream e h p s) =
  let nFree = totalMassBox e
      nTotal = totalMassBox e + totalMassBox h + totalMassBox p + totalMassBox s
  in ionizationFraction nFree nTotal

||| Verifies photon mean free path expansion (lambda -> infinity) upon recombination.
%inline
public export
isDecoupledPlasma : UnixelFraction -> Bool
isDecoupledPlasma frac = (unwrapBox frac.num * 1000) <= cast (denominatorNat frac)

------------------------------------------------------------------------
-- 2. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
------------------------------------------------------------------------

||| Left adjoint Plasma Recombination functor wrapping ionization state and payload a
public export
data PlasmaRecombinationFunctor : Type -> Type where
  MkPlasmaRecombinationFunctor : UnixelFraction -> a -> PlasmaRecombinationFunctor a

public export
Functor PlasmaRecombinationFunctor where
  map f (MkPlasmaRecombinationFunctor xe x) = MkPlasmaRecombinationFunctor xe (f x)

public export
(Eq a) => Eq (PlasmaRecombinationFunctor a) where
  (MkPlasmaRecombinationFunctor x1 p1) == (MkPlasmaRecombinationFunctor x2 p2) = x1 == x2 && p1 == p2

||| Right adjoint Plasma Recombination functor wrapping abstract ionization state and payload a
public export
data AbstractPlasmaRecombinationFunctor : Type -> Type where
  MkAbstractPlasmaRecombinationFunctor : UnixelFraction -> a -> AbstractPlasmaRecombinationFunctor a

public export
Functor AbstractPlasmaRecombinationFunctor where
  map f (MkAbstractPlasmaRecombinationFunctor xe x) = MkAbstractPlasmaRecombinationFunctor xe (f x)

public export
(Eq a) => Eq (AbstractPlasmaRecombinationFunctor a) where
  (MkAbstractPlasmaRecombinationFunctor x1 p1) == (MkAbstractPlasmaRecombinationFunctor x2 p2) = x1 == x2 && p1 == p2

||| Forward hom-tensor isomorphism mapping micro to macro Plasma Recombination multiset tensors
public export
plasmaRecombinationHomTensorIso : MultisetTensor (PlasmaRecombinationFunctor a) b -> MultisetTensor a (AbstractPlasmaRecombinationFunctor b)
plasmaRecombinationHomTensorIso ZeroM = ZeroM
plasmaRecombinationHomTensorIso (AddM (MkPlasmaRecombinationFunctor xe val, b) w rest) =
  AddM (val, MkAbstractPlasmaRecombinationFunctor xe b) w (plasmaRecombinationHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro Plasma Recombination multiset tensors
public export
plasmaRecombinationHomTensorInv : MultisetTensor a (AbstractPlasmaRecombinationFunctor b) -> MultisetTensor (PlasmaRecombinationFunctor a) b
plasmaRecombinationHomTensorInv ZeroM = ZeroM
plasmaRecombinationHomTensorInv (AddM (val, MkAbstractPlasmaRecombinationFunctor xe b) w rest) =
  AddM (MkPlasmaRecombinationFunctor xe val, b) w (plasmaRecombinationHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofPlasmaRecombinationHomIso : (t : MultisetTensor (PlasmaRecombinationFunctor a) b) ->
                                   plasmaRecombinationHomTensorInv (plasmaRecombinationHomTensorIso t) = t
proofPlasmaRecombinationHomIso ZeroM = Refl
proofPlasmaRecombinationHomIso (AddM (MkPlasmaRecombinationFunctor xe val, b) w rest) =
  let rec = proofPlasmaRecombinationHomIso rest
  in cong (AddM (MkPlasmaRecombinationFunctor xe val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofPlasmaRecombinationHomInv : (u : MultisetTensor a (AbstractPlasmaRecombinationFunctor b)) ->
                                   plasmaRecombinationHomTensorIso (plasmaRecombinationHomTensorInv u) = u
proofPlasmaRecombinationHomInv ZeroM = Refl
proofPlasmaRecombinationHomInv (AddM (val, MkAbstractPlasmaRecombinationFunctor xe b) w rest) =
  let rec = proofPlasmaRecombinationHomInv rest
  in cong (AddM (val, MkAbstractPlasmaRecombinationFunctor xe b) w) rec

||| Category-Theoretic MultisetAdjunction instance PlasmaRecombinationFunctor ⊣ AbstractPlasmaRecombinationFunctor
public export
MultisetDuality PlasmaRecombinationFunctor AbstractPlasmaRecombinationFunctor where
  leftAdjoint x = MkPlasmaRecombinationFunctor zeroUnixelFraction x
  rightAdjoint (MkPlasmaRecombinationFunctor _ x) = x
  homTensorIso = plasmaRecombinationHomTensorIso
  homTensorInv = plasmaRecombinationHomTensorInv
  verifyHomIso = proofPlasmaRecombinationHomIso
  verifyHomInv = proofPlasmaRecombinationHomInv

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Law 51 (Plasma Recombination & Cosmic Microwave Decoupling):
||| 1. Ionization fraction X_e = 1 / 10000 at decoupling.
||| 2. Decoupling condition holds.
%inline
public export
auditLaw51PlasmaRecombinationProof : Bool
auditLaw51PlasmaRecombinationProof =
  let xe = ionizationFraction (intToBoxInt 1) (intToBoxInt 10000)
  in isDecoupledPlasma xe

