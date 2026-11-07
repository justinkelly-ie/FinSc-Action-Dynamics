module Stage1.Math.FractionalQuantumHall

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor

%default total

------------------------------------------------------------------------
-- 1. FRACTIONAL QUANTUM HALL FLUID & ANYONIC BRAIDING
------------------------------------------------------------------------

||| Represents a Fractional Quantum Hall Laughlin / Jain state with filling factor ν = p / q:
public export
record LaughlinState where
  constructor MkLaughlinState
  fillingNumerator : Nat
  fillingDenominator : Nat

public export
Eq LaughlinState where
  (MkLaughlinState p1 q1) == (MkLaughlinState p2 q2) =
    p1 == p2 && q1 == q2

||| Evaluates LaughlinState from QuadStream payload mass ratios.
public export
evaluateQuadStreamLaughlin : QuadStreamMultiset Stage0.BoxInt.BoxInt -> LaughlinState
evaluateQuadStreamLaughlin (MkQuadStream e h p s) =
  let pVal = boxIntToPositiveNat (multisetSum e)
      qVal = boxIntToPositiveNat (multisetSum h)
  in MkLaughlinState pVal qVal

||| Computes the fractional charge of a Laughlin quasiparticle excitation e* = (p/q) * e:
public export
fractionalQuasiparticleCharge : LaughlinState -> Stage1.UnixelFraction.UnixelFraction
fractionalQuasiparticleCharge (MkLaughlinState p q) =
  Stage1.UnixelFraction.MkUnixelFraction (Stage0.BoxInt.natToBoxInt p) (MkUnixel (if q == 0 then 1 else q))

||| Computes the anyonic statistical exchange angle denominator:
||| Exchanging two anyons yields topological phase θ = π / q.
||| Full 2π cycle corresponds to 2 * q fractional step subdivisions.
public export
anyonicExchangePeriod : LaughlinState -> Nat
anyonicExchangePeriod (MkLaughlinState _ q) = 2 * q

||| Computes the Quantized Fractional Hall Conductance:
||| σ_{xy} = (p / q) * (e^2 / h).
public export
fractionalHallConductance : LaughlinState -> Stage1.UnixelFraction.UnixelFraction
fractionalHallConductance = fractionalQuasiparticleCharge

------------------------------------------------------------------------
-- 2. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
------------------------------------------------------------------------

||| Left adjoint Fractional Quantum Hall functor wrapping Laughlin state and payload a
public export
data LaughlinFunctor : Type -> Type where
  MkLaughlinFunctor : LaughlinState -> a -> LaughlinFunctor a

public export
Functor LaughlinFunctor where
  map f (MkLaughlinFunctor state x) = MkLaughlinFunctor state (f x)

public export
(Eq a) => Eq (LaughlinFunctor a) where
  (MkLaughlinFunctor s1 x1) == (MkLaughlinFunctor s2 x2) = s1 == s2 && x1 == x2

||| Right adjoint Fractional Quantum Hall functor wrapping abstract Laughlin state and payload a
public export
data AbstractLaughlinFunctor : Type -> Type where
  MkAbstractLaughlinFunctor : LaughlinState -> a -> AbstractLaughlinFunctor a

public export
Functor AbstractLaughlinFunctor where
  map f (MkAbstractLaughlinFunctor state x) = MkAbstractLaughlinFunctor state (f x)

public export
(Eq a) => Eq (AbstractLaughlinFunctor a) where
  (MkAbstractLaughlinFunctor s1 x1) == (MkAbstractLaughlinFunctor s2 x2) = s1 == s2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro Laughlin multiset tensors
public export
laughlinHomTensorIso : MultisetTensor (LaughlinFunctor a) b -> MultisetTensor a (AbstractLaughlinFunctor b)
laughlinHomTensorIso ZeroM = ZeroM
laughlinHomTensorIso (AddM (MkLaughlinFunctor state val, b) w rest) =
  AddM (val, MkAbstractLaughlinFunctor state b) w (laughlinHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro Laughlin multiset tensors
public export
laughlinHomTensorInv : MultisetTensor a (AbstractLaughlinFunctor b) -> MultisetTensor (LaughlinFunctor a) b
laughlinHomTensorInv ZeroM = ZeroM
laughlinHomTensorInv (AddM (val, MkAbstractLaughlinFunctor state b) w rest) =
  AddM (MkLaughlinFunctor state val, b) w (laughlinHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofLaughlinHomIso : (t : MultisetTensor (LaughlinFunctor a) b) ->
                        laughlinHomTensorInv (laughlinHomTensorIso t) = t
proofLaughlinHomIso ZeroM = Refl
proofLaughlinHomIso (AddM (MkLaughlinFunctor state val, b) w rest) =
  let rec = proofLaughlinHomIso rest
  in cong (AddM (MkLaughlinFunctor state val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofLaughlinHomInv : (u : MultisetTensor a (AbstractLaughlinFunctor b)) ->
                        laughlinHomTensorIso (laughlinHomTensorInv u) = u
proofLaughlinHomInv ZeroM = Refl
proofLaughlinHomInv (AddM (val, MkAbstractLaughlinFunctor state b) w rest) =
  let rec = proofLaughlinHomInv rest
  in cong (AddM (val, MkAbstractLaughlinFunctor state b) w) rec

||| Category-Theoretic MultisetAdjunction instance LaughlinFunctor ⊣ AbstractLaughlinFunctor
public export
MultisetAdjunction LaughlinFunctor AbstractLaughlinFunctor where
  leftAdjoint x = MkLaughlinFunctor (MkLaughlinState 1 1) x
  rightAdjoint (MkLaughlinFunctor _ x) = x
  homTensorIso = laughlinHomTensorIso
  homTensorInv = laughlinHomTensorInv
  verifyHomIso = proofLaughlinHomIso
  verifyHomInv = proofLaughlinHomInv

------------------------------------------------------------------------
-- 3. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 14: Fractional Quantum Hall & Anyonic Statistics)
------------------------------------------------------------------------

||| QTT 0 Erased Proof: Quasiparticle Fractional Charge Quantization (e* = 1/3 e).
public export
0 prfFractionalChargeQuantization :
  fractionalQuasiparticleCharge (MkLaughlinState 1 3) =
  Stage1.UnixelFraction.MkUnixelFraction (intToBoxInt 1) (MkUnixel 3)
prfFractionalChargeQuantization = Refl

||| QTT 0 Erased Proof: Anyonic Topological Braiding Phase Period (2 * 3 = 6).
public export
0 prfAnyonicBraidingPhase : anyonicExchangePeriod (MkLaughlinState 1 3) = 6
prfAnyonicBraidingPhase = Refl

||| QTT 0 Erased Proof: Fractional Hall Hom-Tensor Adjunction Duality.
public export
0 prfFractionalHallConductance : (t : MultisetTensor (LaughlinFunctor Nat) Nat) ->
                                laughlinHomTensorInv (laughlinHomTensorIso t) = t
prfFractionalHallConductance = proofLaughlinHomIso

||| Audits Fractional Quantum Hall Conductance, charge fractionalization, and anyonic braiding phase (Law 14).
public export
auditFractionalHallConductanceProof : Bool
auditFractionalHallConductanceProof =
  let st = MkLaughlinState 1 3
      cond = fractionalHallConductance st
      period = anyonicExchangePeriod st
  in cond.num == intToBoxInt 1 && denominatorNat cond == 3 && period == 6



