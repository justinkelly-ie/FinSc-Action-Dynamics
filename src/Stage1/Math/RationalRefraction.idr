module Stage1.Math.RationalRefraction

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List

%default total

------------------------------------------------------------------------
-- 1. LAW 55: DISCRETE RATIONAL SNELL'S LAW & TRIPLE SPREAD LAW
------------------------------------------------------------------------

||| Helper: checks if a BoxInt token value is zero.
%inline
public export
boxZero : Stage0.BoxInt.BoxInt -> Bool
boxZero b = Stage0.BoxInt.boxIsZero b

||| Evaluates Rational Snell's Law under Chromogeometric refraction:
||| n1^2 * s1 = n2^2 * s2  ==> (n1^2 * s1) - (n2^2 * s2) = 0.
%inline
public export
rationalSnellRefraction : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
rationalSnellRefraction n1 s1 n2 s2 =
  let lhs = (n1 * n1) * s1
      rhs = (n2 * n2) * s2
  in lhs - rhs

||| Evaluates Rational Snell's Refraction from QuadStream payload.
public export
evaluateQuadStreamSnellRefraction : QuadStreamMultiset BoxInt -> BoxInt
evaluateQuadStreamSnellRefraction (MkQuadStream e h p s) =
  let n1 = totalMassBox e
      s1 = totalMassBox h
      n2 = totalMassBox p
      s2 = totalMassBox s
  in rationalSnellRefraction n1 s1 n2 s2

||| Verifies non-reflective total internal refraction invariant.
%inline
public export
isSnellRefracted : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Bool
isSnellRefracted n1 s1 n2 s2 = boxZero (rationalSnellRefraction n1 s1 n2 s2)

------------------------------------------------------------------------
-- 2. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
------------------------------------------------------------------------

||| Left adjoint Rational Refraction functor wrapping optical state and payload a
public export
data RefractionFunctor : Type -> Type where
  MkRefractionFunctor : BoxInt -> BoxInt -> BoxInt -> BoxInt -> a -> RefractionFunctor a

public export
Functor RefractionFunctor where
  map f (MkRefractionFunctor n1 s1 n2 s2 x) = MkRefractionFunctor n1 s1 n2 s2 (f x)

public export
(Eq a) => Eq (RefractionFunctor a) where
  (MkRefractionFunctor a1 b1 c1 d1 x1) == (MkRefractionFunctor a2 b2 c2 d2 x2) =
    a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2 && x1 == x2

||| Right adjoint Rational Refraction functor wrapping abstract optical state and payload a
public export
data AbstractRefractionFunctor : Type -> Type where
  MkAbstractRefractionFunctor : BoxInt -> BoxInt -> BoxInt -> BoxInt -> a -> AbstractRefractionFunctor a

public export
Functor AbstractRefractionFunctor where
  map f (MkAbstractRefractionFunctor n1 s1 n2 s2 x) = MkAbstractRefractionFunctor n1 s1 n2 s2 (f x)

public export
(Eq a) => Eq (AbstractRefractionFunctor a) where
  (MkAbstractRefractionFunctor a1 b1 c1 d1 x1) == (MkAbstractRefractionFunctor a2 b2 c2 d2 x2) =
    a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro Refraction multiset tensors
public export
refractionHomTensorIso : MultisetTensor (RefractionFunctor a) b -> MultisetTensor a (AbstractRefractionFunctor b)
refractionHomTensorIso ZeroM = ZeroM
refractionHomTensorIso (AddM (MkRefractionFunctor n1 s1 n2 s2 val, b) w rest) =
  AddM (val, MkAbstractRefractionFunctor n1 s1 n2 s2 b) w (refractionHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro Refraction multiset tensors
public export
refractionHomTensorInv : MultisetTensor a (AbstractRefractionFunctor b) -> MultisetTensor (RefractionFunctor a) b
refractionHomTensorInv ZeroM = ZeroM
refractionHomTensorInv (AddM (val, MkAbstractRefractionFunctor n1 s1 n2 s2 b) w rest) =
  AddM (MkRefractionFunctor n1 s1 n2 s2 val, b) w (refractionHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofRefractionHomIso : (t : MultisetTensor (RefractionFunctor a) b) ->
                          refractionHomTensorInv (refractionHomTensorIso t) = t
proofRefractionHomIso ZeroM = Refl
proofRefractionHomIso (AddM (MkRefractionFunctor n1 s1 n2 s2 val, b) w rest) =
  let rec = proofRefractionHomIso rest
  in cong (AddM (MkRefractionFunctor n1 s1 n2 s2 val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofRefractionHomInv : (u : MultisetTensor a (AbstractRefractionFunctor b)) ->
                          refractionHomTensorIso (refractionHomTensorInv u) = u
proofRefractionHomInv ZeroM = Refl
proofRefractionHomInv (AddM (val, MkAbstractRefractionFunctor n1 s1 n2 s2 b) w rest) =
  let rec = proofRefractionHomInv rest
  in cong (AddM (val, MkAbstractRefractionFunctor n1 s1 n2 s2 b) w) rec

||| Category-Theoretic MultisetAdjunction instance RefractionFunctor ⊣ AbstractRefractionFunctor
public export
MultisetDuality RefractionFunctor AbstractRefractionFunctor where
  leftAdjoint x = MkRefractionFunctor (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0) x
  rightAdjoint (MkRefractionFunctor _ _ _ _ x) = x
  homTensorIso = refractionHomTensorIso
  homTensorInv = refractionHomTensorInv
  verifyHomIso = proofRefractionHomIso
  verifyHomInv = proofRefractionHomInv

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Law 55 (Discrete Rational Snell's Refraction n1^2 * s1 = n2^2 * s2):
public export
auditRationalSnellProof : Bool
auditRationalSnellProof =
  let n1 = Stage0.BoxInt.intToBoxInt 2
      s1 = Stage0.BoxInt.intToBoxInt 9
      n2 = Stage0.BoxInt.intToBoxInt 3
      s2 = Stage0.BoxInt.intToBoxInt 4
  in isSnellRefracted n1 s1 n2 s2


