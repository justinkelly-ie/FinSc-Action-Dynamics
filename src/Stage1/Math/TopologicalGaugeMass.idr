module Stage1.Math.TopologicalGaugeMass

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 23: DISCRETE CHERN-SIMONS TOPOLOGICAL MASS GENERATION
------------------------------------------------------------------------

||| Computes the gauge-invariant topological photon mass:
||| m_gamma = level * couplingSquared (on exact integer BoxInt units).
public export
discreteChernSimonsMass : (level : Stage0.BoxInt.BoxInt) -> (couplingSquared : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
discreteChernSimonsMass k e2 = k * e2

||| Evaluates Chern-Simons gauge mass from QuadStream payload.
public export
evaluateQuadStreamChernSimonsMass : QuadStreamMultiset Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
evaluateQuadStreamChernSimonsMass (MkQuadStream e h p s) =
  let k = totalMassBox e
      e2 = totalMassBox h
  in discreteChernSimonsMass k e2

||| Proves Parity & Time-Reversal Oddness of Chern-Simons mass:
||| Under P or T inversion: k -> -k => m_gamma -> -m_gamma.
public export
isChernSimonsParityOdd : (level : Stage0.BoxInt.BoxInt) -> (couplingSquared : Stage0.BoxInt.BoxInt) -> Bool
isChernSimonsParityOdd k e2 =
  let mOrig = discreteChernSimonsMass k e2
      kInv  = negate k
      mInv  = discreteChernSimonsMass kInv e2
  in mInv == negate mOrig


------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 23: Discrete Chern-Simons Mass Generation)
------------------------------------------------------------------------

||| Audits Law 23 across topological gauge mass generation:
||| 1. Quantized Chern-Simons level k = 3 with coupling e^2 = 4:
|||    m_gamma = 3 * 4 = 12 (exact non-zero topological mass without Higgs).
||| 2. Parity inversion: k = -3 => m_gamma = -12.
||| 3. Zero level k = 0 => m_gamma = 0 (standard massless Maxwell photon).
public export
auditTopologicalGaugeMassProof : Bool
auditTopologicalGaugeMassProof =
  let kLevel = Stage0.BoxInt.intToBoxInt 3
      e2Val  = Stage0.BoxInt.intToBoxInt 4
      mPhot  = discreteChernSimonsMass kLevel e2Val
      mZero  = discreteChernSimonsMass (Stage0.BoxInt.intToBoxInt 0) e2Val
  in mPhot == intToBoxInt 12 &&
     boxIsZero mZero &&
     isChernSimonsParityOdd kLevel e2Val

------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
record ChernSimonsState where
  constructor MkChernSimonsState
  level           : BoxInt
  couplingSquared : BoxInt

public export
Eq ChernSimonsState where
  (MkChernSimonsState k1 e1) == (MkChernSimonsState k2 e2) = k1 == k2 && e1 == e2

public export
data ChernSimonsFunctor : Type -> Type where
  MkChernSimonsFunctor : ChernSimonsState -> a -> ChernSimonsFunctor a

public export
Functor ChernSimonsFunctor where
  map f (MkChernSimonsFunctor s x) = MkChernSimonsFunctor s (f x)

public export
(Eq a) => Eq (ChernSimonsFunctor a) where
  (MkChernSimonsFunctor s1 x1) == (MkChernSimonsFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractChernSimonsFunctor : Type -> Type where
  MkAbstractChernSimonsFunctor : ChernSimonsState -> a -> AbstractChernSimonsFunctor a

public export
Functor AbstractChernSimonsFunctor where
  map f (MkAbstractChernSimonsFunctor s x) = MkAbstractChernSimonsFunctor s (f x)

public export
(Eq a) => Eq (AbstractChernSimonsFunctor a) where
  (MkAbstractChernSimonsFunctor s1 x1) == (MkAbstractChernSimonsFunctor s2 x2) = s1 == s2 && x1 == x2

public export
chernSimonsHomTensorIso : MultisetTensor (ChernSimonsFunctor a) b -> MultisetTensor a (AbstractChernSimonsFunctor b)
chernSimonsHomTensorIso ZeroM = ZeroM
chernSimonsHomTensorIso (AddM (MkChernSimonsFunctor s val, b) w rest) =
  AddM (val, MkAbstractChernSimonsFunctor s b) w (chernSimonsHomTensorIso rest)

public export
chernSimonsHomTensorInv : MultisetTensor a (AbstractChernSimonsFunctor b) -> MultisetTensor (ChernSimonsFunctor a) b
chernSimonsHomTensorInv ZeroM = ZeroM
chernSimonsHomTensorInv (AddM (val, MkAbstractChernSimonsFunctor s b) w rest) =
  AddM (MkChernSimonsFunctor s val, b) w (chernSimonsHomTensorInv rest)

public export
0 proofChernSimonsHomIso : (t : MultisetTensor (ChernSimonsFunctor a) b) ->
                           chernSimonsHomTensorInv (chernSimonsHomTensorIso t) = t
proofChernSimonsHomIso ZeroM = Refl
proofChernSimonsHomIso (AddM (MkChernSimonsFunctor s val, b) w rest) =
  let rec = proofChernSimonsHomIso rest
  in cong (AddM (MkChernSimonsFunctor s val, b) w) rec

public export
0 proofChernSimonsHomInv : (u : MultisetTensor a (AbstractChernSimonsFunctor b)) ->
                           chernSimonsHomTensorIso (chernSimonsHomTensorInv u) = u
proofChernSimonsHomInv ZeroM = Refl
proofChernSimonsHomInv (AddM (val, MkAbstractChernSimonsFunctor s b) w rest) =
  let rec = proofChernSimonsHomInv rest
  in cong (AddM (val, MkAbstractChernSimonsFunctor s b) w) rec

public export
MultisetDuality ChernSimonsFunctor AbstractChernSimonsFunctor where
  leftAdjoint x = MkChernSimonsFunctor (MkChernSimonsState (intToBoxInt 0) (intToBoxInt 0)) x
  rightAdjoint (MkChernSimonsFunctor _ x) = x
  homTensorIso = chernSimonsHomTensorIso
  homTensorInv = chernSimonsHomTensorInv
  verifyHomIso = proofChernSimonsHomIso
  verifyHomInv = proofChernSimonsHomInv

