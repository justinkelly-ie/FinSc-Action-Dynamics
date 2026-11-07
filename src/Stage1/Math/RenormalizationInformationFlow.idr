module Stage1.Math.RenormalizationInformationFlow

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.Multiset
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage1.QuadStream
import Stage1.Math.TopologicalChernNumber
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List

%default total

------------------------------------------------------------------------
-- 1. DISCRETE CALLAN-SYMANZIK BETA FUNCTION & RG FLOW
------------------------------------------------------------------------

||| Discrete Callan-Symanzik beta function evaluating step-change in effective coupling:
||| beta(g) = Delta g_k = - (drag_k * g) / (1 + drag_k)
public export
discreteBetaStep : (coupling : Stage1.UnixelFraction.UnixelFraction) -> (dragNat : Nat) -> Stage1.UnixelFraction.UnixelFraction
discreteBetaStep coupling drag =
  let numVal = coupling.num
      denVal = denominatorNat coupling
      dragBox = Stage0.BoxInt.natToBoxInt drag
      newNum = - (numVal * dragBox)
      newDen = denVal * (1 + drag)
  in Stage1.UnixelFraction.mkUnixelFraction newNum (if newDen == 0 then 1 else newDen)

------------------------------------------------------------------------
-- 2. DISCRETE FISHER INFORMATION METRIC ON PROBABILITY SIMPLICES
--    I_F(P, Q) = sum_k (P_k - Q_k)^2 / P_k
------------------------------------------------------------------------

||| Evaluates discrete Fisher information quadrance between two 1-particle state weights:
||| I_F = (w1 - w2)^2 / w1 (as a UnixelFraction).
public export
discreteFisherQuadrance : (w1 : Nat) -> (w2 : Nat) -> Stage1.UnixelFraction.UnixelFraction
discreteFisherQuadrance w1 w2 =
  let diff = (natToInteger w1) - (natToInteger w2)
      sqDiff = diff * diff
      den = if w1 == 0 then 1 else w1
  in Stage1.UnixelFraction.mkUnixelFraction (Stage0.BoxInt.intToBoxInt sqDiff) den

||| Evaluates Fisher quadrance from QuadStream payload sector weights.
public export
evaluateQuadStreamFisherQuadrance : QuadStreamMultiset Stage0.BoxInt.BoxInt -> Stage1.UnixelFraction.UnixelFraction
evaluateQuadStreamFisherQuadrance (MkQuadStream e h p s) =
  let w1 = natVal (multisetSum e)
      w2 = natVal (multisetSum h)
  in discreteFisherQuadrance w1 w2
  where
    natVal : Stage0.BoxInt.BoxInt -> Nat
    natVal = boxToNat

------------------------------------------------------------------------
-- 3. TOPOLOGICAL RG FIXED POINT COARSE-GRAINING
------------------------------------------------------------------------

||| Coarse-graining decimation operator on 2D Berry curvature grid:
||| Aggregates 2x2 fine plaquettes into 1 coarse plaquette while preserving total First Chern Number.
public export
decimateBerryCurvature : (finePlaquettes : List Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
decimateBerryCurvature = foldl (+) (Stage0.BoxInt.intToBoxInt 0)

------------------------------------------------------------------------
-- 4. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Multi-Scale Renormalization & Information Geometry)
------------------------------------------------------------------------

||| Audits Renormalization Group Information Flow & Topological Invariance:
public export
auditRenormalizationInformationFlowProof : Bool
auditRenormalizationInformationFlowProof =
  let g0 = Stage1.UnixelFraction.mkUnixelFraction (Stage0.BoxInt.intToBoxInt 1) 1
      (Stage1.UnixelFraction.MkUnixelFraction numDg _) = discreteBetaStep g0 1
      (Stage1.UnixelFraction.MkUnixelFraction numFish _) = discreteFisherQuadrance 10 6
      cCoarse = decimateBerryCurvature [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0]
  in cCoarse == Stage0.BoxInt.intToBoxInt 1 &&
     numDg == Stage0.BoxInt.intToBoxInt (-1) &&
     numFish == Stage0.BoxInt.intToBoxInt 16

public export
auditDiscreteBetaFlowProof : Bool
auditDiscreteBetaFlowProof =
  let g0 = mkUnixelFraction (Stage0.BoxInt.intToBoxInt 1) 1
      dg = discreteBetaStep g0 1
  in dg.num == Stage0.BoxInt.intToBoxInt (-1) && denominatorNat dg == 2

public export
auditDiscreteFisherMetricProof : Bool
auditDiscreteFisherMetricProof =
  let fq = discreteFisherQuadrance 10 6
  in fq.num == Stage0.BoxInt.intToBoxInt 16 && denominatorNat fq == 10

public export
auditTopologicalRGFixedPointProof : Bool
auditTopologicalRGFixedPointProof =
  let cCoarse = decimateBerryCurvature [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0]
  in cCoarse == Stage0.BoxInt.intToBoxInt 1

public export
auditPlaquetteDecimationProof : Bool
auditPlaquetteDecimationProof =
  let plaquettes = [Stage0.BoxInt.intToBoxInt 2, Stage0.BoxInt.intToBoxInt 3, Stage0.BoxInt.intToBoxInt (-1), Stage0.BoxInt.intToBoxInt 1]
      coarse = decimateBerryCurvature plaquettes
  in coarse == Stage0.BoxInt.intToBoxInt 5

public export
auditMultiBlockTopologicalFixedPointProof : Bool
auditMultiBlockTopologicalFixedPointProof =
  let block1 = decimateBerryCurvature [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0]
      block2 = decimateBerryCurvature [Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 0, Stage0.BoxInt.intToBoxInt 0]
      macroBlock = decimateBerryCurvature [block1, block2]
  in macroBlock == Stage0.BoxInt.intToBoxInt 2

------------------------------------------------------------------------
-- 5. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
record RenormalizationState where
  constructor MkRenormalizationState
  drag : Nat

public export
Eq RenormalizationState where
  (MkRenormalizationState d1) == (MkRenormalizationState d2) = d1 == d2

public export
data RenormalizationFunctor : Type -> Type where
  MkRenormalizationFunctor : RenormalizationState -> a -> RenormalizationFunctor a

public export
Functor RenormalizationFunctor where
  map f (MkRenormalizationFunctor s x) = MkRenormalizationFunctor s (f x)

public export
(Eq a) => Eq (RenormalizationFunctor a) where
  (MkRenormalizationFunctor s1 x1) == (MkRenormalizationFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractRenormalizationFunctor : Type -> Type where
  MkAbstractRenormalizationFunctor : RenormalizationState -> a -> AbstractRenormalizationFunctor a

public export
Functor AbstractRenormalizationFunctor where
  map f (MkAbstractRenormalizationFunctor s x) = MkAbstractRenormalizationFunctor s (f x)

public export
(Eq a) => Eq (AbstractRenormalizationFunctor a) where
  (MkAbstractRenormalizationFunctor s1 x1) == (MkAbstractRenormalizationFunctor s2 x2) = s1 == s2 && x1 == x2

public export
renormalizationHomTensorIso : MultisetTensor (RenormalizationFunctor a) b -> MultisetTensor a (AbstractRenormalizationFunctor b)
renormalizationHomTensorIso ZeroM = ZeroM
renormalizationHomTensorIso (AddM (MkRenormalizationFunctor s val, b) w rest) =
  AddM (val, MkAbstractRenormalizationFunctor s b) w (renormalizationHomTensorIso rest)

public export
renormalizationHomTensorInv : MultisetTensor a (AbstractRenormalizationFunctor b) -> MultisetTensor (RenormalizationFunctor a) b
renormalizationHomTensorInv ZeroM = ZeroM
renormalizationHomTensorInv (AddM (val, MkAbstractRenormalizationFunctor s b) w rest) =
  AddM (MkRenormalizationFunctor s val, b) w (renormalizationHomTensorInv rest)

public export
0 proofRenormalizationHomIso : (t : MultisetTensor (RenormalizationFunctor a) b) ->
                               renormalizationHomTensorInv (renormalizationHomTensorIso t) = t
proofRenormalizationHomIso ZeroM = Refl
proofRenormalizationHomIso (AddM (MkRenormalizationFunctor s val, b) w rest) =
  let rec = proofRenormalizationHomIso rest
  in cong (AddM (MkRenormalizationFunctor s val, b) w) rec

public export
0 proofRenormalizationHomInv : (u : MultisetTensor a (AbstractRenormalizationFunctor b)) ->
                               renormalizationHomTensorIso (renormalizationHomTensorInv u) = u
proofRenormalizationHomInv ZeroM = Refl
proofRenormalizationHomInv (AddM (val, MkAbstractRenormalizationFunctor s b) w rest) =
  let rec = proofRenormalizationHomInv rest
  in cong (AddM (val, MkAbstractRenormalizationFunctor s b) w) rec

public export
MultisetAdjunction RenormalizationFunctor AbstractRenormalizationFunctor where
  leftAdjoint x = MkRenormalizationFunctor (MkRenormalizationState 0) x
  rightAdjoint (MkRenormalizationFunctor _ x) = x
  homTensorIso = renormalizationHomTensorIso
  homTensorInv = renormalizationHomTensorInv
  verifyHomIso = proofRenormalizationHomIso
  verifyHomInv = proofRenormalizationHomInv


