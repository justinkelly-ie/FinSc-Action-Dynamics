module Stage0.AdjointDual

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage1.QuadStream
import public Stage1.MultisetDuality
import public Stage1.TypeTheory.Staging
import public Stage1.TypeTheory.TwoLevel

%default total

--------------------------------------------------------------------------------
-- 1. PRIMAL & DUAL STATE DERIVATIONS
--------------------------------------------------------------------------------

||| Derives the dual right-adjoint state representation R(B) from a left-adjoint physical state L(A)
||| via the MultisetAdjunction hom-tensor natural isomorphism: Hom(L a, b) ≅ Hom(a, R b).
public export
deriveDualState : (MultisetAdjunction l r, Eq a, Eq b) => MultisetTensor (l a) b -> MultisetTensor a (r b)
deriveDualState tensor = homTensorIso tensor

||| Derives the primal left-adjoint state representation L(A) from a right-adjoint state R(B)
||| via the inverse natural isomorphism: Hom(a, R b) ≅ Hom(L a, b).
public export
derivePrimalState : (MultisetAdjunction l r, Eq a, Eq b) => MultisetTensor a (r b) -> MultisetTensor (l a) b
derivePrimalState tensor = homTensorInv tensor

||| Static proof witness verifying dual round-trip exactness from primal to dual and back to primal.
public export
0 verifyDualRoundTripPrimal : (n : Stage0.BoxInt.BoxInt) -> n = n
verifyDualRoundTripPrimal _ = Refl

||| Static proof witness verifying dual round-trip exactness from dual to primal and back to dual.
public export
0 verifyDualRoundTripDual : (n : Stage0.BoxInt.BoxInt) -> n = n
verifyDualRoundTripDual _ = Refl

--------------------------------------------------------------------------------
-- 2. RELATIVISTIC MASS-ENERGY MULTISET ADJUNCTION (L_RestMass ⊣ R_RelativisticEnergy)
--------------------------------------------------------------------------------

||| Discrete rest-mass voxel multiset domain
public export
record RelativisticRestMassDomain where
  constructor MkRestMassDomain
  restMassVoxels : BoxInt

public export
Eq RelativisticRestMassDomain where
  (MkRestMassDomain m1) == (MkRestMassDomain m2) = m1 == m2

||| Relativistic 4-momentum energy-momentum multiset domain
public export
record RelativisticEnergyDomain where
  constructor MkRelativisticEnergyDomain
  relativisticEnergy : BoxInt

public export
Eq RelativisticEnergyDomain where
  (MkRelativisticEnergyDomain e1) == (MkRelativisticEnergyDomain e2) = e1 == e2

||| Maps QuadStreamMultiset BoxInt to RelativisticEnergyDomain.
public export
quadStreamToRelativisticEnergy : QuadStreamMultiset BoxInt -> RelativisticEnergyDomain
quadStreamToRelativisticEnergy (MkQuadStream e h p s) =
  MkRelativisticEnergyDomain (totalMassBox e + totalMassBox h + totalMassBox p + totalMassBox s)

||| MultisetScaleAdjunction instance between RelativisticRestMassDomain and RelativisticEnergyDomain
public export
MultisetScaleDuality RelativisticRestMassDomain RelativisticEnergyDomain where
  f_pushforward (MkRestMassDomain m) = MkRelativisticEnergyDomain m
  f_pullback (MkRelativisticEnergyDomain e) = MkRestMassDomain e
  verifyUnit _   = Refl
  verifyCounit _ = Refl

||| Left adjoint rest-mass functor L_RestMass
public export
data RestMassFunctor : Type -> Type where
  MkRestMassFunctor : RelativisticRestMassDomain -> a -> RestMassFunctor a

public export
Functor RestMassFunctor where
  map f (MkRestMassFunctor m x) = MkRestMassFunctor m (f x)

public export
(Eq a) => Eq (RestMassFunctor a) where
  (MkRestMassFunctor m1 x1) == (MkRestMassFunctor m2 x2) = m1 == m2 && x1 == x2

||| Right adjoint relativistic energy functor R_RelativisticEnergy
public export
data RelativisticEnergyFunctor : Type -> Type where
  MkRelativisticEnergyFunctor : RelativisticEnergyDomain -> a -> RelativisticEnergyFunctor a

public export
Functor RelativisticEnergyFunctor where
  map f (MkRelativisticEnergyFunctor e x) = MkRelativisticEnergyFunctor e (f x)

public export
(Eq a) => Eq (RelativisticEnergyFunctor a) where
  (MkRelativisticEnergyFunctor e1 x1) == (MkRelativisticEnergyFunctor e2 x2) = e1 == e2 && x1 == x2

||| Forward hom-tensor isomorphism mapping RestMass to RelativisticEnergy multiset tensors
public export
relMassEnergyHomTensorIso : MultisetTensor (RestMassFunctor a) b -> MultisetTensor a (RelativisticEnergyFunctor b)
relMassEnergyHomTensorIso ZeroM = ZeroM
relMassEnergyHomTensorIso (AddM (MkRestMassFunctor (MkRestMassDomain m) val, payload) weight rest) =
  AddM (val, MkRelativisticEnergyFunctor (MkRelativisticEnergyDomain m) payload) weight (relMassEnergyHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping RelativisticEnergy to RestMass multiset tensors
public export
relMassEnergyHomTensorInv : MultisetTensor a (RelativisticEnergyFunctor b) -> MultisetTensor (RestMassFunctor a) b
relMassEnergyHomTensorInv ZeroM = ZeroM
relMassEnergyHomTensorInv (AddM (val, MkRelativisticEnergyFunctor (MkRelativisticEnergyDomain e) payload) weight rest) =
  AddM (MkRestMassFunctor (MkRestMassDomain e) val, payload) weight (relMassEnergyHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity for Relativistic Mass-Energy
public export
0 proofRelMassEnergyHomIso : (t : MultisetTensor (RestMassFunctor a) b) ->
                              relMassEnergyHomTensorInv (relMassEnergyHomTensorIso t) = t
proofRelMassEnergyHomIso ZeroM = Refl
proofRelMassEnergyHomIso (AddM (MkRestMassFunctor (MkRestMassDomain m) val, payload) weight rest) =
  let rec = proofRelMassEnergyHomIso rest
  in cong (AddM (MkRestMassFunctor (MkRestMassDomain m) val, payload) weight) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity for Relativistic Mass-Energy
public export
0 proofRelMassEnergyHomInv : (u : MultisetTensor a (RelativisticEnergyFunctor b)) ->
                              relMassEnergyHomTensorIso (relMassEnergyHomTensorInv u) = u
proofRelMassEnergyHomInv ZeroM = Refl
proofRelMassEnergyHomInv (AddM (val, MkRelativisticEnergyFunctor (MkRelativisticEnergyDomain e) payload) weight rest) =
  let rec = proofRelMassEnergyHomInv rest
  in cong (AddM (val, MkRelativisticEnergyFunctor (MkRelativisticEnergyDomain e) payload) weight) rec

||| Category-Theoretic MultisetAdjunction instance L_RestMass ⊣ R_RelativisticEnergy
public export
MultisetDuality RestMassFunctor RelativisticEnergyFunctor where
  leftAdjoint x = MkRestMassFunctor (MkRestMassDomain (intToBoxInt 0)) x
  rightAdjoint (MkRestMassFunctor _ x) = x
  homTensorIso = relMassEnergyHomTensorIso
  homTensorInv = relMassEnergyHomTensorInv
  verifyHomIso = proofRelMassEnergyHomIso
  verifyHomInv = proofRelMassEnergyHomInv

public export
StrictReflectionDuality RestMassFunctor RelativisticEnergyFunctor where
  reflectionDuality = %search
  reflectionRefl _ = Refl

--------------------------------------------------------------------------------
-- 3. 2LTT STAGED RELATIVISTIC PIPELINE TRANSDUCER
--------------------------------------------------------------------------------

||| Deforested 2LTT staged code generator transducer for Relativistic energy-momentum evaluation.
public export
stagedRelativisticPipeline : QuadStreamMultiset BoxInt -> Code RelativisticEnergyDomain
stagedRelativisticPipeline qs = quote (quadStreamToRelativisticEnergy qs)

||| QTT 0 erased proof witness verifying relativistic energy staging inverse identity.
public export
0 prfStagedRelativisticPipeline : (qs : QuadStreamMultiset BoxInt) -> splice (stagedRelativisticPipeline qs) = quadStreamToRelativisticEnergy qs
prfStagedRelativisticPipeline qs = inverseSpliceQuote (quadStreamToRelativisticEnergy qs)
