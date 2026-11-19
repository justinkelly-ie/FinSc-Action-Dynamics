module Stage1.Math.PhysicsScaleTransforms

import PhaseUnfolding
import Stage0.ActionPrinciple
import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.Multiset
import Stage1.MultisetTensor
import Stage1.ScaleTransform
import Stage1.MultisetDuality
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws

%default total

||| Concrete physical state wrapping spatial quadrance BoxInt
public export
record ConcretePhysicsState where
  constructor MkConcretePhysics
  spatialQuadrance : Stage0.BoxInt.BoxInt

public export
Eq ConcretePhysicsState where
  (MkConcretePhysics q1) == (MkConcretePhysics q2) = q1 == q2

public export
Show ConcretePhysicsState where
  show (MkConcretePhysics q) = "ConcretePhysics(" ++ show q ++ ")"

||| Maps QuadStreamMultiset spatial state to ConcretePhysicsState.
public export
evaluateQuadStreamConcretePhysics : QuadStreamMultiset Stage0.BoxInt.BoxInt -> ConcretePhysicsState
evaluateQuadStreamConcretePhysics (MkQuadStream e h p s) =
  MkConcretePhysics (totalMassBox e + totalMassBox h + totalMassBox p + totalMassBox s)

||| Abstract macro physical domain state wrapping spatial quadrance BoxInt
public export
record PhysicsMacroDomain where
  constructor MkPhysicsMacro
  spatialQuadrance : Stage0.BoxInt.BoxInt

public export
Eq PhysicsMacroDomain where
  (MkPhysicsMacro q1) == (MkPhysicsMacro q2) = q1 == q2

public export
Show PhysicsMacroDomain where
  show (MkPhysicsMacro q) = "PhysicsMacro(" ++ show q ++ ")"

||| Heterogeneous MultisetScaleAdjunction instance (f_* ⊣ f^*) between ConcretePhysicsState and PhysicsMacroDomain
public export
Stage1.MultisetDuality.MultisetScaleDuality ConcretePhysicsState PhysicsMacroDomain where
  f_pushforward (MkConcretePhysics q) = MkPhysicsMacro q
  f_pullback (MkPhysicsMacro q)       = MkConcretePhysics q
  verifyUnit _   = Refl
  verifyCounit _ = Refl

--------------------------------------------------------------------------------
-- CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
--------------------------------------------------------------------------------

||| Left adjoint physics scale functor L_Physics wrapping concrete states and payload a
public export
data ConcretePhysicsFunctor : Type -> Type where
  MkConcretePhysicsFunctor : ConcretePhysicsState -> a -> ConcretePhysicsFunctor a

public export
Functor ConcretePhysicsFunctor where
  map f (MkConcretePhysicsFunctor c x) = MkConcretePhysicsFunctor c (f x)

public export
(Eq a) => Eq (ConcretePhysicsFunctor a) where
  (MkConcretePhysicsFunctor c1 x1) == (MkConcretePhysicsFunctor c2 x2) = c1 == c2 && x1 == x2

||| Right adjoint physics scale functor R_Physics wrapping PhysicsMacroDomain states and payload a
public export
data AbstractPhysicsFunctor : Type -> Type where
  MkAbstractPhysicsFunctor : PhysicsMacroDomain -> a -> AbstractPhysicsFunctor a

public export
Functor AbstractPhysicsFunctor where
  map f (MkAbstractPhysicsFunctor m x) = MkAbstractPhysicsFunctor m (f x)

public export
(Eq a) => Eq (AbstractPhysicsFunctor a) where
  (MkAbstractPhysicsFunctor m1 x1) == (MkAbstractPhysicsFunctor m2 x2) = m1 == m2 && x1 == x2

||| Forward hom-tensor isomorphism mapping concrete to macro physics scale multiset tensors
public export
physicsHomTensorIso : Stage1.MultisetTensor.MultisetTensor (ConcretePhysicsFunctor a) b -> Stage1.MultisetTensor.MultisetTensor a (AbstractPhysicsFunctor b)
physicsHomTensorIso ZeroM = ZeroM
physicsHomTensorIso (AddM (MkConcretePhysicsFunctor (MkConcretePhysics q) val, b) w rest) =
  AddM (val, MkAbstractPhysicsFunctor (MkPhysicsMacro q) b) w (physicsHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to concrete physics scale multiset tensors
public export
physicsHomTensorInv : Stage1.MultisetTensor.MultisetTensor a (AbstractPhysicsFunctor b) -> Stage1.MultisetTensor.MultisetTensor (ConcretePhysicsFunctor a) b
physicsHomTensorInv ZeroM = ZeroM
physicsHomTensorInv (AddM (val, MkAbstractPhysicsFunctor (MkPhysicsMacro q) b) w rest) =
  AddM (MkConcretePhysicsFunctor (MkConcretePhysics q) val, b) w (physicsHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofPhysicsHomIso : (t : Stage1.MultisetTensor.MultisetTensor (ConcretePhysicsFunctor a) b) ->
                       physicsHomTensorInv (physicsHomTensorIso t) = t
proofPhysicsHomIso ZeroM = Refl
proofPhysicsHomIso (AddM (MkConcretePhysicsFunctor (MkConcretePhysics q) val, b) w rest) =
  let rec = proofPhysicsHomIso rest
  in cong (AddM (MkConcretePhysicsFunctor (MkConcretePhysics q) val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofPhysicsHomInv : (u : Stage1.MultisetTensor.MultisetTensor a (AbstractPhysicsFunctor b)) ->
                       physicsHomTensorIso (physicsHomTensorInv u) = u
proofPhysicsHomInv ZeroM = Refl
proofPhysicsHomInv (AddM (val, MkAbstractPhysicsFunctor (MkPhysicsMacro q) b) w rest) =
  let rec = proofPhysicsHomInv rest
  in cong (AddM (val, MkAbstractPhysicsFunctor (MkPhysicsMacro q) b) w) rec

||| Category-Theoretic MultisetAdjunction instance L_Physics ⊣ R_Physics for physical scale space
public export
Stage1.MultisetDuality.MultisetDuality ConcretePhysicsFunctor AbstractPhysicsFunctor where
  leftAdjoint x = MkConcretePhysicsFunctor (MkConcretePhysics (Stage0.BoxInt.intToBoxInt 0)) x
  rightAdjoint (MkConcretePhysicsFunctor _ x) = x
  homTensorIso = physicsHomTensorIso
  homTensorInv = physicsHomTensorInv
  verifyHomIso = proofPhysicsHomIso
  verifyHomInv = proofPhysicsHomInv

||| 2LTT Subfibration Reflection Duality instance coupling physics multiset duality with QTT 0 erased reflection
public export
StrictReflectionDuality ConcretePhysicsFunctor AbstractPhysicsFunctor where
  reflectionDuality = %search
  reflectionRefl _ = Refl

||| ScaleTransform instance: Maps a 2D physical coordinate (Coord2D) to its spatial quadrance (BoxInt)
public export
ScaleTransform LatticeCoord2D Stage0.BoxInt.BoxInt where
  scaleTransform (MkCoord2D x y) = (x * x) + (y * y)

||| Audits physical coordinate scale transform quadrance invariance:
public export
auditPhysicsScaleTransformProof : Bool
auditPhysicsScaleTransformProof =
  let q = scaleTransform (MkCoord2D (Stage0.BoxInt.intToBoxInt 4) (Stage0.BoxInt.intToBoxInt 3))
  in q == Stage0.BoxInt.intToBoxInt 25

||| Evaluates physical pushforward along an AdjointScaleChain scale jump
public export
evalPhysicsChainPush : Stage1.MultisetDuality.AdjointScaleChain a b -> a -> b
evalPhysicsChainPush = Stage1.MultisetDuality.evalChainPush

||| Evaluates physical pullback along an AdjointScaleChain scale jump
public export
evalPhysicsChainPull : Stage1.MultisetDuality.AdjointScaleChain a b -> b -> a
evalPhysicsChainPull = Stage1.MultisetDuality.evalChainPull

--------------------------------------------------------------------------------
-- 2LTT STAGED MULTISET ACTION INTEGRAL DEFORESTATION
--------------------------------------------------------------------------------

||| 2LTT Staged Action Integral: Evaluates total physical action quadrance from a streaming multiset
||| at compile-time Stage 1 (U_1) and splices out the unboxed scalar BoxInt to Stage 0 (U_0).
%inline public export
stagedPhysicsActionIntegral : Lift (Stage0.Multiset.Carrier Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
stagedPhysicsActionIntegral liftedStream = totalMassBox (splice liftedStream)

||| QTT 0 Erased Proof: Staged Multiset Action Integral Deforestation Invariant
public export
0 prfStagedActionDeforestation : (m : Stage0.Multiset.Carrier Stage0.BoxInt.BoxInt) ->
                                 stagedPhysicsActionIntegral (quote m) = totalMassBox m
prfStagedActionDeforestation _ = Refl


