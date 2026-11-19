module Stage1.Math.GravitationalCollapseLimit

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.ExclusionPrinciple
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 24: DISCRETE TOLMAN-OPPENHEIMER-VOLKOFF (TOV) GRAVITATIONAL MASS LIMIT
------------------------------------------------------------------------

||| Maximum stable discrete mass capacity for a compact degenerate core
||| before gravitational shear exceeds Pauli degeneracy pressure.
||| Equal to the Alpha Cluster Capacity: M_TOV = 108 tokens.
public export
maxTOVMassLimit : Nat
maxTOVMassLimit = 108

||| Checks whether a degenerate core with token mass M is gravitationally stable:
||| Stable: M <= M_TOV (108)
||| Collapsed: M > M_TOV (collapses to a holographic boundary Area=54)
public export
isTOVGravitationallyStable : (coreMass : Nat) -> Bool
isTOVGravitationallyStable m = m <= maxTOVMassLimit

||| Evaluates TOV gravitational collapse stability across QuadStream mass distribution.
public export
isTOVQuadStreamStable : QuadStreamMultiset Stage0.BoxInt.BoxInt -> Bool
isTOVQuadStreamStable (MkQuadStream e h p s) =
  let totalM = totalMassBox e + totalMassBox h + totalMassBox p + totalMassBox s
      unwrapNat = boxToNat totalM
  in isTOVGravitationallyStable unwrapNat

||| Discrete Core Evolution State under gravitational accretion:
public export
record StellarCore where
  constructor MkStellarCore
  coreMass     : Nat
  isCollapsed  : Bool
  boundaryArea : Nat

public export
Eq StellarCore where
  (MkStellarCore m1 c1 a1) == (MkStellarCore m2 c2 a2) =
    m1 == m2 && c1 == c2 && a1 == a2

||| Executes one accretion step of dM = 1:
public export
stepCoreAccretion : StellarCore -> StellarCore
stepCoreAccretion (MkStellarCore m _ _) =
  let newM = m + 1
      collapsed = not (isTOVGravitationallyStable newM)
      area = if collapsed then 54 else 0
  in MkStellarCore newM collapsed area

------------------------------------------------------------------------
-- 2. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
------------------------------------------------------------------------

||| Left adjoint TOV Gravitational Collapse functor wrapping stellar core state and payload a
public export
data TOVCollapseFunctor : Type -> Type where
  MkTOVCollapseFunctor : StellarCore -> a -> TOVCollapseFunctor a

public export
Functor TOVCollapseFunctor where
  map f (MkTOVCollapseFunctor core x) = MkTOVCollapseFunctor core (f x)

public export
(Eq a) => Eq (TOVCollapseFunctor a) where
  (MkTOVCollapseFunctor c1 x1) == (MkTOVCollapseFunctor c2 x2) = c1 == c2 && x1 == x2

||| Right adjoint TOV Gravitational Collapse functor wrapping abstract stellar core state and payload a
public export
data AbstractTOVCollapseFunctor : Type -> Type where
  MkAbstractTOVCollapseFunctor : StellarCore -> a -> AbstractTOVCollapseFunctor a

public export
Functor AbstractTOVCollapseFunctor where
  map f (MkAbstractTOVCollapseFunctor core x) = MkAbstractTOVCollapseFunctor core (f x)

public export
(Eq a) => Eq (AbstractTOVCollapseFunctor a) where
  (MkAbstractTOVCollapseFunctor c1 x1) == (MkAbstractTOVCollapseFunctor c2 x2) = c1 == c2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro TOV collapse multiset tensors
public export
tovCollapseHomTensorIso : MultisetTensor (TOVCollapseFunctor a) b -> MultisetTensor a (AbstractTOVCollapseFunctor b)
tovCollapseHomTensorIso ZeroM = ZeroM
tovCollapseHomTensorIso (AddM (MkTOVCollapseFunctor core val, b) w rest) =
  AddM (val, MkAbstractTOVCollapseFunctor core b) w (tovCollapseHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro TOV collapse multiset tensors
public export
tovCollapseHomTensorInv : MultisetTensor a (AbstractTOVCollapseFunctor b) -> MultisetTensor (TOVCollapseFunctor a) b
tovCollapseHomTensorInv ZeroM = ZeroM
tovCollapseHomTensorInv (AddM (val, MkAbstractTOVCollapseFunctor core b) w rest) =
  AddM (MkTOVCollapseFunctor core val, b) w (tovCollapseHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofTOVCollapseHomIso : (t : MultisetTensor (TOVCollapseFunctor a) b) ->
                           tovCollapseHomTensorInv (tovCollapseHomTensorIso t) = t
proofTOVCollapseHomIso ZeroM = Refl
proofTOVCollapseHomIso (AddM (MkTOVCollapseFunctor core val, b) w rest) =
  let rec = proofTOVCollapseHomIso rest
  in cong (AddM (MkTOVCollapseFunctor core val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofTOVCollapseHomInv : (u : MultisetTensor a (AbstractTOVCollapseFunctor b)) ->
                           tovCollapseHomTensorIso (tovCollapseHomTensorInv u) = u
proofTOVCollapseHomInv ZeroM = Refl
proofTOVCollapseHomInv (AddM (val, MkAbstractTOVCollapseFunctor core b) w rest) =
  let rec = proofTOVCollapseHomInv rest
  in cong (AddM (val, MkAbstractTOVCollapseFunctor core b) w) rec

||| Category-Theoretic MultisetAdjunction instance TOVCollapseFunctor ⊣ AbstractTOVCollapseFunctor
public export
MultisetDuality TOVCollapseFunctor AbstractTOVCollapseFunctor where
  leftAdjoint x = MkTOVCollapseFunctor (MkStellarCore 0 False 0) x
  rightAdjoint (MkTOVCollapseFunctor _ x) = x
  homTensorIso = tovCollapseHomTensorIso
  homTensorInv = tovCollapseHomTensorInv
  verifyHomIso = proofTOVCollapseHomIso
  verifyHomInv = proofTOVCollapseHomInv

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT PROOFS
--    (Law 24: Discrete TOV Limit)
------------------------------------------------------------------------

||| Audits Law 24 across stellar core stability:
||| 1. Stable Neutron Core at M = 108 (isCollapsed = False).
||| 2. Critical Super-TOV Accretion at M = 109 triggers immediate horizon collapse (isCollapsed = True, boundaryArea = 54).
||| 3. Sub-TOV stability holds for M = 50.
public export
auditGravitationalCollapseLimitProof : Bool
auditGravitationalCollapseLimitProof =
  let core108 = MkStellarCore 108 False 0
      core109 = stepCoreAccretion core108
  in isTOVGravitationallyStable 50 &&
     isTOVGravitationallyStable 108 &&
     not (isTOVGravitationallyStable 109) &&
     isCollapsed core109 &&
     boundaryArea core109 == 54

