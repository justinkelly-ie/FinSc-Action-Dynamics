module Stage1.Math.HolonomyPhase

import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor

%default total

------------------------------------------------------------------------
-- 1. DISCRETE GAUSSIAN LINK VARIABLES & WILSON LOOP HOLONOMY
------------------------------------------------------------------------

||| Discrete U(1) Gaussian Integer Link Token: {+1, +i, -1, -i}.
public export
data GaussianLink = PlusOne | PlusI | MinusOne | MinusI

public export
Eq GaussianLink where
  PlusOne  == PlusOne  = True
  PlusI    == PlusI    = True
  MinusOne == MinusOne = True
  MinusI   == MinusI   = True
  _        == _        = False

public export
Show GaussianLink where
  show PlusOne  = "+1"
  show PlusI    = "+i"
  show MinusOne = "-1"
  show MinusI   = "-i"

||| Computes the discrete Gaussian integer product: U_1 * U_2.
public export
mulGaussianLink : GaussianLink -> GaussianLink -> GaussianLink
mulGaussianLink PlusOne  x        = x
mulGaussianLink PlusI    PlusOne  = PlusI
mulGaussianLink PlusI    PlusI    = MinusOne
mulGaussianLink PlusI    MinusOne = MinusI
mulGaussianLink PlusI    MinusI   = PlusOne
mulGaussianLink MinusOne PlusOne  = MinusOne
mulGaussianLink MinusOne PlusI    = MinusI
mulGaussianLink MinusOne MinusOne = PlusOne
mulGaussianLink MinusOne MinusI   = PlusI
mulGaussianLink MinusI   PlusOne  = MinusI
mulGaussianLink MinusI   PlusI    = PlusOne
mulGaussianLink MinusI   MinusOne = PlusI
mulGaussianLink MinusI   MinusI   = MinusOne

||| Computes the Hermitian conjugate / inverse of a Gaussian link variable: U†.
public export
conjGaussianLink : GaussianLink -> GaussianLink
conjGaussianLink PlusOne  = PlusOne
conjGaussianLink PlusI    = MinusI
conjGaussianLink MinusOne = MinusOne
conjGaussianLink MinusI   = PlusI

||| Evaluates the holonomy of a closed discrete Wilson loop:
||| U(C) = ∏_{e ∈ C} U_e.
public export
computeWilsonLoopHolonomy : List GaussianLink -> GaussianLink
computeWilsonLoopHolonomy [] = PlusOne
computeWilsonLoopHolonomy (u :: us) =
  mulGaussianLink u (computeWilsonLoopHolonomy us)

||| Computes the real trace of a Gaussian link variable as a BoxInt: Re(Tr(U)).
public export
traceGaussianLink : GaussianLink -> BoxInt
traceGaussianLink PlusOne  = intToBoxInt 1
traceGaussianLink PlusI    = intToBoxInt 0
traceGaussianLink MinusOne = intToBoxInt (-1)
traceGaussianLink MinusI   = intToBoxInt 0

||| Evaluates GaussianLink holonomy from QuadStream payload sector weights.
public export
evaluateQuadStreamHolonomy : QuadStreamMultiset Stage0.BoxInt.BoxInt -> GaussianLink
evaluateQuadStreamHolonomy (MkQuadStream e h p s) =
  let wE = (cast {to = Integer} (boxToNat (absBox (totalMassBox e)))) `mod` 4
  in case wE of
       0 => PlusOne
       1 => PlusI
       2 => MinusOne
       _ => MinusI

------------------------------------------------------------------------
-- 2. GAUGE INVARIANCE UNDER VERTEX TRANSFORMATIONS
------------------------------------------------------------------------

||| Evaluates local gauge transformation on a link variable: U_{uv} -> V_u * U_{uv} * V_v†.
public export
gaugeTransformLink : GaussianLink -> GaussianLink -> GaussianLink -> GaussianLink
gaugeTransformLink vU uUV vV =
  mulGaussianLink vU (mulGaussianLink uUV (conjGaussianLink vV))

------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
------------------------------------------------------------------------

||| Left adjoint Wilson Loop Holonomy functor wrapping link state and payload a
public export
data WilsonLoopFunctor : Type -> Type where
  MkWilsonLoopFunctor : GaussianLink -> a -> WilsonLoopFunctor a

public export
Functor WilsonLoopFunctor where
  map f (MkWilsonLoopFunctor link x) = MkWilsonLoopFunctor link (f x)

public export
(Eq a) => Eq (WilsonLoopFunctor a) where
  (MkWilsonLoopFunctor l1 x1) == (MkWilsonLoopFunctor l2 x2) = l1 == l2 && x1 == x2

||| Right adjoint Wilson Loop Holonomy functor wrapping abstract link state and payload a
public export
data AbstractWilsonLoopFunctor : Type -> Type where
  MkAbstractWilsonLoopFunctor : GaussianLink -> a -> AbstractWilsonLoopFunctor a

public export
Functor AbstractWilsonLoopFunctor where
  map f (MkAbstractWilsonLoopFunctor link x) = MkAbstractWilsonLoopFunctor link (f x)

public export
(Eq a) => Eq (AbstractWilsonLoopFunctor a) where
  (MkAbstractWilsonLoopFunctor l1 x1) == (MkAbstractWilsonLoopFunctor l2 x2) = l1 == l2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro Wilson loop multiset tensors
public export
wilsonLoopHomTensorIso : MultisetTensor (WilsonLoopFunctor a) b -> MultisetTensor a (AbstractWilsonLoopFunctor b)
wilsonLoopHomTensorIso ZeroM = ZeroM
wilsonLoopHomTensorIso (AddM (MkWilsonLoopFunctor link val, b) w rest) =
  AddM (val, MkAbstractWilsonLoopFunctor link b) w (wilsonLoopHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro Wilson loop multiset tensors
public export
wilsonLoopHomTensorInv : MultisetTensor a (AbstractWilsonLoopFunctor b) -> MultisetTensor (WilsonLoopFunctor a) b
wilsonLoopHomTensorInv ZeroM = ZeroM
wilsonLoopHomTensorInv (AddM (val, MkAbstractWilsonLoopFunctor link b) w rest) =
  AddM (MkWilsonLoopFunctor link val, b) w (wilsonLoopHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofWilsonLoopHomIso : (t : MultisetTensor (WilsonLoopFunctor a) b) ->
                          wilsonLoopHomTensorInv (wilsonLoopHomTensorIso t) = t
proofWilsonLoopHomIso ZeroM = Refl
proofWilsonLoopHomIso (AddM (MkWilsonLoopFunctor link val, b) w rest) =
  let rec = proofWilsonLoopHomIso rest
  in cong (AddM (MkWilsonLoopFunctor link val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofWilsonLoopHomInv : (u : MultisetTensor a (AbstractWilsonLoopFunctor b)) ->
                          wilsonLoopHomTensorIso (wilsonLoopHomTensorInv u) = u
proofWilsonLoopHomInv ZeroM = Refl
proofWilsonLoopHomInv (AddM (val, MkAbstractWilsonLoopFunctor link b) w rest) =
  let rec = proofWilsonLoopHomInv rest
  in cong (AddM (val, MkAbstractWilsonLoopFunctor link b) w) rec

||| Category-Theoretic MultisetAdjunction instance WilsonLoopFunctor ⊣ AbstractWilsonLoopFunctor
public export
MultisetDuality WilsonLoopFunctor AbstractWilsonLoopFunctor where
  leftAdjoint x = MkWilsonLoopFunctor PlusOne x
  rightAdjoint (MkWilsonLoopFunctor _ x) = x
  homTensorIso = wilsonLoopHomTensorIso
  homTensorInv = wilsonLoopHomTensorInv
  verifyHomIso = proofWilsonLoopHomIso
  verifyHomInv = proofWilsonLoopHomInv

------------------------------------------------------------------------
-- 4. CONSTRUCTIVE FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits the Topological Aharonov-Bohm Phase Shift Invariant:
||| Proves that a Wilson loop with π-flux (half-integer quantum flux) evaluates to holonomy -1:
||| U_1 * U_2 * U_3 * U_4 = (+i) * (+i) * (+1) * (+1) = -1.
public export
auditAharonovBohmPhaseShiftProof : Bool
auditAharonovBohmPhaseShiftProof =
  let loopFluxPi = [PlusI, PlusI, PlusOne, PlusOne]
      holonomy = computeWilsonLoopHolonomy loopFluxPi
  in holonomy == MinusOne && boxEq (traceGaussianLink holonomy) (intToBoxInt (-1))

||| Audits the Wilson Loop Gauge Closure Invariant:
||| Proves that a local gauge rotation V = +i preserves the trace of the closed 4-link loop:
||| Tr(U') = Tr(U) = -1.
public export
auditWilsonLoopGaugeClosureProof : Bool
auditWilsonLoopGaugeClosureProof =
  let v0 = PlusI
      v1 = PlusOne
      v2 = MinusI
      v3 = PlusOne
      -- Original links around loop: [e01, e12, e23, e30]
      e01 = PlusI
      e12 = PlusI
      e23 = PlusOne
      e30 = PlusOne
      -- Gauge transformed links
      e01' = gaugeTransformLink v0 e01 v1
      e12' = gaugeTransformLink v1 e12 v2
      e23' = gaugeTransformLink v2 e23 v3
      e30' = gaugeTransformLink v3 e30 v0
      holonomyOrig = computeWilsonLoopHolonomy [e01, e12, e23, e30]
      holonomyGauge = computeWilsonLoopHolonomy [e01', e12', e23', e30']
  in holonomyOrig == holonomyGauge &&
     boxEq (traceGaussianLink holonomyGauge) (intToBoxInt (-1))

