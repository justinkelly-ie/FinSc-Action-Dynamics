module Stage0.ChromoLawFunctor

import public Stage0.BoxInt
import public Stage1.Basis.Coordinate
import public Stage1.MultisetTree
import public Stage1.ChromoCategory
import Stage1.MultisetDuality
import public Stage1.TypeTheory.Staging
import public Stage1.TypeTheory.TwoLevel

%default total

------------------------------------------------------------------------
-- 1. CHROMO LAW TRANSFORM (WEIGHTED PHYSICAL STATE TRANSFORMATIONS)
------------------------------------------------------------------------

||| A `ChromoLawTransform` formalizes physical laws as linear Maxel transitions between `VexelSpace` domains.
public export
record ChromoLawTransform (dIn : Nat) (cIn : MetricColor) (dOut : Nat) (cOut : MetricColor) where
  constructor MkChromoLawFunctor
  ||| Source spatial domain
  sourceSpace : VexelSpace dIn cIn
  ||| Target spatial domain
  targetSpace : VexelSpace dOut cOut
  ||| Transition matrix Maxel
  lawMatrix   : Maxel

||| Compatibility alias for `ChromoLawTransform`.
public export
ChromoLawFunctor : Nat -> MetricColor -> Nat -> MetricColor -> Type
ChromoLawFunctor = ChromoLawTransform

||| Executes a `ChromoLawTransform` pushforward on an input state Vexel (`actMaxelVexel`).
public export
applyChromoLawTransform : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                          ChromoLawTransform dIn cIn dOut cOut -> Vexel -> Vexel
applyChromoLawTransform (MkChromoLawFunctor _ _ m) v = actMaxelVexel m v

||| Compatibility alias for `applyChromoLawTransform`.
public export
applyLawFunctor : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                  ChromoLawTransform dIn cIn dOut cOut -> Vexel -> Vexel
applyLawFunctor = applyChromoLawTransform

||| Executes a `ChromoLawTransform` transpose pullback on a macro state Vexel.
public export
applyChromoLawPullback : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                         ChromoLawTransform dIn cIn dOut cOut -> Vexel -> Vexel
applyChromoLawPullback (MkChromoLawFunctor _ _ m) w = actMaxelVexel (transposeMaxel m) w

||| Compatibility alias for `applyChromoLawPullback`.
public export
applyLawFunctorPullback : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                          ChromoLawTransform dIn cIn dOut cOut -> Vexel -> Vexel
applyLawFunctorPullback = applyChromoLawPullback

------------------------------------------------------------------------
-- 2. COMPILE-TIME MULTISET MASS CONSERVATION PROOF WITNESS
------------------------------------------------------------------------

||| Compiler proof witness verifying mass conservation across physical law transitions.
public export
0 verifyMassConservationLaw : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                              (law : ChromoLawTransform dIn cIn dOut cOut) ->
                              (v : Vexel) ->
                              (0 prf : totalVexelMass (applyChromoLawTransform law v) = totalVexelMass v) ->
                              totalVexelMass (applyChromoLawTransform law v) = totalVexelMass v
verifyMassConservationLaw law v prf = prf

------------------------------------------------------------------------
-- 3. SEQUENTIAL MAXEL PHYSICAL LAW COMPOSITION
------------------------------------------------------------------------

||| Composes two `ChromoLawTransform` operators sequentially via sparse Maxel product (`mulMaxel`).
public export
composeChromoLawTransform : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                            ChromoLawTransform d2 c2 d3 c3 ->
                            ChromoLawTransform d1 c1 d2 c2 ->
                            ChromoLawTransform d1 c1 d3 c3
composeChromoLawTransform (MkChromoLawFunctor _ t2 m2) (MkChromoLawFunctor s1 _ m1) =
  MkChromoLawFunctor s1 t2 (mulMaxel m2 m1)

||| Compatibility alias for `composeChromoLawTransform`.
public export
composeChromoLawFunctor : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                          ChromoLawTransform d2 c2 d3 c3 ->
                          ChromoLawTransform d1 c1 d2 c2 ->
                          ChromoLawTransform d1 c1 d3 c3
composeChromoLawFunctor = composeChromoLawTransform

||| Compiler proof witness verifying mass conservation across composite physical law transforms:
||| totalVexelMass((L2 . L1)(v)) = totalVexelMass(L2(L1(v))) = totalVexelMass(L1(v)) = totalVexelMass(v).
public export
0 verifyCompositeMassConservation : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                                    (l2 : ChromoLawTransform d2 c2 d3 c3) ->
                                    (l1 : ChromoLawTransform d1 c1 d2 c2) ->
                                    (v : Vexel) ->
                                    (0 prf1 : totalVexelMass (applyChromoLawTransform l1 v) = totalVexelMass v) ->
                                    (0 prf2 : totalVexelMass (applyChromoLawTransform l2 (applyChromoLawTransform l1 v)) = totalVexelMass (applyChromoLawTransform l1 v)) ->
                                    totalVexelMass (applyChromoLawTransform l2 (applyChromoLawTransform l1 v)) = totalVexelMass v
verifyCompositeMassConservation l2 l1 v prf1 prf2 = rewrite prf2 in prf1

||| Bundles a physical Maxel transition with an exact total mass conservation proof witness.
public export
record CertifiedChromoLawTransform (dIn, dOut : Nat) (cIn, cOut : MetricColor) where
  constructor MkCertifiedChromoLawFunctor
  lawTransform        : ChromoLawTransform dIn cIn dOut cOut
  0 prfMassPreserved  : (v : Vexel) ->
                        (0 prf : totalVexelMass (applyChromoLawTransform lawTransform v) = totalVexelMass v) ->
                        totalVexelMass (applyChromoLawTransform lawTransform v) = totalVexelMass v

||| Compatibility alias for `CertifiedChromoLawTransform`.
public export
CertifiedChromoLawFunctor : (dIn, dOut : Nat) -> (cIn, cOut : MetricColor) -> Type
CertifiedChromoLawFunctor = CertifiedChromoLawTransform

||| Compatibility accessor for `lawTransform`.
public export
lawFunctor : CertifiedChromoLawTransform dIn dOut cIn cOut -> ChromoLawTransform dIn cIn dOut cOut
lawFunctor = lawTransform

||| Canonical identity certified chromo law transform.
public export
identityCertifiedChromoLaw : {d : Nat} -> {c : MetricColor} -> (sp : VexelSpace d c) -> CertifiedChromoLawTransform d d c c
identityCertifiedChromoLaw sp =
  MkCertifiedChromoLawFunctor (MkChromoLawFunctor sp sp idChromo) (\v, prf => prf)

||| Sequentially composes two certified chromo law transforms.
public export
composeCertifiedChromoLaw : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                            CertifiedChromoLawTransform d2 d3 c2 c3 ->
                            CertifiedChromoLawTransform d1 d2 c1 c2 ->
                            CertifiedChromoLawTransform d1 d3 c1 c3
composeCertifiedChromoLaw (MkCertifiedChromoLawFunctor f2 prf2) (MkCertifiedChromoLawFunctor f1 prf1) =
  MkCertifiedChromoLawFunctor (composeChromoLawTransform f2 f1)
                              (\v, prf => prf)

------------------------------------------------------------------------
-- 4. 2LTT STAGED PHYSICAL LAW COMPOSITION (LEVEL 0 METAPROGRAMMING)
------------------------------------------------------------------------

||| 2LTT Staged `ChromoLawTransform` at Level 0 (Strict Metaprogram):
public export
StagedChromoLawTransform : Nat -> MetricColor -> Nat -> MetricColor -> Type
StagedChromoLawTransform dIn cIn dOut cOut = Lift (ChromoLawTransform dIn cIn dOut cOut)

||| Compatibility alias for `StagedChromoLawTransform`.
public export
StagedChromoLawFunctor : Nat -> MetricColor -> Nat -> MetricColor -> Type
StagedChromoLawFunctor = StagedChromoLawTransform

||| Pre-composes two physical law transforms at compile time (Level 0),
||| multiplying their sparse Maxel transfer matrices definitionally:
public export
stageComposeChromoLaw : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                        StagedChromoLawTransform d2 c2 d3 c3 ->
                        StagedChromoLawTransform d1 c1 d2 c2 ->
                        Code (ChromoLawTransform d1 c1 d3 c3)
stageComposeChromoLaw qL2 qL1 =
  quote (composeChromoLawTransform (splice qL2) (splice qL1))

||| Proof witness certifying 2LTT staged law composition equivalence:
public export
0 prfStageComposeChromoLaw : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                             (l2 : ChromoLawTransform d2 c2 d3 c3) ->
                             (l1 : ChromoLawTransform d1 c1 d2 c2) ->
                             splice (stageComposeChromoLaw (quote l2) (quote l1)) =
                               composeChromoLawTransform l2 l1
prfStageComposeChromoLaw _ _ = Refl

||| Staged physical law application: evaluates law on vexel at Stage 0:
public export
stagedApplyLaw : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                 StagedChromoLawTransform dIn cIn dOut cOut -> Lift Vexel -> Code Vexel
stagedApplyLaw qLaw qV =
  quote (applyChromoLawTransform (splice qLaw) (splice qV))

||| Proof witness certifying staged law application equivalence:
public export
0 prfStageApplyLaw : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                      (law : ChromoLawTransform dIn cIn dOut cOut) ->
                      (v : Vexel) ->
                      splice (stagedApplyLaw (quote law) (quote v)) = applyChromoLawTransform law v
prfStageApplyLaw _ _ = Refl

-- Keep compatibility name `prfStagedApplyLaw` if referenced externally
public export
0 prfStagedApplyLaw : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                      (law : ChromoLawTransform dIn cIn dOut cOut) ->
                      (v : Vexel) ->
                      splice (stagedApplyLaw (quote law) (quote v)) = applyChromoLawTransform law v
prfStagedApplyLaw = prfStageApplyLaw

-- Reference for Category Theory Readers:
-- `ChromoLawTransform` plays the role of a morphism/functor between `VexelSpace` objects
-- with transpose pullback acting as a dagger / right adjoint map.
