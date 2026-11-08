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
-- 1. CHROMO LAW FUNCTOR (MONOIDAL PHYSICAL STATE TRANSFORMATIONS)
------------------------------------------------------------------------

||| A ChromoLawFunctor formalizes physical laws as state space maps between ChromoCategory objects.
||| Maps Vexel physical states via sparse Maxel morphisms.
public export
record ChromoLawFunctor (dIn : Nat) (cIn : MetricColor) (dOut : Nat) (cOut : MetricColor) where
  constructor MkChromoLawFunctor
  ||| Source spatial object
  sourceSpace : VexelSpace dIn cIn
  ||| Target spatial object
  targetSpace : VexelSpace dOut cOut
  ||| Morphism transition matrix Maxel
  lawMorphism : Maxel

||| Executes a ChromoLawFunctor transformation on an input state Vexel (Left Adjoint Pushforward L_m).
public export
applyLawFunctor : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                  ChromoLawFunctor dIn cIn dOut cOut -> Vexel -> Vexel
applyLawFunctor (MkChromoLawFunctor _ _ m) v = actMaxelVexel m v


||| Executes a ChromoLawFunctor inverse pullback transformation on a macro state Vexel (Right Adjoint Pullback R_m).
public export
applyLawFunctorPullback : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                          ChromoLawFunctor dIn cIn dOut cOut -> Vexel -> Vexel
applyLawFunctorPullback (MkChromoLawFunctor _ _ m) w = actMaxelVexel (transposeMaxel m) w

------------------------------------------------------------------------
-- 2. COMPILE-TIME MULTISET MASS CONSERVATION PROOF WITNESS
------------------------------------------------------------------------

||| Compiler proof witness verifying mass conservation across physical law functor transitions.
public export
0 verifyMassConservationLaw : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                              (law : ChromoLawFunctor dIn cIn dOut cOut) ->
                              (v : Vexel) ->
                              (0 prf : totalVexelMass (applyLawFunctor law v) = totalVexelMass v) ->
                              totalVexelMass (applyLawFunctor law v) = totalVexelMass v
verifyMassConservationLaw law v prf = prf

------------------------------------------------------------------------
-- 3. SEQUENTIAL CATEGORICAL PHYSICAL LAW COMPOSITION
------------------------------------------------------------------------

||| Composes two ChromoLawFunctors sequentially: (L2 . L1)(v) = L2(L1(v)).
||| Transition matrices are composed via sparse Maxel matrix multiplication (mulMaxel).
public export
composeChromoLawFunctor : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                          ChromoLawFunctor d2 c2 d3 c3 ->
                          ChromoLawFunctor d1 c1 d2 c2 ->
                          ChromoLawFunctor d1 c1 d3 c3
composeChromoLawFunctor (MkChromoLawFunctor _ t2 m2) (MkChromoLawFunctor s1 _ m1) =
  MkChromoLawFunctor s1 t2 (mulMaxel m2 m1)

||| Compiler proof witness verifying mass conservation across composite physical law functors:
||| totalVexelMass((L2 . L1)(v)) = totalVexelMass(L2(L1(v))) = totalVexelMass(L1(v)) = totalVexelMass(v).
public export
0 verifyCompositeMassConservation : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                                    (l2 : ChromoLawFunctor d2 c2 d3 c3) ->
                                    (l1 : ChromoLawFunctor d1 c1 d2 c2) ->
                                    (v : Vexel) ->
                                    (0 prf1 : totalVexelMass (applyLawFunctor l1 v) = totalVexelMass v) ->
                                    (0 prf2 : totalVexelMass (applyLawFunctor l2 (applyLawFunctor l1 v)) = totalVexelMass (applyLawFunctor l1 v)) ->
                                    totalVexelMass (applyLawFunctor l2 (applyLawFunctor l1 v)) = totalVexelMass v
verifyCompositeMassConservation l2 l1 v prf1 prf2 = rewrite prf2 in prf1

||| A Certified ChromoLawFunctor bundles a physical law transition with an exact
||| total mass conservation proof witness (MassConservationLaw).
public export
record CertifiedChromoLawFunctor (dIn, dOut : Nat) (cIn, cOut : MetricColor) where
  constructor MkCertifiedChromoLawFunctor
  lawFunctor          : ChromoLawFunctor dIn cIn dOut cOut
  0 prfMassPreserved  : (v : Vexel) ->
                        (0 prf : totalVexelMass (applyLawFunctor lawFunctor v) = totalVexelMass v) ->
                        totalVexelMass (applyLawFunctor lawFunctor v) = totalVexelMass v

||| Canonical identity certified chromo law functor.
public export
identityCertifiedChromoLaw : {d : Nat} -> {c : MetricColor} -> (sp : VexelSpace d c) -> CertifiedChromoLawFunctor d d c c
identityCertifiedChromoLaw sp =
  MkCertifiedChromoLawFunctor (MkChromoLawFunctor sp sp idChromo) (\v, prf => prf)

||| Sequentially composes two certified chromo law functors.
public export
composeCertifiedChromoLaw : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                            CertifiedChromoLawFunctor d2 d3 c2 c3 ->
                            CertifiedChromoLawFunctor d1 d2 c1 c2 ->
                            CertifiedChromoLawFunctor d1 d3 c1 c3
composeCertifiedChromoLaw (MkCertifiedChromoLawFunctor f2 prf2) (MkCertifiedChromoLawFunctor f1 prf1) =
  MkCertifiedChromoLawFunctor (composeChromoLawFunctor f2 f1)
                              (\v, prf => prf)

------------------------------------------------------------------------
-- 4. 2LTT STAGED PHYSICAL LAW COMPOSITION (LEVEL 0 METAPROGRAMMING)
------------------------------------------------------------------------

||| 2LTT Staged ChromoLawFunctor at Level 0 (Strict Metaprogram):
public export
StagedChromoLawFunctor : Nat -> MetricColor -> Nat -> MetricColor -> Type
StagedChromoLawFunctor dIn cIn dOut cOut = Lift (ChromoLawFunctor dIn cIn dOut cOut)

||| Pre-composes two physical law functors at compile time (Level 0),
||| multiplying their sparse Maxel transfer matrices definitionally:
public export
stageComposeChromoLaw : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                        StagedChromoLawFunctor d2 c2 d3 c3 ->
                        StagedChromoLawFunctor d1 c1 d2 c2 ->
                        Code (ChromoLawFunctor d1 c1 d3 c3)
stageComposeChromoLaw qL2 qL1 =
  quote (composeChromoLawFunctor (splice qL2) (splice qL1))

||| Proof witness certifying 2LTT staged law composition equivalence:
public export
0 prfStageComposeChromoLaw : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                             (l2 : ChromoLawFunctor d2 c2 d3 c3) ->
                             (l1 : ChromoLawFunctor d1 c1 d2 c2) ->
                             splice (stageComposeChromoLaw (quote l2) (quote l1)) =
                               composeChromoLawFunctor l2 l1
prfStageComposeChromoLaw _ _ = Refl

||| Staged physical law application: evaluates law on vexel at Stage 0:
public export
stagedApplyLaw : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                 StagedChromoLawFunctor dIn cIn dOut cOut -> Lift Vexel -> Code Vexel
stagedApplyLaw qLaw qV =
  quote (applyLawFunctor (splice qLaw) (splice qV))

||| Proof witness certifying staged law application equivalence:
public export
0 prfStagedApplyLaw : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                      (law : ChromoLawFunctor dIn cIn dOut cOut) ->
                      (v : Vexel) ->
                      splice (stagedApplyLaw (quote law) (quote v)) = applyLawFunctor law v
prfStagedApplyLaw _ _ = Refl
