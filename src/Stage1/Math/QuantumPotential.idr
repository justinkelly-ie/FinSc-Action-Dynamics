module Stage1.Math.QuantumPotential

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.Multiset
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage0.ActionPrinciple
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 27: DISCRETE BOHMIAN QUANTUM POTENTIAL & CAUSAL TRAJECTORIES
------------------------------------------------------------------------

||| Computes the exact discrete Bohmian Quantum Potential from amplitude R and its Laplacian Delta R:
||| Q = - (Delta R) / (2 * R) (in exact UnixelFraction units).
public export
discreteQuantumPotential : (laplacianR : Stage0.BoxInt.BoxInt) -> (amplitudeR : Nat) -> Stage1.UnixelFraction.UnixelFraction
discreteQuantumPotential lapR r =
  let denom = if r == 0 then 1 else 2 * r
  in Stage1.UnixelFraction.MkUnixelFraction (- lapR) (MkUnixel denom)

||| Evaluates discrete Bohmian quantum potential across QuadStream payload.
public export
evaluateQuadStreamBohmianPotential : Stage0.BoxInt.BoxInt -> QuadStreamMultiset Stage0.BoxInt.BoxInt -> Stage1.UnixelFraction.UnixelFraction
evaluateQuadStreamBohmianPotential lapR (MkQuadStream e h p s) =
  let rVal = boxIntToPositiveNat (multisetSum e + multisetSum h)
  in discreteQuantumPotential lapR rVal

||| Total Discrete Bohmian Particle Energy along a causal trajectory:
||| E_total = E_kin + V_classical + Q_quantum
public export
bohmianTotalEnergy : (kin : Stage0.BoxInt.BoxInt) -> (vClassical : Stage0.BoxInt.BoxInt) -> (qQuantum : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
bohmianTotalEnergy k v q = k + v + q

------------------------------------------------------------------------
-- 2. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
------------------------------------------------------------------------

||| Left adjoint Bohmian Quantum Potential functor wrapping potential state and payload a
public export
data BohmianPotentialFunctor : Type -> Type where
  MkBohmianPotentialFunctor : UnixelFraction -> a -> BohmianPotentialFunctor a

public export
Functor BohmianPotentialFunctor where
  map f (MkBohmianPotentialFunctor q x) = MkBohmianPotentialFunctor q (f x)

public export
(Eq a) => Eq (BohmianPotentialFunctor a) where
  (MkBohmianPotentialFunctor q1 x1) == (MkBohmianPotentialFunctor q2 x2) = q1 == q2 && x1 == x2

||| Right adjoint Bohmian Quantum Potential functor wrapping abstract potential state and payload a
public export
data AbstractBohmianPotentialFunctor : Type -> Type where
  MkAbstractBohmianPotentialFunctor : UnixelFraction -> a -> AbstractBohmianPotentialFunctor a

public export
Functor AbstractBohmianPotentialFunctor where
  map f (MkAbstractBohmianPotentialFunctor q x) = MkAbstractBohmianPotentialFunctor q (f x)

public export
(Eq a) => Eq (AbstractBohmianPotentialFunctor a) where
  (MkAbstractBohmianPotentialFunctor q1 x1) == (MkAbstractBohmianPotentialFunctor q2 x2) = q1 == q2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro Bohmian potential multiset tensors
public export
bohmianPotentialHomTensorIso : MultisetTensor (BohmianPotentialFunctor a) b -> MultisetTensor a (AbstractBohmianPotentialFunctor b)
bohmianPotentialHomTensorIso ZeroM = ZeroM
bohmianPotentialHomTensorIso (AddM (MkBohmianPotentialFunctor q val, b) w rest) =
  AddM (val, MkAbstractBohmianPotentialFunctor q b) w (bohmianPotentialHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro Bohmian potential multiset tensors
public export
bohmianPotentialHomTensorInv : MultisetTensor a (AbstractBohmianPotentialFunctor b) -> MultisetTensor (BohmianPotentialFunctor a) b
bohmianPotentialHomTensorInv ZeroM = ZeroM
bohmianPotentialHomTensorInv (AddM (val, MkAbstractBohmianPotentialFunctor q b) w rest) =
  AddM (MkBohmianPotentialFunctor q val, b) w (bohmianPotentialHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofBohmianPotentialHomIso : (t : MultisetTensor (BohmianPotentialFunctor a) b) ->
                                bohmianPotentialHomTensorInv (bohmianPotentialHomTensorIso t) = t
proofBohmianPotentialHomIso ZeroM = Refl
proofBohmianPotentialHomIso (AddM (MkBohmianPotentialFunctor q val, b) w rest) =
  let rec = proofBohmianPotentialHomIso rest
  in cong (AddM (MkBohmianPotentialFunctor q val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofBohmianPotentialHomInv : (u : MultisetTensor a (AbstractBohmianPotentialFunctor b)) ->
                                bohmianPotentialHomTensorIso (bohmianPotentialHomTensorInv u) = u
proofBohmianPotentialHomInv ZeroM = Refl
proofBohmianPotentialHomInv (AddM (val, MkAbstractBohmianPotentialFunctor q b) w rest) =
  let rec = proofBohmianPotentialHomInv rest
  in cong (AddM (val, MkAbstractBohmianPotentialFunctor q b) w) rec

||| Category-Theoretic MultisetAdjunction instance BohmianPotentialFunctor ⊣ AbstractBohmianPotentialFunctor
public export
MultisetAdjunction BohmianPotentialFunctor AbstractBohmianPotentialFunctor where
  leftAdjoint x = MkBohmianPotentialFunctor zeroUnixelFraction x
  rightAdjoint (MkBohmianPotentialFunctor _ x) = x
  homTensorIso = bohmianPotentialHomTensorIso
  homTensorInv = bohmianPotentialHomTensorInv
  verifyHomIso = proofBohmianPotentialHomIso
  verifyHomInv = proofBohmianPotentialHomInv

------------------------------------------------------------------------
-- 3. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 27: Discrete Bohmian Potential)
------------------------------------------------------------------------

||| QTT 0 Erased Proof: Discrete Bohmian Quantum Potential Adjunction Hom-Tensor Invariant.
public export
0 prfQuantumPotential : (t : MultisetTensor (BohmianPotentialFunctor a) b) ->
                        bohmianPotentialHomTensorInv (bohmianPotentialHomTensorIso t) = t
prfQuantumPotential = proofBohmianPotentialHomIso

||| Audits Discrete Bohmian Quantum Potential and total energy along causal trajectories (Law 27).
public export
auditQuantumPotentialProof : Bool
auditQuantumPotentialProof =
  let lapR = intToBoxInt 4
      r = 2
      q = discreteQuantumPotential lapR r
      eTotal = bohmianTotalEnergy (intToBoxInt 10) (intToBoxInt 5) (intToBoxInt (-1))
  in q.num == intToBoxInt (-4) && denominatorNat q == 4 && eTotal == intToBoxInt 14


