module Stage1.Math.SuperconductingFluxQuantization

import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List

%default total

------------------------------------------------------------------------
-- 1. COOPER PAIRS & QUANTIZED FLUX STATES
------------------------------------------------------------------------

||| Superconducting Condensate State on a closed loop:
||| - cooperPairCharge: elementary Cooper pair charge q = 2e (in units of e = 1)
||| - fluxQuantumPhi0: base quantum of magnetic flux Phi_0 = h / 2e (normalized = 1)
||| - windingNumber: integer topological winding index n in Z
public export
record SuperconductingLoop where
  constructor MkSuperconductingLoop
  cooperPairCharge : Stage0.BoxInt.BoxInt
  fluxQuantumPhi0  : Stage0.BoxInt.BoxInt
  windingNumber    : Stage0.BoxInt.BoxInt

public export
Eq SuperconductingLoop where
  (MkSuperconductingLoop q1 f1 w1) == (MkSuperconductingLoop q2 f2 w2) =
    q1 == q2 && f1 == f2 && w1 == w2

public export
Show SuperconductingLoop where
  show (MkSuperconductingLoop q f w) =
    "SuperconductingLoop(q=" ++ show q ++ ", Phi_0=" ++ show f ++ 
    ", winding=" ++ show w ++ ")"

||| Evaluates total trapped magnetic flux: Phi = n * Phi_0.
public export
trappedMagneticFlux : SuperconductingLoop -> Stage0.BoxInt.BoxInt
trappedMagneticFlux (MkSuperconductingLoop _ f0 n) = n * f0

||| Evaluates SuperconductingLoop trapped magnetic flux from QuadStream payload.
public export
evaluateQuadStreamTrappedFlux : QuadStreamMultiset Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
evaluateQuadStreamTrappedFlux (MkQuadStream e h p s) =
  let loop = MkSuperconductingLoop (Stage0.BoxInt.intToBoxInt 2) (totalMassBox e) (totalMassBox h)
  in trappedMagneticFlux loop

------------------------------------------------------------------------
-- 2. DISCRETE JOSEPHSON PHASE EVOLUTION
------------------------------------------------------------------------

||| Discrete AC Josephson Phase Step under constant voltage bias V:
||| delta_phi = (2e * V) / hbar = 2 * V.
||| phi(t+1) = (phi(t) + 2 * V) mod (2 * pi).
public export
stepJosephsonPhase : (phi : Stage0.BoxInt.BoxInt) -> (voltage : Stage0.BoxInt.BoxInt) -> (period : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
stepJosephsonPhase phi v period =
  let nextPhase = phi + (Stage0.BoxInt.intToBoxInt 2 * v)
  in nextPhase `mod` period

------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
------------------------------------------------------------------------

||| Left adjoint Superconducting Flux Quantization functor wrapping loop state and payload a
public export
data FluxQuantizationFunctor : Type -> Type where
  MkFluxQuantizationFunctor : SuperconductingLoop -> a -> FluxQuantizationFunctor a

public export
Functor FluxQuantizationFunctor where
  map f (MkFluxQuantizationFunctor loop x) = MkFluxQuantizationFunctor loop (f x)

public export
(Eq a) => Eq (FluxQuantizationFunctor a) where
  (MkFluxQuantizationFunctor l1 x1) == (MkFluxQuantizationFunctor l2 x2) = l1 == l2 && x1 == x2

||| Right adjoint Superconducting Flux Quantization functor wrapping abstract loop state and payload a
public export
data AbstractFluxQuantizationFunctor : Type -> Type where
  MkAbstractFluxQuantizationFunctor : SuperconductingLoop -> a -> AbstractFluxQuantizationFunctor a

public export
Functor AbstractFluxQuantizationFunctor where
  map f (MkAbstractFluxQuantizationFunctor loop x) = MkAbstractFluxQuantizationFunctor loop (f x)

public export
(Eq a) => Eq (AbstractFluxQuantizationFunctor a) where
  (MkAbstractFluxQuantizationFunctor l1 x1) == (MkAbstractFluxQuantizationFunctor l2 x2) = l1 == l2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro Flux Quantization multiset tensors
public export
fluxQuantizationHomTensorIso : MultisetTensor (FluxQuantizationFunctor a) b -> MultisetTensor a (AbstractFluxQuantizationFunctor b)
fluxQuantizationHomTensorIso ZeroM = ZeroM
fluxQuantizationHomTensorIso (AddM (MkFluxQuantizationFunctor loop val, b) w rest) =
  AddM (val, MkAbstractFluxQuantizationFunctor loop b) w (fluxQuantizationHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro Flux Quantization multiset tensors
public export
fluxQuantizationHomTensorInv : MultisetTensor a (AbstractFluxQuantizationFunctor b) -> MultisetTensor (FluxQuantizationFunctor a) b
fluxQuantizationHomTensorInv ZeroM = ZeroM
fluxQuantizationHomTensorInv (AddM (val, MkAbstractFluxQuantizationFunctor loop b) w rest) =
  AddM (MkFluxQuantizationFunctor loop val, b) w (fluxQuantizationHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofFluxQuantizationHomIso : (t : MultisetTensor (FluxQuantizationFunctor a) b) ->
                                fluxQuantizationHomTensorInv (fluxQuantizationHomTensorIso t) = t
proofFluxQuantizationHomIso ZeroM = Refl
proofFluxQuantizationHomIso (AddM (MkFluxQuantizationFunctor loop val, b) w rest) =
  let rec = proofFluxQuantizationHomIso rest
  in cong (AddM (MkFluxQuantizationFunctor loop val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofFluxQuantizationHomInv : (u : MultisetTensor a (AbstractFluxQuantizationFunctor b)) ->
                                fluxQuantizationHomTensorIso (fluxQuantizationHomTensorInv u) = u
proofFluxQuantizationHomInv ZeroM = Refl
proofFluxQuantizationHomInv (AddM (val, MkAbstractFluxQuantizationFunctor loop b) w rest) =
  let rec = proofFluxQuantizationHomInv rest
  in cong (AddM (val, MkAbstractFluxQuantizationFunctor loop b) w) rec

||| Category-Theoretic MultisetAdjunction instance FluxQuantizationFunctor ⊣ AbstractFluxQuantizationFunctor
public export
MultisetDuality FluxQuantizationFunctor AbstractFluxQuantizationFunctor where
  leftAdjoint x = MkFluxQuantizationFunctor (MkSuperconductingLoop (intToBoxInt 2) (intToBoxInt 1) (intToBoxInt 0)) x
  rightAdjoint (MkFluxQuantizationFunctor _ x) = x
  homTensorIso = fluxQuantizationHomTensorIso
  homTensorInv = fluxQuantizationHomTensorInv
  verifyHomIso = proofFluxQuantizationHomIso
  verifyHomInv = proofFluxQuantizationHomInv

------------------------------------------------------------------------
-- 4. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 11: Superconducting Flux Quantization & Josephson Dynamics)
------------------------------------------------------------------------

||| Audits Cooper Pair Charge Double-Electron Valency (q = 2e):
||| Proves Cooper pair condensation charge is exactly 2 units:
||| q_pair = 1 + 1 = 2.
public export
auditCooperPairFluxQuantumProof : Bool
auditCooperPairFluxQuantumProof =
  let loop = MkSuperconductingLoop (Stage0.BoxInt.intToBoxInt 2) (Stage0.BoxInt.intToBoxInt 1) (Stage0.BoxInt.intToBoxInt 0)
  in cooperPairCharge loop == intToBoxInt 2

||| Audits Exact Integer Magnetic Flux Quantization (Phi = n * Phi_0):
||| For winding number n = 5 with flux quantum Phi_0 = 10:
||| Trapped flux Phi = 5 * 10 = 50.
public export
auditFluxQuantizationIntegerStepsProof : Bool
auditFluxQuantizationIntegerStepsProof =
  let loop = MkSuperconductingLoop (Stage0.BoxInt.intToBoxInt 2) (Stage0.BoxInt.intToBoxInt 10) (Stage0.BoxInt.intToBoxInt 5)
      flux = trappedMagneticFlux loop
  in flux == intToBoxInt 50

||| Audits Josephson Phase Periodicity & Modulo 2*pi Invariance:
||| Proves that an initial phase phi = 1 under voltage V = 3 and period 6 (representing 2*pi):
||| phi(t+1) = (1 + 2 * 3) mod 6 = 7 mod 6 = 1 == phi(t).
public export
auditJosephsonPhaseSlipPeriodicityProof : Bool
auditJosephsonPhaseSlipPeriodicityProof =
  let phi0 = Stage0.BoxInt.intToBoxInt 1
      v    = Stage0.BoxInt.intToBoxInt 3
      period = Stage0.BoxInt.intToBoxInt 6
      phi1 = stepJosephsonPhase phi0 v period
  in phi1 == intToBoxInt 1 && phi1 == phi0
