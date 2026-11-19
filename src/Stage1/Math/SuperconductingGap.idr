module Stage1.Math.SuperconductingGap

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.ExclusionPrinciple
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Data.Fin
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. LAW 29: DISCRETE BCS SUPERCONDUCTIVITY & ENERGY GAP
------------------------------------------------------------------------

||| Discrete BCS Superconducting State on a multi-fermion lattice.
||| Represents Cooper pair pairing amplitude and discrete energy gap.
public export
record DiscreteBCSState where
  constructor MkBCSState
  ||| Debye cutoff energy tokens (ω_D)
  debyeEnergy : BoxInt
  ||| Pairing coupling strength tokens (V_0)
  couplingStrength : BoxInt
  ||| Electronic density of states tokens (N_0)
  densityOfStates : BoxInt
  ||| Cooper pair condensation energy gap tokens (Δ_0)
  energyGap : BoxInt
  ||| Ground state condensation energy saving (E_cond < 0)
  condensationEnergy : BoxInt

public export
Eq DiscreteBCSState where
  (MkBCSState d1 c1 n1 g1 e1) == (MkBCSState d2 c2 n2 g2 e2) =
    d1 == d2 && c1 == c2 && n1 == n2 && g1 == g2 && e1 == e2

------------------------------------------------------------------------
-- 2. DISCRETE GAP EQUATION & CONDENSATION FREE ENERGY
------------------------------------------------------------------------

||| Computes the discrete BCS energy gap:
||| Δ_0 = (2 * ω_D * couplingStrength * densityOfStates) / (couplingStrength * densityOfStates + 10)
public export
computeBCSGap : (debye : BoxInt) -> (coupling : BoxInt) -> (dos : BoxInt) -> BoxInt
computeBCSGap debye coupling dos =
  let g = coupling * dos
      denom = g + intToBoxInt 10
  in if denom > intToBoxInt 0
        then (intToBoxInt 2 * debye * g) `div` denom
        else intToBoxInt 0

||| Computes the discrete condensation energy saving:
||| E_cond = - (1/2) * N_0 * Δ_0^2
public export
computeCondensationSaving : (dos : BoxInt) -> (gap : BoxInt) -> BoxInt
computeCondensationSaving dos gap =
  let gapSq = gap * gap
      saving = (dos * gapSq) `div` intToBoxInt 2
  in intToBoxInt (-1) * saving

||| Constructs a discrete BCS ground state for given parameters.
public export
synthesizeBCSState : (debye : BoxInt) -> (coupling : BoxInt) -> (dos : BoxInt) -> DiscreteBCSState
synthesizeBCSState debye coupling dos =
  let gap = computeBCSGap debye coupling dos
      cond = computeCondensationSaving dos gap
  in MkBCSState debye coupling dos gap cond

||| Evaluates BCS state from QuadStream payload.
public export
evaluateQuadStreamBCS : QuadStreamMultiset BoxInt -> DiscreteBCSState
evaluateQuadStreamBCS (MkQuadStream e h p s) =
  synthesizeBCSState (totalMassBox e) (totalMassBox h) (totalMassBox p)

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT
------------------------------------------------------------------------

||| Audits Law 29 (Discrete BCS Superconductivity & Energy Gap):
||| 1. Debye energy ω_D = 100, Coupling V_0 = 2, DOS N_0 = 5.
||| 2. Coupling product g = 2 * 5 = 10.
||| 3. Energy Gap Δ_0 = (2 * 100 * 10) / (10 + 10) = 2000 / 20 = 100 tokens.
||| 4. Condensation saving E_cond = - (1/2) * 5 * 100^2 = - (5 * 10000) / 2 = -25000 tokens.
||| 5. Condensation energy is strictly negative (superconducting state is thermodynamically favored).
public export
auditSuperconductingGapProof : Bool
auditSuperconductingGapProof =
  let bcs = synthesizeBCSState (intToBoxInt 100) (intToBoxInt 2) (intToBoxInt 5)
      tGap = energyGap bcs == intToBoxInt 100
      tCond = condensationEnergy bcs == intToBoxInt (-25000)
      tThermodynamic = condensationEnergy bcs < intToBoxInt 0
  in tGap && tCond && tThermodynamic

--------------------------------------------------------------------------------
-- 4. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
--------------------------------------------------------------------------------

||| Left adjoint BCS Superconducting Gap functor wrapping micro state and payload a
public export
data BCSGapFunctor : Type -> Type where
  MkBCSGapFunctor : DiscreteBCSState -> a -> BCSGapFunctor a

public export
Functor BCSGapFunctor where
  map f (MkBCSGapFunctor state x) = MkBCSGapFunctor state (f x)

public export
(Eq a) => Eq (BCSGapFunctor a) where
  (MkBCSGapFunctor s1 x1) == (MkBCSGapFunctor s2 x2) = s1 == s2 && x1 == x2

||| Right adjoint BCS Superconducting Gap functor wrapping macro state and payload a
public export
data AbstractBCSGapFunctor : Type -> Type where
  MkAbstractBCSGapFunctor : DiscreteBCSState -> a -> AbstractBCSGapFunctor a

public export
Functor AbstractBCSGapFunctor where
  map f (MkAbstractBCSGapFunctor state x) = MkAbstractBCSGapFunctor state (f x)

public export
(Eq a) => Eq (AbstractBCSGapFunctor a) where
  (MkAbstractBCSGapFunctor s1 x1) == (MkAbstractBCSGapFunctor s2 x2) = s1 == s2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro BCS gap multiset tensors
public export
bcsGapHomTensorIso : MultisetTensor (BCSGapFunctor a) b -> MultisetTensor a (AbstractBCSGapFunctor b)
bcsGapHomTensorIso ZeroM = ZeroM
bcsGapHomTensorIso (AddM (MkBCSGapFunctor state val, b) w rest) =
  AddM (val, MkAbstractBCSGapFunctor state b) w (bcsGapHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro BCS gap multiset tensors
public export
bcsGapHomTensorInv : MultisetTensor a (AbstractBCSGapFunctor b) -> MultisetTensor (BCSGapFunctor a) b
bcsGapHomTensorInv ZeroM = ZeroM
bcsGapHomTensorInv (AddM (val, MkAbstractBCSGapFunctor state b) w rest) =
  AddM (MkBCSGapFunctor state val, b) w (bcsGapHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofBCSGapHomIso : (t : MultisetTensor (BCSGapFunctor a) b) ->
                     bcsGapHomTensorInv (bcsGapHomTensorIso t) = t
proofBCSGapHomIso ZeroM = Refl
proofBCSGapHomIso (AddM (MkBCSGapFunctor state val, b) w rest) =
  let rec = proofBCSGapHomIso rest
  in cong (AddM (MkBCSGapFunctor state val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofBCSGapHomInv : (u : MultisetTensor a (AbstractBCSGapFunctor b)) ->
                     bcsGapHomTensorIso (bcsGapHomTensorInv u) = u
proofBCSGapHomInv ZeroM = Refl
proofBCSGapHomInv (AddM (val, MkAbstractBCSGapFunctor state b) w rest) =
  let rec = proofBCSGapHomInv rest
  in cong (AddM (val, MkAbstractBCSGapFunctor state b) w) rec

||| Category-Theoretic MultisetAdjunction instance BCSGapFunctor ⊣ AbstractBCSGapFunctor
public export
MultisetDuality BCSGapFunctor AbstractBCSGapFunctor where
  leftAdjoint x = MkBCSGapFunctor (MkBCSState (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0)) x
  rightAdjoint (MkBCSGapFunctor _ x) = x
  homTensorIso = bcsGapHomTensorIso
  homTensorInv = bcsGapHomTensorInv
  verifyHomIso = proofBCSGapHomIso
  verifyHomInv = proofBCSGapHomInv

||| QTT 0 Erased Proof: Superconducting Energy Gap Adjunction Hom-Tensor Duality Invariant
public export
0 prfBCSGapAdjunctionDuality : (t : MultisetTensor (BCSGapFunctor Nat) Nat) ->
                               bcsGapHomTensorInv (bcsGapHomTensorIso t) = t
prfBCSGapAdjunctionDuality = proofBCSGapHomIso




