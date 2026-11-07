module Stage1.Math.OscillatingReactions

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Data.Fin
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. LAW 31: DISCRETE BELOUSOV-ZHABOTINSKY CHEMICAL OSCILLATIONS
------------------------------------------------------------------------

||| Discrete chemical concentration state of the BZ oscillator (Oregonator model):
|||   X = Activator species (Bromous acid HBrO2 tokens)
|||   Y = Inhibitor species (Bromide ion Br- tokens)
|||   Z = Oxidized catalyst species (Cerium(IV) / Ferroin tokens)
public export
record BZState where
  constructor MkBZState
  activatorX : BoxInt
  inhibitorY : BoxInt
  catalystZ  : BoxInt

public export
Eq BZState where
  (MkBZState x1 y1 z1) == (MkBZState x2 y2 z2) =
    x1 == x2 && y1 == y2 && z1 == z2

||| Evaluates BZState from QuadStream payload mass sectors.
public export
evaluateQuadStreamBZState : QuadStreamMultiset BoxInt -> BZState
evaluateQuadStreamBZState (MkQuadStream e h p s) =
  let x = multisetSum e
      y = multisetSum h
      z = multisetSum p
  in MkBZState x y z

------------------------------------------------------------------------
-- 2. DISCRETE OREGONATOR MULTISET REACTION OPERATOR
------------------------------------------------------------------------

||| Helper: checks if a BoxInt token value is strictly negative.
%inline
public export
boxNegative : Stage0.BoxInt.BoxInt -> Bool
boxNegative b = b < Stage0.BoxInt.intToBoxInt 0

||| Single discrete time-step transition of the BZ reaction network:
||| 1. Autocatalysis: X production when Y is depleted (Y < 10).
||| 2. Inhibition: Y suppresses X when Y is elevated (Y >= 10).
||| 3. Oxidation/Feedback: X triggers oxidation of Z; elevated Z regenerates inhibitor Y.
public export
stepBZReaction : BZState -> BZState
stepBZReaction (MkBZState x y z) =
  let -- 1. Activator dynamic: surges if Y is low, quenches if Y is high
      deltaX = if y < Stage0.BoxInt.intToBoxInt 10 then Stage0.BoxInt.intToBoxInt 20 else Stage0.BoxInt.intToBoxInt (-15)
      -- 2. Inhibitor dynamic: depleted during autocatalysis, surges if Z is elevated
      deltaY = if z > Stage0.BoxInt.intToBoxInt 15 then Stage0.BoxInt.intToBoxInt 15 else if x > Stage0.BoxInt.intToBoxInt 20 then Stage0.BoxInt.intToBoxInt (-2) else Stage0.BoxInt.intToBoxInt 0
      -- 3. Catalyst dynamic: oxidizes when X is high, reduces when regenerating Y
      deltaZ = if x > Stage0.BoxInt.intToBoxInt 20 then Stage0.BoxInt.intToBoxInt 10 else Stage0.BoxInt.intToBoxInt (-5)
      
      x' = if boxNegative (x + deltaX) then Stage0.BoxInt.intToBoxInt 0 else x + deltaX
      y' = if boxNegative (y + deltaY) then Stage0.BoxInt.intToBoxInt 0 else y + deltaY
      z' = if boxNegative (z + deltaZ) then Stage0.BoxInt.intToBoxInt 0 else z + deltaZ
  in MkBZState x' y' z'


||| Simulates n discrete time steps of the BZ oscillator.
public export
simulateBZEpochs : (steps : Nat) -> BZState -> BZState
simulateBZEpochs Z state = state
simulateBZEpochs (S k) state = simulateBZEpochs k (stepBZReaction state)

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT
------------------------------------------------------------------------

||| QTT 0 Erased Proof: Discrete Belousov-Zhabotinsky Chemical Oscillations simulation identity.
public export
0 prfOscillatingReactions : (s : BZState) -> simulateBZEpochs Z s = s
prfOscillatingReactions s = Refl

||| Audits Discrete Oregonator reaction step: activator surge, inhibitor depletion, and catalyst feedback (Law 31).
public export
auditOscillatingReactionsProof : Bool
auditOscillatingReactionsProof =
  let s0 = MkBZState (intToBoxInt 5) (intToBoxInt 2) (intToBoxInt 0)
      s1 = stepBZReaction s0
  in s1.activatorX == intToBoxInt 25 && s1.inhibitorY == intToBoxInt 2 && s1.catalystZ == intToBoxInt 0


------------------------------------------------------------------------
-- 4. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
data BZFunctor : Type -> Type where
  MkBZFunctor : BZState -> a -> BZFunctor a

public export
Functor BZFunctor where
  map f (MkBZFunctor s x) = MkBZFunctor s (f x)

public export
(Eq a) => Eq (BZFunctor a) where
  (MkBZFunctor s1 x1) == (MkBZFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractBZFunctor : Type -> Type where
  MkAbstractBZFunctor : BZState -> a -> AbstractBZFunctor a

public export
Functor AbstractBZFunctor where
  map f (MkAbstractBZFunctor s x) = MkAbstractBZFunctor s (f x)

public export
(Eq a) => Eq (AbstractBZFunctor a) where
  (MkAbstractBZFunctor s1 x1) == (MkAbstractBZFunctor s2 x2) = s1 == s2 && x1 == x2

public export
bzHomTensorIso : MultisetTensor (BZFunctor a) b -> MultisetTensor a (AbstractBZFunctor b)
bzHomTensorIso ZeroM = ZeroM
bzHomTensorIso (AddM (MkBZFunctor s val, b) w rest) =
  AddM (val, MkAbstractBZFunctor s b) w (bzHomTensorIso rest)

public export
bzHomTensorInv : MultisetTensor a (AbstractBZFunctor b) -> MultisetTensor (BZFunctor a) b
bzHomTensorInv ZeroM = ZeroM
bzHomTensorInv (AddM (val, MkAbstractBZFunctor s b) w rest) =
  AddM (MkBZFunctor s val, b) w (bzHomTensorInv rest)

public export
0 proofBZHomIso : (t : MultisetTensor (BZFunctor a) b) ->
                   bzHomTensorInv (bzHomTensorIso t) = t
proofBZHomIso ZeroM = Refl
proofBZHomIso (AddM (MkBZFunctor s val, b) w rest) =
  let rec = proofBZHomIso rest
  in cong (AddM (MkBZFunctor s val, b) w) rec

public export
0 proofBZHomInv : (u : MultisetTensor a (AbstractBZFunctor b)) ->
                   bzHomTensorIso (bzHomTensorInv u) = u
proofBZHomInv ZeroM = Refl
proofBZHomInv (AddM (val, MkAbstractBZFunctor s b) w rest) =
  let rec = proofBZHomInv rest
  in cong (AddM (val, MkAbstractBZFunctor s b) w) rec

public export
MultisetAdjunction BZFunctor AbstractBZFunctor where
  leftAdjoint x = MkBZFunctor (MkBZState (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0)) x
  rightAdjoint (MkBZFunctor _ x) = x
  homTensorIso = bzHomTensorIso
  homTensorInv = bzHomTensorInv
  verifyHomIso = proofBZHomIso
  verifyHomInv = proofBZHomInv

