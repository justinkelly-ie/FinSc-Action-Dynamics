module Stage1.Math.MultiTerminalConduction

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 28: DISCRETE LANDAUER-BÜTTIKER MULTI-TERMINAL CONDUCTION
------------------------------------------------------------------------

||| 3-Terminal Conductance Matrix G_pq (in units of e^2/h):
||| Terminal 1, 2, 3
public export
record ConductanceMatrix3x3 where
  constructor MkConductanceMatrix3x3
  g12 : Nat
  g13 : Nat
  g21 : Nat
  g23 : Nat
  g31 : Nat
  g32 : Nat

public export
Eq ConductanceMatrix3x3 where
  (MkConductanceMatrix3x3 a1 b1 c1 d1 e1 f1) == (MkConductanceMatrix3x3 a2 b2 c2 d2 e2 f2) =
    a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2 && e1 == e2 && f1 == f2

||| Validates Time-Reversal Microscopic Reciprocity: G_pq == G_qp.
public export
isBuettikerReciprocal : ConductanceMatrix3x3 -> Bool
isBuettikerReciprocal (MkConductanceMatrix3x3 g12 g13 g21 g23 g31 g32) =
  g12 == g21 && g13 == g31 && g23 == g32

||| Computes Terminal Currents I_1, I_2, I_3 given Terminal Voltages V_1, V_2, V_3:
||| I_p = sum_{q != p} G_pq * (V_p - V_q)
public export
terminalCurrents : ConductanceMatrix3x3 -> (v1 : Stage0.BoxInt.BoxInt) -> (v2 : Stage0.BoxInt.BoxInt) -> (v3 : Stage0.BoxInt.BoxInt) -> (Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt)
terminalCurrents (MkConductanceMatrix3x3 g12 g13 g21 g23 g31 g32) v1 v2 v3 =
  let g12B = Stage0.BoxInt.natToBoxInt g12
      g13B = Stage0.BoxInt.natToBoxInt g13
      g21B = Stage0.BoxInt.natToBoxInt g21
      g23B = Stage0.BoxInt.natToBoxInt g23
      g31B = Stage0.BoxInt.natToBoxInt g31
      g32B = Stage0.BoxInt.natToBoxInt g32
      i1 = g12B * (v1 - v2) + g13B * (v1 - v3)
      i2 = g21B * (v2 - v1) + g23B * (v2 - v3)
      i3 = g31B * (v3 - v1) + g32B * (v3 - v2)
  in (i1, i2, i3)

||| Evaluates 3-terminal currents across QuadStream voltage payloads.
public export
evaluateQuadStreamTerminalCurrents : ConductanceMatrix3x3 -> QuadStreamMultiset Stage0.BoxInt.BoxInt -> (Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt)
evaluateQuadStreamTerminalCurrents gMat (MkQuadStream e h p s) =
  terminalCurrents gMat (totalMassBox e) (totalMassBox h) (totalMassBox p)

||| Validates Kirchhoff Total Current Conservation: I_1 + I_2 + I_3 == 0.
public export
isKirchhoffConserved : (Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt, Stage0.BoxInt.BoxInt) -> Bool
isKirchhoffConserved (i1, i2, i3) =
  boxIsZero (i1 + i2 + i3)

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 28: Discrete Landauer-Büttiker Conduction)
------------------------------------------------------------------------

||| Audits Law 28 across multi-terminal quantum transport:
||| 1. Matrix G = {g12=2, g13=1, g21=2, g23=3, g31=1, g32=3} is reciprocal (G_pq = G_qp).
||| 2. Voltages V = (10, 5, 2):
|||    I_1 = 2*(10-5) + 1*(10-2) = 2*5 + 1*8 = 18
|||    I_2 = 2*(5-10) + 3*(5-2) = 2*(-5) + 3*3 = -10 + 9 = -1
|||    I_3 = 1*(2-10) + 3*(2-5) = 1*(-8) + 3*(-3) = -8 - 9 = -17
||| 3. Kirchhoff Loop Conservation: 18 + (-1) + (-17) = 0.
public export
auditMultiTerminalConductionProof : Bool
auditMultiTerminalConductionProof =
  let gMat = MkConductanceMatrix3x3 2 1 2 3 1 3
      v1 = Stage0.BoxInt.intToBoxInt 10
      v2 = Stage0.BoxInt.intToBoxInt 5
      v3 = Stage0.BoxInt.intToBoxInt 2
      currs = terminalCurrents gMat v1 v2 v3
      (i1, i2, i3) = currs
  in isBuettikerReciprocal gMat &&
     i1 == Stage0.BoxInt.intToBoxInt 18 &&
     i2 == Stage0.BoxInt.intToBoxInt (-1) &&
     i3 == Stage0.BoxInt.intToBoxInt (-17) &&
     isKirchhoffConserved currs

------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
data BuettikerFunctor : Type -> Type where
  MkBuettikerFunctor : ConductanceMatrix3x3 -> a -> BuettikerFunctor a

public export
Functor BuettikerFunctor where
  map f (MkBuettikerFunctor g x) = MkBuettikerFunctor g (f x)

public export
(Eq a) => Eq (BuettikerFunctor a) where
  (MkBuettikerFunctor g1 x1) == (MkBuettikerFunctor g2 x2) = g1 == g2 && x1 == x2

public export
data AbstractBuettikerFunctor : Type -> Type where
  MkAbstractBuettikerFunctor : ConductanceMatrix3x3 -> a -> AbstractBuettikerFunctor a

public export
Functor AbstractBuettikerFunctor where
  map f (MkAbstractBuettikerFunctor g x) = MkAbstractBuettikerFunctor g (f x)

public export
(Eq a) => Eq (AbstractBuettikerFunctor a) where
  (MkAbstractBuettikerFunctor g1 x1) == (MkAbstractBuettikerFunctor g2 x2) = g1 == g2 && x1 == x2

public export
buettikerHomTensorIso : MultisetTensor (BuettikerFunctor a) b -> MultisetTensor a (AbstractBuettikerFunctor b)
buettikerHomTensorIso ZeroM = ZeroM
buettikerHomTensorIso (AddM (MkBuettikerFunctor g val, b) w rest) =
  AddM (val, MkAbstractBuettikerFunctor g b) w (buettikerHomTensorIso rest)

public export
buettikerHomTensorInv : MultisetTensor a (AbstractBuettikerFunctor b) -> MultisetTensor (BuettikerFunctor a) b
buettikerHomTensorInv ZeroM = ZeroM
buettikerHomTensorInv (AddM (val, MkAbstractBuettikerFunctor g b) w rest) =
  AddM (MkBuettikerFunctor g val, b) w (buettikerHomTensorInv rest)

public export
0 proofBuettikerHomIso : (t : MultisetTensor (BuettikerFunctor a) b) ->
                          buettikerHomTensorInv (buettikerHomTensorIso t) = t
proofBuettikerHomIso ZeroM = Refl
proofBuettikerHomIso (AddM (MkBuettikerFunctor g val, b) w rest) =
  let rec = proofBuettikerHomIso rest
  in cong (AddM (MkBuettikerFunctor g val, b) w) rec

public export
0 proofBuettikerHomInv : (u : MultisetTensor a (AbstractBuettikerFunctor b)) ->
                          buettikerHomTensorIso (buettikerHomTensorInv u) = u
proofBuettikerHomInv ZeroM = Refl
proofBuettikerHomInv (AddM (val, MkAbstractBuettikerFunctor g b) w rest) =
  let rec = proofBuettikerHomInv rest
  in cong (AddM (val, MkAbstractBuettikerFunctor g b) w) rec

public export
MultisetDuality BuettikerFunctor AbstractBuettikerFunctor where
  leftAdjoint x = MkBuettikerFunctor (MkConductanceMatrix3x3 0 0 0 0 0 0) x
  rightAdjoint (MkBuettikerFunctor _ x) = x
  homTensorIso = buettikerHomTensorIso
  homTensorInv = buettikerHomTensorInv
  verifyHomIso = proofBuettikerHomIso
  verifyHomInv = proofBuettikerHomInv

