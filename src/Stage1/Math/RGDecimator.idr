module Stage1.Math.RGDecimator

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.Multiset
import Stage1.Polynumber
import Stage1.Basis.Coordinate
import Stage1.Carrier.BalanceArray
import Stage1.UnixelFraction
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. CATEGORICAL RG DECIMATOR INTERFACE
------------------------------------------------------------------------

||| Categorical RG Decimator Interface:
||| Defines coarse-graining projections Pi: Micro -> Macro across discrete lattice scales
||| with determining parameter (| micro) and invariant preservation audit.
public export
interface RGDecimator micro macro | micro where
  decimate : micro -> macro
  isScaleInvariant : micro -> macro -> Bool

------------------------------------------------------------------------
-- 2. 2D & 3D DEC LATTICE BLOCK DECIMATOR
------------------------------------------------------------------------

||| 2x2 Micro Plaquette of 2-Form fluxes [f00, f01, f10, f11]
public export
record Plaquette2x2 where
  constructor MkPlaquette2x2
  f00 : Stage0.BoxInt.BoxInt
  f01 : Stage0.BoxInt.BoxInt
  f10 : Stage0.BoxInt.BoxInt
  f11 : Stage0.BoxInt.BoxInt

public export
Eq Plaquette2x2 where
  (MkPlaquette2x2 a b c d) == (MkPlaquette2x2 e f g h) =
    a == e && b == f && c == g && d == h

||| Evaluates 2x2 micro plaquette from QuadStream payload.
public export
evaluateQuadStreamPlaquette : QuadStreamMultiset Stage0.BoxInt.BoxInt -> Plaquette2x2
evaluateQuadStreamPlaquette (MkQuadStream e h p s) =
  let f00 = multisetSum e
      f01 = multisetSum h
      f10 = multisetSum p
      f11 = multisetSum s
  in MkPlaquette2x2 f00 f01 f10 f11

||| Macro Plaquette aggregated from 2x2 microcells:
||| Macro flux = f00 + f01 + f10 + f11
public export
record MacroPlaquette where
  constructor MkMacroPlaquette
  totalFlux : Stage0.BoxInt.BoxInt

public export
Eq MacroPlaquette where
  (MkMacroPlaquette f1) == (MkMacroPlaquette f2) = f1 == f2

public export
RGDecimator Plaquette2x2 MacroPlaquette where
  decimate (MkPlaquette2x2 a b c d) =
    MkMacroPlaquette (a + b + c + d)
  isScaleInvariant (MkPlaquette2x2 a b c d) (MkMacroPlaquette m) =
    m == (a + b + c + d)

------------------------------------------------------------------------
-- 3. SCALE-INVARIANT TOPOLOGICAL FIXED POINT PRESERVATION
------------------------------------------------------------------------

||| Evaluates discrete topological First Chern Number over a list of decimated macro-plaquettes:
||| C_1 = sum_i MacroPlaquette_i.
public export
decimatedChernNumber : List MacroPlaquette -> Stage0.BoxInt.BoxInt
decimatedChernNumber [] = Stage0.BoxInt.intToBoxInt 0
decimatedChernNumber (MkMacroPlaquette f :: rest) = f + decimatedChernNumber rest

------------------------------------------------------------------------
-- 4. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Categorical RG Decimator & Invariant Fixed Points)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 5. MULTI-SCALE CARET COMPOSITION OF RG TRANSFORMATIONS
------------------------------------------------------------------------

||| A scale transformation operator represented as a scale monomial α^s.
public export
rgScaleOperator : Nat -> Stage1.Polynumber.Polynumber
rgScaleOperator s = Stage1.Polynumber.monomialPolynumber (Stage0.BoxInt.intToBoxInt 1) s

||| A scale transformation operator represented as a degree-certified scale monomial α^s (Rule 03, Item 7).
public export
rgScaleDepOperator : (s : Nat) -> Stage1.Polynumber.DepPolynumber s
rgScaleDepOperator s = Stage1.Polynumber.monomialDepPoly (Stage0.BoxInt.intToBoxInt 1) s

||| Caret composition of successive RG scaling steps:
||| rgScaleOperator s1 ^ rgScaleOperator s2 = rgScaleOperator (s1 * s2)
public export
composeRGScaleSteps : Stage1.Polynumber.Polynumber -> Stage1.Polynumber.Polynumber -> Stage1.Polynumber.Polynumber
composeRGScaleSteps = Stage1.Polynumber.caretPolynumber

||| Caret composition of successive RG scaling steps with compile-time multiplicative degree guarantee (Rule 03, Item 7):
||| rgScaleDepOperator s1 ^ rgScaleDepOperator s2 = rgScaleDepOperator (s1 * s2)
public export
composeRGScaleDepSteps : {s1, s2 : Nat} ->
                         Stage1.Polynumber.DepPolynumber s1 ->
                         Stage1.Polynumber.DepPolynumber s2 ->
                         Stage1.Polynumber.DepPolynumber (s1 * s2)
composeRGScaleDepSteps = Stage1.Polynumber.caretDepPoly

||| Static compile-time proof verifying that RG decimation steps multiply degrees:
||| R_2 ^ R_3 yields degree 2 * 3 = 6.
public export
0 auditRGDecimationDegreeProof :
  (composeRGScaleDepSteps (rgScaleDepOperator 2) (rgScaleDepOperator 3)) = rgScaleDepOperator 6
auditRGDecimationDegreeProof = Refl

------------------------------------------------------------------------
-- 6. DOUBLY STOCHASTIC RG DECIMATION KERNELS (CH. 27)
------------------------------------------------------------------------

||| A 4x4 Magic Maxel RG Decimation Kernel (Sigma = 4):
||| Governs discrete token redistribution between 4 micro-cells and 4 macro-channels.
public export
rgDecimationMagicMaxel : MagicMaxel 4
rgDecimationMagicMaxel =
  MkMagicMaxel [ [1, 2, 0, 1]
               , [2, 0, 1, 1]
               , [0, 1, 2, 1]
               , [1, 1, 1, 1]
               ]

||| Applies the 4x4 Doubly Stochastic RG Decimation Kernel to a 4-channel microstate:
public export
applyRGMagicDecimation : Vect 4 Nat -> Vect 4 Nat
applyRGMagicDecimation = applyMagicMaxel rgDecimationMagicMaxel

||| Structural sum of natural numbers in a vector ensuring compile-time reduction:
public export
vectSum : {n : Nat} -> Vect n Nat -> Nat
vectSum [] = 0
vectSum (x :: xs) = x + vectSum xs

||| Audits 2x2 Block Decimation Additive Invariance & Doubly Stochastic Magic Maxel Decimation:
public export
auditRGDecimatorProof : Bool
auditRGDecimatorProof =
  let p = MkPlaquette2x2 (Stage0.BoxInt.intToBoxInt 1) (Stage0.BoxInt.intToBoxInt 2) (Stage0.BoxInt.intToBoxInt 3) (Stage0.BoxInt.intToBoxInt 4)
      macroP = decimate p
      vIn : Vect 4 Nat = [1, 1, 1, 1]
      vOut = applyRGMagicDecimation vIn
  in isScaleInvariant p macroP &&
     totalFlux macroP == Stage0.BoxInt.intToBoxInt 10 &&
     vectSum vOut == 16

||| Audits Doubly Stochastic Magic Maxel RG Decimation Kernel (Witness 122).
public export
auditRGMagicMaxelDecimationProof : Bool
auditRGMagicMaxelDecimationProof =
  isMagicMaxel rgDecimationMagicMaxel 4 && auditRGDecimatorProof

------------------------------------------------------------------------
-- 7. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
record RGState where
  constructor MkRGState
  scale : Nat

public export
Eq RGState where
  (MkRGState s1) == (MkRGState s2) = s1 == s2

public export
data RGFunctor : Type -> Type where
  MkRGFunctor : RGState -> a -> RGFunctor a

public export
Functor RGFunctor where
  map f (MkRGFunctor s x) = MkRGFunctor s (f x)

public export
(Eq a) => Eq (RGFunctor a) where
  (MkRGFunctor s1 x1) == (MkRGFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractRGFunctor : Type -> Type where
  MkAbstractRGFunctor : RGState -> a -> AbstractRGFunctor a

public export
Functor AbstractRGFunctor where
  map f (MkAbstractRGFunctor s x) = MkAbstractRGFunctor s (f x)

public export
(Eq a) => Eq (AbstractRGFunctor a) where
  (MkAbstractRGFunctor s1 x1) == (MkAbstractRGFunctor s2 x2) = s1 == s2 && x1 == x2

public export
rgHomTensorIso : MultisetTensor (RGFunctor a) b -> MultisetTensor a (AbstractRGFunctor b)
rgHomTensorIso ZeroM = ZeroM
rgHomTensorIso (AddM (MkRGFunctor s val, b) w rest) =
  AddM (val, MkAbstractRGFunctor s b) w (rgHomTensorIso rest)

public export
rgHomTensorInv : MultisetTensor a (AbstractRGFunctor b) -> MultisetTensor (RGFunctor a) b
rgHomTensorInv ZeroM = ZeroM
rgHomTensorInv (AddM (val, MkAbstractRGFunctor s b) w rest) =
  AddM (MkRGFunctor s val, b) w (rgHomTensorInv rest)

public export
0 proofRGHomIso : (t : MultisetTensor (RGFunctor a) b) ->
                   rgHomTensorInv (rgHomTensorIso t) = t
proofRGHomIso ZeroM = Refl
proofRGHomIso (AddM (MkRGFunctor s val, b) w rest) =
  let rec = proofRGHomIso rest
  in cong (AddM (MkRGFunctor s val, b) w) rec

public export
0 proofRGHomInv : (u : MultisetTensor a (AbstractRGFunctor b)) ->
                   rgHomTensorIso (rgHomTensorInv u) = u
proofRGHomInv ZeroM = Refl
proofRGHomInv (AddM (val, MkAbstractRGFunctor s b) w rest) =
  let rec = proofRGHomInv rest
  in cong (AddM (val, MkAbstractRGFunctor s b) w) rec

public export
MultisetAdjunction RGFunctor AbstractRGFunctor where
  leftAdjoint x = MkRGFunctor (MkRGState 1) x
  rightAdjoint (MkRGFunctor _ x) = x
  homTensorIso = rgHomTensorIso
  homTensorInv = rgHomTensorInv
  verifyHomIso = proofRGHomIso
  verifyHomInv = proofRGHomInv


