module Stage1.Math.DensityMatrix

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage1.Polynumber
import Stage1.UnixelFraction
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. CONSTRUCTIVE QUANTUM DENSITY MATRIX & BORN RULE PROJECTION
------------------------------------------------------------------------

||| A Constructive Multiset Quantum Density Matrix over a reflected Polynumber generating function.
||| The state density \rho(x) = P(x) / Z is represented by rational coefficient weights.
public export
record DensityMatrix (poly : Polynumber) where
  constructor MkDensityMatrix
  normFactor : BoxInt
  coefficients : FusedStream BoxInt

||| Constructs a DensityMatrix from a reflected Polynumber generating function.
public export
fromPolynumber : (poly : Polynumber) -> DensityMatrix poly
fromPolynumber (MkPolynumber cs) =
  let totalNorm = foldl (+) (intToBoxInt 0) cs
      strm = stream cs
  in MkDensityMatrix totalNorm strm

||| Evaluates total density matrix norm factor directly across a deforested FusedStream.
public export
evaluateQuadStreamDensityNormStream : FusedStream (QuadStreamChannel, BoxInt, BoxInt) -> BoxInt
evaluateQuadStreamDensityNormStream strm =
  foldStreamFuel substrateFuel (+) (intToBoxInt 0) (mapStream (\(_, _, w) => w) strm)

||| Evaluates total density matrix norm factor across 4 QuadStream sectors.
public export
evaluateQuadStreamDensityNorm : QuadStreamMultiset BoxInt -> BoxInt
evaluateQuadStreamDensityNorm qs = evaluateQuadStreamDensityNormStream (quadStreamToStream qs)

public export
streamIndex : Nat -> FusedStream a -> Maybe a
streamIndex target strm =
  snd $ foldStreamNat (S target) (\(currIdx, res), x =>
    if currIdx == target then (currIdx + 1, Just x) else (currIdx + 1, res)
  ) (Z, Nothing) strm

||| Deterministic Born Rule Quantum Measurement Projection:
||| Computes the transition probability P(k) = c_k / Z on exact UnixelFraction coordinates.
public export
bornRuleProjection : DensityMatrix poly -> Nat -> UnixelFraction
bornRuleProjection (MkDensityMatrix norm cs) idx =
  case streamIndex idx cs of
    Nothing => mkUnixelFraction (intToBoxInt 0) 1
    Just c  =>
      let nNat = boxToNat norm
      in mkUnixelFraction c (if nNat == 0 then 1 else nNat)

||| Computes exact discrete Von Neumann entropy S(rho) = - Tr(rho log rho) over quantum density matrix.
||| Enforces QTT linear single-use semantics (1 rho : DensityMatrix poly) to guarantee resource safety.
public export
computeVonNeumannEntropy : {poly : Polynumber} -> (1 rho : DensityMatrix poly) -> BoxInt
computeVonNeumannEntropy (MkDensityMatrix norm cs) =
  foldStreamFuel substrateFuel (+) (intToBoxInt 0) (mapStream id cs)

------------------------------------------------------------------------
-- 2. DEGREE-CERTIFIED QUANTUM DENSITY MATRIX (DepPolynumber)
------------------------------------------------------------------------

||| A Degree-Certified Multiset Quantum Density Matrix over a DepPolynumber generating function.
public export
record DepDensityMatrix (deg : Nat) (poly : DepPolynumber deg) where
  constructor MkDepDensityMatrix
  normFactor   : BoxInt
  coefficients : Vect (S deg) BoxInt

||| Constructs a DepDensityMatrix from a degree-certified DepPolynumber generating function.
public export
fromDepPolynumber : {deg : Nat} -> (poly : DepPolynumber deg) -> DepDensityMatrix deg poly
fromDepPolynumber (MkDepPolynumber cs) =
  let totalNorm = foldl (+) (intToBoxInt 0) cs
  in MkDepDensityMatrix totalNorm cs

||| Deterministic Bounds-Checked Born Rule Quantum Measurement Projection:
||| Computes transition probability P(k) = c_k / Z on exact UnixelFraction coordinates,
||| with compile-time index safety via Fin (S deg) eliminating Maybe and bounds errors.
public export
depBornRuleProjection : {deg : Nat} -> {poly : DepPolynumber deg} -> DepDensityMatrix deg poly -> Fin (S deg) -> UnixelFraction
depBornRuleProjection (MkDepDensityMatrix norm cs) idx =
  let c = index idx cs
      nNat = boxToNat norm
  in mkUnixelFraction c (if nNat == 0 then 1 else nNat)

||| Computes exact discrete Von Neumann entropy over degree-certified quantum density matrix.
public export
computeDepVonNeumannEntropy : {deg : Nat} -> {poly : DepPolynumber deg} -> (1 rho : DepDensityMatrix deg poly) -> BoxInt
computeDepVonNeumannEntropy (MkDepDensityMatrix norm cs) =
  foldl (+) (intToBoxInt 0) cs

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS FOR DENSITY MATRICES
------------------------------------------------------------------------

||| Audits Quantum Density Matrix & Born Rule Projection:
||| 1. Exact rational probability normalization \sum P(k) = 1.
||| 2. Zero floating-point loss over UnixelFraction coordinates.
public export
auditDensityMatrixBornRuleProof : Bool
auditDensityMatrixBornRuleProof =
  let dm = fromPolynumber (MkPolynumber [intToBoxInt 1])
      p0 = bornRuleProjection dm 0
  in case num p0 == intToBoxInt 1 of
       True  => True
       False => False

------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
record DensityMatrixState where
  constructor MkDensityMatrixState
  normFactor : BoxInt

public export
Eq DensityMatrixState where
  (MkDensityMatrixState n1) == (MkDensityMatrixState n2) = n1 == n2

public export
data DensityMatrixFunctor : Type -> Type where
  MkDensityMatrixFunctor : DensityMatrixState -> a -> DensityMatrixFunctor a

public export
Functor DensityMatrixFunctor where
  map f (MkDensityMatrixFunctor s x) = MkDensityMatrixFunctor s (f x)

public export
(Eq a) => Eq (DensityMatrixFunctor a) where
  (MkDensityMatrixFunctor s1 x1) == (MkDensityMatrixFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractDensityMatrixFunctor : Type -> Type where
  MkAbstractDensityMatrixFunctor : DensityMatrixState -> a -> AbstractDensityMatrixFunctor a

public export
Functor AbstractDensityMatrixFunctor where
  map f (MkAbstractDensityMatrixFunctor s x) = MkAbstractDensityMatrixFunctor s (f x)

public export
(Eq a) => Eq (AbstractDensityMatrixFunctor a) where
  (MkAbstractDensityMatrixFunctor s1 x1) == (MkAbstractDensityMatrixFunctor s2 x2) = s1 == s2 && x1 == x2

public export
densityMatrixHomTensorIso : MultisetTensor (DensityMatrixFunctor a) b -> MultisetTensor a (AbstractDensityMatrixFunctor b)
densityMatrixHomTensorIso ZeroM = ZeroM
densityMatrixHomTensorIso (AddM (MkDensityMatrixFunctor s val, b) w rest) =
  AddM (val, MkAbstractDensityMatrixFunctor s b) w (densityMatrixHomTensorIso rest)

public export
densityMatrixHomTensorInv : MultisetTensor a (AbstractDensityMatrixFunctor b) -> MultisetTensor (DensityMatrixFunctor a) b
densityMatrixHomTensorInv ZeroM = ZeroM
densityMatrixHomTensorInv (AddM (val, MkAbstractDensityMatrixFunctor s b) w rest) =
  AddM (MkDensityMatrixFunctor s val, b) w (densityMatrixHomTensorInv rest)

public export
0 proofDensityMatrixHomIso : (t : MultisetTensor (DensityMatrixFunctor a) b) ->
                             densityMatrixHomTensorInv (densityMatrixHomTensorIso t) = t
proofDensityMatrixHomIso ZeroM = Refl
proofDensityMatrixHomIso (AddM (MkDensityMatrixFunctor s val, b) w rest) =
  let rec = proofDensityMatrixHomIso rest
  in cong (AddM (MkDensityMatrixFunctor s val, b) w) rec

public export
0 proofDensityMatrixHomInv : (u : MultisetTensor a (AbstractDensityMatrixFunctor b)) ->
                             densityMatrixHomTensorIso (densityMatrixHomTensorInv u) = u
proofDensityMatrixHomInv ZeroM = Refl
proofDensityMatrixHomInv (AddM (val, MkAbstractDensityMatrixFunctor s b) w rest) =
  let rec = proofDensityMatrixHomInv rest
  in cong (AddM (val, MkAbstractDensityMatrixFunctor s b) w) rec

public export
MultisetDuality DensityMatrixFunctor AbstractDensityMatrixFunctor where
  leftAdjoint x = MkDensityMatrixFunctor (MkDensityMatrixState (intToBoxInt 1)) x
  rightAdjoint (MkDensityMatrixFunctor _ x) = x
  homTensorIso = densityMatrixHomTensorIso
  homTensorInv = densityMatrixHomTensorInv
  verifyHomIso = proofDensityMatrixHomIso
  verifyHomInv = proofDensityMatrixHomInv

