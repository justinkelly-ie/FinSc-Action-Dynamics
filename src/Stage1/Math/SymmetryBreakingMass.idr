module Stage1.Math.SymmetryBreakingMass

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor

%default total

||| Represents a Discrete Higgs Field Vacuum state (v^2, λ, g).
public export
record DiscreteHiggsVacuum where
  constructor MkDiscreteHiggsVacuum
  vevSquared : UnixelFraction  -- v^2 (vacuum expectation value squared)
  lambda     : UnixelFraction  -- λ (self-coupling constant)
  gaugeCoeff : UnixelFraction  -- g (weak gauge coupling constant)

public export
Eq DiscreteHiggsVacuum where
  (MkDiscreteHiggsVacuum v1 l1 g1) == (MkDiscreteHiggsVacuum v2 l2 g2) =
    v1 == v2 && l1 == l2 && g1 == g2

||| Computes the Discrete Higgs Potential V(φ) = λ * (φ^2 - v^2/2)^2.
public export
%inline
discreteHiggsPotential : DiscreteHiggsVacuum -> UnixelFraction -> UnixelFraction
discreteHiggsPotential (MkDiscreteHiggsVacuum vevSq lam _) phiSq =
  let halfVev = mulUnixelFraction (mkUnixelFraction (intToBoxInt 1) 2) vevSq
      diff = subUnixelFraction phiSq halfVev
  in mulUnixelFraction lam (mulUnixelFraction diff diff)

||| Verifies that spontaneous symmetry breaking ground state expectation value φ^2 = v^2/2
||| achieves the absolute minimum discrete potential V(φ) = 0.
public export
%inline
auditHiggsVacuumStabilityProof : Bool
auditHiggsVacuumStabilityProof =
  let vac = MkDiscreteHiggsVacuum (mkUnixelFraction (intToBoxInt 246) 1) (mkUnixelFraction (intToBoxInt 1) 8) (mkUnixelFraction (intToBoxInt 2) 3)
      phiGround = mkUnixelFraction (intToBoxInt 123) 1
      vMin = discreteHiggsPotential vac phiGround
  in boxIsZero (num vMin)

||| Computes the exact rational gauge boson mass squared m_W^2 = (1/4) * g^2 * v^2.
public export
wBosonMassSquared : DiscreteHiggsVacuum -> UnixelFraction
wBosonMassSquared (MkDiscreteHiggsVacuum vevSq _ g) =
  let quarter = mkUnixelFraction (intToBoxInt 1) 4
      gSq = mulUnixelFraction g g
  in mulUnixelFraction quarter (mulUnixelFraction gSq vevSq)

||| Evaluates W Boson mass squared from QuadStream payload.
public export
evaluateQuadStreamWBosonMassSquared : QuadStreamMultiset BoxInt -> UnixelFraction
evaluateQuadStreamWBosonMassSquared (MkQuadStream e h p s) =
  let vevSq = mkUnixelFractionBox (totalMassBox e) (totalMassBox h)
      lam = mkUnixelFraction (intToBoxInt 1) 8
      g = mkUnixelFraction (intToBoxInt 2) 3
      vac = MkDiscreteHiggsVacuum vevSq lam g
  in wBosonMassSquared vac

------------------------------------------------------------------------
-- 2. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
data HiggsVacuumFunctor : Type -> Type where
  MkHiggsVacuumFunctor : DiscreteHiggsVacuum -> a -> HiggsVacuumFunctor a

public export
Functor HiggsVacuumFunctor where
  map f (MkHiggsVacuumFunctor v x) = MkHiggsVacuumFunctor v (f x)

public export
(Eq a) => Eq (HiggsVacuumFunctor a) where
  (MkHiggsVacuumFunctor v1 x1) == (MkHiggsVacuumFunctor v2 x2) = v1 == v2 && x1 == x2

public export
data AbstractHiggsVacuumFunctor : Type -> Type where
  MkAbstractHiggsVacuumFunctor : DiscreteHiggsVacuum -> a -> AbstractHiggsVacuumFunctor a

public export
Functor AbstractHiggsVacuumFunctor where
  map f (MkAbstractHiggsVacuumFunctor v x) = MkAbstractHiggsVacuumFunctor v (f x)

public export
(Eq a) => Eq (AbstractHiggsVacuumFunctor a) where
  (MkAbstractHiggsVacuumFunctor v1 x1) == (MkAbstractHiggsVacuumFunctor v2 x2) = v1 == v2 && x1 == x2

public export
higgsVacuumHomTensorIso : MultisetTensor (HiggsVacuumFunctor a) b -> MultisetTensor a (AbstractHiggsVacuumFunctor b)
higgsVacuumHomTensorIso ZeroM = ZeroM
higgsVacuumHomTensorIso (AddM (MkHiggsVacuumFunctor v val, b) w rest) =
  AddM (val, MkAbstractHiggsVacuumFunctor v b) w (higgsVacuumHomTensorIso rest)

public export
higgsVacuumHomTensorInv : MultisetTensor a (AbstractHiggsVacuumFunctor b) -> MultisetTensor (HiggsVacuumFunctor a) b
higgsVacuumHomTensorInv ZeroM = ZeroM
higgsVacuumHomTensorInv (AddM (val, MkAbstractHiggsVacuumFunctor v b) w rest) =
  AddM (MkHiggsVacuumFunctor v val, b) w (higgsVacuumHomTensorInv rest)

public export
0 proofHiggsVacuumHomIso : (t : MultisetTensor (HiggsVacuumFunctor a) b) ->
                           higgsVacuumHomTensorInv (higgsVacuumHomTensorIso t) = t
proofHiggsVacuumHomIso ZeroM = Refl
proofHiggsVacuumHomIso (AddM (MkHiggsVacuumFunctor v val, b) w rest) =
  let rec = proofHiggsVacuumHomIso rest
  in cong (AddM (MkHiggsVacuumFunctor v val, b) w) rec

public export
0 proofHiggsVacuumHomInv : (u : MultisetTensor a (AbstractHiggsVacuumFunctor b)) ->
                           higgsVacuumHomTensorIso (higgsVacuumHomTensorInv u) = u
proofHiggsVacuumHomInv ZeroM = Refl
proofHiggsVacuumHomInv (AddM (val, MkAbstractHiggsVacuumFunctor v b) w rest) =
  let rec = proofHiggsVacuumHomInv rest
  in cong (AddM (val, MkAbstractHiggsVacuumFunctor v b) w) rec

public export
MultisetDuality HiggsVacuumFunctor AbstractHiggsVacuumFunctor where
  leftAdjoint x = MkHiggsVacuumFunctor (MkDiscreteHiggsVacuum (mkUnixelFraction (intToBoxInt 0) 1) (mkUnixelFraction (intToBoxInt 0) 1) (mkUnixelFraction (intToBoxInt 0) 1)) x
  rightAdjoint (MkHiggsVacuumFunctor _ x) = x
  homTensorIso = higgsVacuumHomTensorIso
  homTensorInv = higgsVacuumHomTensorInv
  verifyHomIso = proofHiggsVacuumHomIso
  verifyHomInv = proofHiggsVacuumHomInv

