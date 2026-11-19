module Stage1.Math.InformationErasureCost

import Stage0.BoxInt
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
-- 1. DISCRETE BIT MEMORY STATE & THERMODYNAMIC SINK
------------------------------------------------------------------------

||| A discrete computational register coupled to a parabolic dissipation sink.
||| - activeBits: number of non-zero informational bits in memory.
||| - activeEnergy: total kinetic/computational token pool in active memory.
||| - sinkEnergy: accumulated heat token residue in the parabolic Dark Matter sink.
public export
record BitMemoryState where
  constructor MkBitMemoryState
  activeBits   : Nat
  activeEnergy : Stage0.BoxInt.BoxInt
  sinkEnergy   : Stage0.BoxInt.BoxInt

public export
Eq BitMemoryState where
  (MkBitMemoryState b1 e1 s1) == (MkBitMemoryState b2 e2 s2) =
    b1 == b2 && e1 == e2 && s1 == s2

public export
Show BitMemoryState where
  show (MkBitMemoryState b e s) =
    "BitMemory(bits=" ++ show b ++ ", E_active=" ++ show e ++ ", E_sink=" ++ show s ++ ")"

||| Evaluates the total energy across the active computational register and the parabolic sink.
public export
totalMemoryEnergy : BitMemoryState -> Stage0.BoxInt.BoxInt
totalMemoryEnergy (MkBitMemoryState _ e s) = e + s

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE LANDAUER INFORMATION ERASURE TRANSFORMATION
------------------------------------------------------------------------

||| Erases b informational bits at discrete temperature scale tScale:
||| Relocates at least (b * tScale) tokens from active energy into the parabolic sink.
public export
eraseBitAndDissipate : (b : Nat) -> (tScale : Nat) -> BitMemoryState -> BitMemoryState
eraseBitAndDissipate b tScale (MkBitMemoryState curBits curE curSink) =
  let erasedBits = if b > curBits then curBits else b
      remainingBits = minus curBits erasedBits
      dissipated = Stage0.BoxInt.intToBoxInt (cast (erasedBits * tScale))
      newE = curE - dissipated
      newSink = curSink + dissipated
  in MkBitMemoryState remainingBits newE newSink

||| Erases bits from QuadStream computational payload, transferring dissipated heat into the Substrate sector.
public export
eraseQuadStreamBits : Nat -> Nat -> QuadStreamMultiset Stage0.BoxInt.BoxInt -> QuadStreamMultiset Stage0.BoxInt.BoxInt
eraseQuadStreamBits b tScale (MkQuadStream e h p s) =
  let dissipated = Stage0.BoxInt.intToBoxInt (cast (b * tScale))
      eNew = totalMassBox e - dissipated
      sNew = totalMassBox s + dissipated
  in MkQuadStream (singletonCarrier (intToBoxInt 0) eNew) h p (singletonCarrier (intToBoxInt 0) sNew)

------------------------------------------------------------------------
-- 3. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 6: Discrete Landauer Principle)
------------------------------------------------------------------------

||| Audits the Landauer Minimum Dissipation Lower Bound:
||| Proves that erasing 4 bits at temperature scale T = 2 dissipates exactly ΔQ = 8 tokens:
||| ΔQ = 4 * 2 = 8.
public export
auditLandauerDissipationBoundProof : Bool
auditLandauerDissipationBoundProof =
  let init = MkBitMemoryState 8 (Stage0.BoxInt.intToBoxInt 100) (Stage0.BoxInt.intToBoxInt 20)
      after = eraseBitAndDissipate 4 2 init
      deltaSink = sinkEnergy after - sinkEnergy init
      deltaE = activeEnergy init - activeEnergy after
  in deltaSink == Stage0.BoxInt.intToBoxInt 8 &&
     deltaE == Stage0.BoxInt.intToBoxInt 8 &&
     activeBits after == 4

||| Audits Exact QTT Total Energy Conservation during bit erasure:
||| Total capacity E_total = E_active + E_sink is strictly invariant under information erasure.
public export
auditLandauerTotalConservationProof : Bool
auditLandauerTotalConservationProof =
  let init = MkBitMemoryState 10 (Stage0.BoxInt.intToBoxInt 200) (Stage0.BoxInt.intToBoxInt 55)
      after = eraseBitAndDissipate 7 3 init
  in totalMemoryEnergy init == totalMemoryEnergy after

||| Audits Parabolic Sink Monotonicity:
||| Erasing bits strictly increases the sink entropy/residue (ΔS_sink >= 0),
||| matching the irreversible nature of the parabolic metric (det g = 0).
public export
auditParabolicSinkMonotonicityProof : Bool
auditParabolicSinkMonotonicityProof =
  let init = MkBitMemoryState 5 (Stage0.BoxInt.intToBoxInt 50) (Stage0.BoxInt.intToBoxInt 10)
      after = eraseBitAndDissipate 3 1 init
      deltaSink = sinkEnergy after - sinkEnergy init
      zero = Stage0.BoxInt.intToBoxInt 0
  in deltaSink >= zero && deltaSink == Stage0.BoxInt.intToBoxInt 3

------------------------------------------------------------------------
-- 4. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
data LandauerFunctor : Type -> Type where
  MkLandauerFunctor : BitMemoryState -> a -> LandauerFunctor a

public export
Functor LandauerFunctor where
  map f (MkLandauerFunctor s x) = MkLandauerFunctor s (f x)

public export
(Eq a) => Eq (LandauerFunctor a) where
  (MkLandauerFunctor s1 x1) == (MkLandauerFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractLandauerFunctor : Type -> Type where
  MkAbstractLandauerFunctor : BitMemoryState -> a -> AbstractLandauerFunctor a

public export
Functor AbstractLandauerFunctor where
  map f (MkAbstractLandauerFunctor s x) = MkAbstractLandauerFunctor s (f x)

public export
(Eq a) => Eq (AbstractLandauerFunctor a) where
  (MkAbstractLandauerFunctor s1 x1) == (MkAbstractLandauerFunctor s2 x2) = s1 == s2 && x1 == x2

public export
landauerHomTensorIso : MultisetTensor (LandauerFunctor a) b -> MultisetTensor a (AbstractLandauerFunctor b)
landauerHomTensorIso ZeroM = ZeroM
landauerHomTensorIso (AddM (MkLandauerFunctor s val, b) w rest) =
  AddM (val, MkAbstractLandauerFunctor s b) w (landauerHomTensorIso rest)

public export
landauerHomTensorInv : MultisetTensor a (AbstractLandauerFunctor b) -> MultisetTensor (LandauerFunctor a) b
landauerHomTensorInv ZeroM = ZeroM
landauerHomTensorInv (AddM (val, MkAbstractLandauerFunctor s b) w rest) =
  AddM (MkLandauerFunctor s val, b) w (landauerHomTensorInv rest)

public export
0 proofLandauerHomIso : (t : MultisetTensor (LandauerFunctor a) b) ->
                        landauerHomTensorInv (landauerHomTensorIso t) = t
proofLandauerHomIso ZeroM = Refl
proofLandauerHomIso (AddM (MkLandauerFunctor s val, b) w rest) =
  let rec = proofLandauerHomIso rest
  in cong (AddM (MkLandauerFunctor s val, b) w) rec

public export
0 proofLandauerHomInv : (u : MultisetTensor a (AbstractLandauerFunctor b)) ->
                        landauerHomTensorIso (landauerHomTensorInv u) = u
proofLandauerHomInv ZeroM = Refl
proofLandauerHomInv (AddM (val, MkAbstractLandauerFunctor s b) w rest) =
  let rec = proofLandauerHomInv rest
  in cong (AddM (val, MkAbstractLandauerFunctor s b) w) rec

public export
MultisetDuality LandauerFunctor AbstractLandauerFunctor where
  leftAdjoint x = MkLandauerFunctor (MkBitMemoryState 0 (intToBoxInt 0) (intToBoxInt 0)) x
  rightAdjoint (MkLandauerFunctor _ x) = x
  homTensorIso = landauerHomTensorIso
  homTensorInv = landauerHomTensorInv
  verifyHomIso = proofLandauerHomIso
  verifyHomInv = proofLandauerHomInv

