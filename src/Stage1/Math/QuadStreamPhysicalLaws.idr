||| Quad-Stream Physical Law Integration & Passband Conservation Engine
|||
||| Connects QuadStreamMultiset state bundles, Goh prime factor adjunctions (L_p ⊣ R_p),
||| and cyclotomic passband filters with physical laws (Helmholtz free energy, Wildberger chromogeometry).
module Stage1.Math.QuadStreamPhysicalLaws

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage1.QuadStream
import Stage1.Goh
import Stage1.Math.Transform.MultisetFilter
import Stage1.Math.Transform.ChromogeometryMetric
import Stage1.Math.Transform.QuadStreamDuality
import Stage1.Math.HelmholtzFreeEnergy
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Stage1.FourGeometries
import public Stage1.TypeTheory.Staging
import public Stage1.TypeTheory.TwoLevel
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- 1. QUAD-STREAM PHYSICAL LAW MAPPING & HELMHOLTZ FREE ENERGY
--------------------------------------------------------------------------------

||| Maps QuadStreamMultiset mass distribution to discrete CosmicBudgetPartition (Baryon -> VM, Vacuum -> DE, Substrate -> DM).
public export
quadStreamToCosmicPartition : QuadStreamMultiset BoxInt -> CosmicBudgetPartition
quadStreamToCosmicPartition (MkQuadStream e h p s) =
  let vm = multisetSum e
      de = multisetSum h
      dm = multisetSum s
  in MkCosmicBudgetPartition vm de dm

||| Evaluates discrete Helmholtz Free Energy (F = U - T * S) over a physical QuadStreamMultiset payload.
public export
evalQuadStreamHelmholtzFreeEnergy : (temp : BoxInt) -> QuadStreamMultiset BoxInt -> BoxInt
evalQuadStreamHelmholtzFreeEnergy temp qs =
  discreteHelmholtzFreeEnergy temp (quadStreamToCosmicPartition qs)

--------------------------------------------------------------------------------
-- 2. PHYSICAL CYCLOTOMIC PASSBAND FILTER TRANSFORMATION
--------------------------------------------------------------------------------

||| Applies physical cyclotomic passband filter (Φ_d(s)) concurrently across all 4 sectors of a QuadStreamMultiset payload.
public export
applyPhysicalQuadStreamFilter : (lawDegree : Nat) -> QuadStreamMultiset BoxInt -> QuadStreamMultiset BoxInt
applyPhysicalQuadStreamFilter lawDegree (MkQuadStream e h p s) =
  let filterStream : Multiset BoxInt BoxInt -> Multiset BoxInt BoxInt
      filterStream ZeroM = ZeroM
      filterStream (AddM v w rest) =
        let dBox = intToBoxInt (cast lawDegree)
            rem  = if dBox == intToBoxInt 0 then intToBoxInt 0 else modBox v dBox
        in if rem == intToBoxInt 0
             then AddM v w (filterStream rest)
             else filterStream rest
  in MkQuadStream (filterStream e)
               (filterStream h)
               (filterStream p)
               (filterStream s)

||| Zero-allocation deforested passband filter transducer operating in O(1) auxiliary registers (Rule 04 §8).
public export
filterQuadSectorStream : (lawDegree : Nat) -> FusedStream (BoxInt, BoxInt) -> FusedStream (BoxInt, BoxInt)
filterQuadSectorStream lawDegree =
  filterStream (\(v, _) =>
    let dBox = intToBoxInt (cast lawDegree)
        rem  = if dBox == intToBoxInt 0 then intToBoxInt 0 else modBox v dBox
    in rem == intToBoxInt 0)

||| Applies physical cyclotomic passband filter Φ_p(x) certified by GohPrime p across all 4 sectors.
public export
applyPhysicalGohPrimeFilter : {p : Nat} -> GohPrime p -> QuadStreamMultiset BoxInt -> QuadStreamMultiset BoxInt
applyPhysicalGohPrimeFilter prf qs = applyPhysicalQuadStreamFilter (gohDegree p) qs

--------------------------------------------------------------------------------
-- 3. WILDBERGER CHROMOGEOMETRIC TRIAD METRIC EVALUATION
--------------------------------------------------------------------------------

||| Computes Wildberger Chromogeometric Triad Quadrances (Q_E, Q_H, Q_P) across a physical QuadStreamMultiset payload at (x, y).
public export
evalPhysicalTripleQuadMetric : QuadStreamMultiset BoxInt -> (BoxInt, BoxInt) -> QuadranceTriad
evalPhysicalTripleQuadMetric qs (x, y) = evalQuadStreamQuadrances qs (x, y)

--------------------------------------------------------------------------------
-- 4. QUAD-STREAM COMPOSITE LAW PIPELINE & TOTAL MASS EVALUATION
--------------------------------------------------------------------------------

||| Evaluates total integer mass aggregated across all 4 channels of a physical QuadStreamMultiset.
public export
quadStreamPhysicalMass : QuadStreamMultiset BoxInt -> BoxInt
quadStreamPhysicalMass qs = quadStreamTotalMass qs

||| Composes two Quad-Stream physical law transformations into a single coupled execution step.
public export
composeQuadLaws : (QuadStreamMultiset BoxInt -> QuadStreamMultiset BoxInt) ->
                  (QuadStreamMultiset BoxInt -> QuadStreamMultiset BoxInt) ->
                  QuadStreamMultiset BoxInt -> QuadStreamMultiset BoxInt
composeQuadLaws law1 law2 qs = law2 (law1 qs)

||| Single-pass fused stream pipeline transducer payload result.
public export
record QuadStreamPipelineResult where
  constructor MkQuadStreamPipelineResult
  densityNorm   : BoxInt
  spinorDensity : BoxInt
  chernNumber   : BoxInt

||| Comprehensive multi-law evaluation ledger for Quad-Stream physics.
public export
record PhysicalLawLedger where
  constructor MkLawLedger
  totalMass           : BoxInt
  ellipticMass        : BoxInt
  hyperbolicMass      : BoxInt
  parabolicMass       : BoxInt
  substrateMass       : BoxInt
  spinorDensity       : BoxInt
  chernNumber         : BoxInt
  helmholtzFreeEnergy : BoxInt

public export
Eq PhysicalLawLedger where
  (MkLawLedger m1 e1 h1 p1 s1 sp1 c1 f1) == (MkLawLedger m2 e2 h2 p2 s2 sp2 c2 f2) =
    m1 == m2 && e1 == e2 && h1 == h2 && p1 == p2 && s1 == s2 &&
    sp1 == sp2 && c1 == c2 && f1 == f2

||| Single-pass fused stream pipeline ledger evaluation over a QuadStream payload.
||| Evaluates 4 sector masses, spinor density, Chern invariant, and Helmholtz free energy concurrently.
public export
pipelineQuadStreamLedger : (temp : BoxInt) -> QuadStreamMultiset BoxInt -> PhysicalLawLedger
pipelineQuadStreamLedger temp qs =
  let countNodes = quadStreamNodeCount qs
      fuel = (countNodes * 4) + 16
      strm = quadStreamToStream qs
      (totalNorm, (sumE, sumH, sumP, sumS), c1) =
        foldStreamNat fuel processElement (intToBoxInt 0, (intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0), intToBoxInt 0) strm
      spinorDensityVal = (sumE * sumE) + (sumH * sumH) + (sumP * sumP) + (sumS * sumS)
      fEnergy = discreteHelmholtzFreeEnergy temp (MkCosmicBudgetPartition sumE sumH sumS)
  in MkLawLedger totalNorm sumE sumH sumP sumS spinorDensityVal c1 fEnergy
  where
    quadStreamNodeCount : QuadStreamMultiset a -> Nat
    quadStreamNodeCount (MkQuadStream e h p s) =
      mCount e + mCount h + mCount p + mCount s
      where
        mCount : Multiset countC countElem -> Nat
        mCount ZeroM = 0
        mCount (AddM _ _ rest) = S (mCount rest)

    processElement : (BoxInt, (BoxInt, BoxInt, BoxInt, BoxInt), BoxInt)
                  -> (QuadStreamChannel, BoxInt, BoxInt)
                  -> (BoxInt, (BoxInt, BoxInt, BoxInt, BoxInt), BoxInt)
    processElement (normAcc, (e, h, p, s), c1Acc) (EllipticSector, _, w) =
      (normAcc + w, (e + w, h, p, s), c1Acc + w)
    processElement (normAcc, (e, h, p, s), c1Acc) (HyperbolicSector, _, w) =
      (normAcc + w, (e, h + w, p, s), c1Acc)
    processElement (normAcc, (e, h, p, s), c1Acc) (ParabolicSector, _, w) =
      (normAcc + w, (e, h, p + w, s), c1Acc)
    processElement (normAcc, (e, h, p, s), c1Acc) (SubstrateSector, _, w) =
      (normAcc + w, (e, h, p, s + w), c1Acc)

||| Fuses density matrix norm, relativistic spinor probability density, and topological Chern number
||| evaluations over a QuadStream payload into a single O(1) allocation deforested stream pass.
public export
pipelineQuadStreamTransducer : QuadStreamMultiset BoxInt -> QuadStreamPipelineResult
pipelineQuadStreamTransducer qs =
  let ledger = pipelineQuadStreamLedger (intToBoxInt 1) qs
  in MkQuadStreamPipelineResult ledger.totalMass ledger.spinorDensity ledger.chernNumber

||| Evaluates physical law ledger directly over a deforested stream without intermediate carrier allocations.
public export
fusedPipelineQuadStreamLedgerDirect : (fuel : Nat) -> (temp : BoxInt) -> FusedStream (QuadStreamChannel, BoxInt, BoxInt) -> PhysicalLawLedger
fusedPipelineQuadStreamLedgerDirect fuel temp strm =
  let (totalNorm, (sumE, sumH, sumP, sumS), c1) =
        foldStreamNat fuel processElement (intToBoxInt 0, (intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 0), intToBoxInt 0) strm
      spinorDensityVal = (sumE * sumE) + (sumH * sumH) + (sumP * sumP) + (sumS * sumS)
      fEnergy = discreteHelmholtzFreeEnergy temp (MkCosmicBudgetPartition sumE sumH sumS)
  in MkLawLedger totalNorm sumE sumH sumP sumS spinorDensityVal c1 fEnergy
  where
    processElement : (BoxInt, (BoxInt, BoxInt, BoxInt, BoxInt), BoxInt)
                  -> (QuadStreamChannel, BoxInt, BoxInt)
                  -> (BoxInt, (BoxInt, BoxInt, BoxInt, BoxInt), BoxInt)
    processElement (normAcc, (e, h, p, s), c1Acc) (EllipticSector, _, w) =
      (normAcc + w, (e + w, h, p, s), c1Acc + w)
    processElement (normAcc, (e, h, p, s), c1Acc) (HyperbolicSector, _, w) =
      (normAcc + w, (e, h + w, p, s), c1Acc)
    processElement (normAcc, (e, h, p, s), c1Acc) (ParabolicSector, _, w) =
      (normAcc + w, (e, h, p + w, s), c1Acc)
    processElement (normAcc, (e, h, p, s), c1Acc) (SubstrateSector, _, w) =
      (normAcc + w, (e, h, p, s + w), c1Acc)

||| Evaluates pipeline result directly over a deforested stream.
public export
fusedPipelineQuadStreamTransducerDirect : (fuel : Nat) -> FusedStream (QuadStreamChannel, BoxInt, BoxInt) -> QuadStreamPipelineResult
fusedPipelineQuadStreamTransducerDirect fuel strm =
  let ledger = fusedPipelineQuadStreamLedgerDirect fuel (intToBoxInt 1) strm
  in MkQuadStreamPipelineResult ledger.totalMass ledger.spinorDensity ledger.chernNumber

||| Evaluates physical ledger from a QuadStreamFusedBundle in a single deforested pass.
public export
evalFusedBundleLedger : (fuel : Nat) -> (temp : BoxInt) -> QuadStreamFusedBundle BoxInt -> PhysicalLawLedger
evalFusedBundleLedger fuel temp bundle =
  fusedPipelineQuadStreamLedgerDirect fuel temp (fusedBundleToTaggedStream bundle)

||| Audit witness verifying zero-allocation deforested QuadStream pipeline ledger evaluation.
public export
auditDeforestedQuadStreamPipelineProof : Bool
auditDeforestedQuadStreamPipelineProof =
  let e = stream [ (intToBoxInt 0, natToBoxInt Stage1.FourGeometries.ellipticLatticeCapacity) ]
      h = stream [ (intToBoxInt 0, natToBoxInt Stage1.FourGeometries.hyperbolicRomCapacity) ]
      p = stream [ (intToBoxInt 0, intToBoxInt 0) ]
      s = stream [ (intToBoxInt 0, natToBoxInt Stage1.FourGeometries.darkMatterTriangularResidue) ]
      bundle = MkQuadStreamBundle e h p s
      ledger = evalFusedBundleLedger 10 (intToBoxInt 1) bundle
  in totalMass ledger == intToBoxInt 210 &&
     ellipticMass ledger == intToBoxInt 27 &&
     hyperbolicMass ledger == intToBoxInt 128 &&
     substrateMass ledger == intToBoxInt 55


||| A composable physical law transducer operating on deforested channel streams.
public export
record QuadStreamLawTransducer where
  constructor MkLawTransducer
  lawName   : String
  transduce : FusedStream (QuadStreamChannel, BoxInt, BoxInt) ->
              FusedStream (QuadStreamChannel, BoxInt, BoxInt)

||| Identity law transducer (leaves stream unchanged).
public export
idLawTransducer : QuadStreamLawTransducer
idLawTransducer = MkLawTransducer "IdentityLaw" id

||| Associative composition of physical law stream transducers.
public export
composeLawTransducers : QuadStreamLawTransducer -> QuadStreamLawTransducer -> QuadStreamLawTransducer
composeLawTransducers (MkLawTransducer n1 t1) (MkLawTransducer n2 t2) =
  MkLawTransducer (n1 ++ " ; " ++ n2) (t2 . t1)

||| Cyclotomic passband filter transducer for law degree d.
public export
cyclotomicFilterTransducer : (lawDegree : Nat) -> QuadStreamLawTransducer
cyclotomicFilterTransducer lawDegree =
  MkLawTransducer ("CyclotomicPassband(" ++ show lawDegree ++ ")")
    (filterStream (\(_, v, _) =>
      let dBox = intToBoxInt (cast lawDegree)
          rem  = if dBox == intToBoxInt 0 then intToBoxInt 0 else modBox v dBox
      in rem == intToBoxInt 0
    ))

||| Linear QTT state step applying cyclotomic passband filtering across all 4 channels (Rule 04).
public export
stepQuadStreamLinearPassband : (1 qs : QuadStreamMultiset BoxInt) -> (lawDegree : Nat) -> QuadStreamMultiset BoxInt
stepQuadStreamLinearPassband (MkQuadStream e h p s) lawDegree =
  MkQuadStream (filterM e) (filterM h) (filterM p) (filterM s)
  where
    filterM : (1 m : Multiset BoxInt BoxInt) -> Multiset BoxInt BoxInt
    filterM ZeroM = ZeroM
    filterM (AddM v w rest) =
      let dBox = intToBoxInt (cast lawDegree)
          rem  = if dBox == intToBoxInt 0 then intToBoxInt 0 else modBox v dBox
      in if rem == intToBoxInt 0
           then AddM v w (filterM rest)
           else filterM rest

||| Cyclotomic passband filter transducer certified by GohPrime p.
public export
gohPrimeFilterTransducer : {p : Nat} -> GohPrime p -> QuadStreamLawTransducer
gohPrimeFilterTransducer prf = cyclotomicFilterTransducer (gohDegree p)

||| Linear QTT state step applying cyclotomic passband filtering certified by GohPrime p (Rule 04).
public export
stepQuadStreamLinearGohPrimePassband : (1 qs : QuadStreamMultiset BoxInt) -> {p : Nat} -> GohPrime p -> QuadStreamMultiset BoxInt
stepQuadStreamLinearGohPrimePassband qs prf = stepQuadStreamLinearPassband qs (gohDegree p)

||| Advances a QuadStreamMultiset using a stream law transducer.
public export
stepQuadStreamWithTransducer : QuadStreamMultiset BoxInt -> QuadStreamLawTransducer -> QuadStreamMultiset BoxInt
stepQuadStreamWithTransducer qs tr =
  let strm = quadStreamToStream qs
      transduced = tr.transduce strm
  in streamToQuadStreamNat Stage1.FourGeometries.primorial210Budget transduced

||| Audit verifying comprehensive ledger evaluation on canonical Primorial 210 ground state.
public export
auditPipelineQuadStreamLedgerProof : Bool
auditPipelineQuadStreamLedgerProof =
  let eCap = natToBoxInt Stage1.FourGeometries.ellipticLatticeCapacity
      hCap = natToBoxInt Stage1.FourGeometries.hyperbolicRomCapacity
      dCap = natToBoxInt Stage1.FourGeometries.darkMatterTriangularResidue
      bTot = natToBoxInt Stage1.FourGeometries.primorial210Budget
      testQs = MkQuadStream (AddM (intToBoxInt 1) eCap ZeroM)
                            (AddM (intToBoxInt 1) hCap ZeroM)
                            ZeroM
                            (AddM (intToBoxInt 1) dCap ZeroM)
      ledger = pipelineQuadStreamLedger (intToBoxInt 2) testQs
  in ledger.totalMass == bTot &&
     ledger.ellipticMass == eCap &&
     ledger.hyperbolicMass == hCap &&
     ledger.substrateMass == dCap &&
     ledger.helmholtzFreeEnergy == intToBoxInt (-1320) &&
     ledger.chernNumber == natToBoxInt Stage1.FourGeometries.ellipticLatticeCapacity

||| Audit verifying associativity of composable physical law transducers.
public export
auditComposableLawAssociativityProof : Bool
auditComposableLawAssociativityProof =
  let l1 = cyclotomicFilterTransducer 1
      l2 = cyclotomicFilterTransducer 2
      l3 = cyclotomicFilterTransducer 3
      c1 = composeLawTransducers (composeLawTransducers l1 l2) l3
      c2 = composeLawTransducers l1 (composeLawTransducers l2 l3)
      testQs = MkQuadStream (AddM (intToBoxInt 6) (intToBoxInt 27) ZeroM) ZeroM ZeroM ZeroM
      out1 = stepQuadStreamWithTransducer testQs c1
      out2 = stepQuadStreamWithTransducer testQs c2
  in quadStreamTotalMass out1 == quadStreamTotalMass out2


--------------------------------------------------------------------------------
-- 5. COMPILE-TIME PROOF WITNESSES
--------------------------------------------------------------------------------

||| Static compile-time proof witness verifying physical QuadStream zero-mass vacuum state.
public export
0 verifyPhysicalQuadStreamConservation :
  quadStreamTotalMass (MkQuadStream ZeroM ZeroM ZeroM ZeroM) = intToBoxInt 0
verifyPhysicalQuadStreamConservation = Refl

||| Static compile-time witness verifying composite law identity preservation.
public export
0 verifyCompositeLawIdentity : (qs : QuadStreamMultiset BoxInt) -> composeQuadLaws Prelude.id Prelude.id qs = qs
verifyCompositeLawIdentity qs = Refl

||| Static compile-time witness verifying that GohPrime passband filtering preserves the vacuum.
public export
0 verifyGohPrimeVacuumFiltering : {p : Nat} -> (prf : GohPrime p) ->
  applyPhysicalGohPrimeFilter prf (MkQuadStream ZeroM ZeroM ZeroM ZeroM) = MkQuadStream ZeroM ZeroM ZeroM ZeroM
verifyGohPrimeVacuumFiltering prf = Refl

--------------------------------------------------------------------------------
-- 6. CATEGORY-THEORETIC MULTISET ADJUNCTION
--------------------------------------------------------------------------------

public export
record QuadLawState where
  constructor MkQuadLawState
  lawDegree : Nat

public export
gohPrimeToQuadLawState : {p : Nat} -> GohPrime p -> QuadLawState
gohPrimeToQuadLawState prf = MkQuadLawState (gohDegree p)

public export
Eq QuadLawState where
  (MkQuadLawState l1) == (MkQuadLawState l2) = l1 == l2

public export
data QuadLawFunctor : Type -> Type where
  MkQuadLawFunctor : QuadLawState -> a -> QuadLawFunctor a

public export
Functor QuadLawFunctor where
  map f (MkQuadLawFunctor s x) = MkQuadLawFunctor s (f x)

public export
(Eq a) => Eq (QuadLawFunctor a) where
  (MkQuadLawFunctor s1 x1) == (MkQuadLawFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractQuadLawFunctor : Type -> Type where
  MkAbstractQuadLawFunctor : QuadLawState -> a -> AbstractQuadLawFunctor a

public export
Functor AbstractQuadLawFunctor where
  map f (MkAbstractQuadLawFunctor s x) = MkAbstractQuadLawFunctor s (f x)

public export
(Eq a) => Eq (AbstractQuadLawFunctor a) where
  (MkAbstractQuadLawFunctor s1 x1) == (MkAbstractQuadLawFunctor s2 x2) = s1 == s2 && x1 == x2

public export
quadLawHomTensorIso : MultisetTensor (QuadLawFunctor a) b -> MultisetTensor a (AbstractQuadLawFunctor b)
quadLawHomTensorIso ZeroM = ZeroM
quadLawHomTensorIso (AddM (MkQuadLawFunctor s val, b) w rest) =
  AddM (val, MkAbstractQuadLawFunctor s b) w (quadLawHomTensorIso rest)

public export
quadLawHomTensorInv : MultisetTensor a (AbstractQuadLawFunctor b) -> MultisetTensor (QuadLawFunctor a) b
quadLawHomTensorInv ZeroM = ZeroM
quadLawHomTensorInv (AddM (val, MkAbstractQuadLawFunctor s b) w rest) =
  AddM (MkQuadLawFunctor s val, b) w (quadLawHomTensorInv rest)

public export
0 proofQuadLawHomIso : (t : MultisetTensor (QuadLawFunctor a) b) ->
                        quadLawHomTensorInv (quadLawHomTensorIso t) = t
proofQuadLawHomIso ZeroM = Refl
proofQuadLawHomIso (AddM (MkQuadLawFunctor s val, b) w rest) =
  let rec = proofQuadLawHomIso rest
  in cong (AddM (MkQuadLawFunctor s val, b) w) rec

public export
0 proofQuadLawHomInv : (u : MultisetTensor a (AbstractQuadLawFunctor b)) ->
                        quadLawHomTensorIso (quadLawHomTensorInv u) = u
proofQuadLawHomInv ZeroM = Refl
proofQuadLawHomInv (AddM (val, MkAbstractQuadLawFunctor s b) w rest) =
  let rec = proofQuadLawHomInv rest
  in cong (AddM (val, MkAbstractQuadLawFunctor s b) w) rec

public export
MultisetAdjunction QuadLawFunctor AbstractQuadLawFunctor where
  leftAdjoint x = MkQuadLawFunctor (MkQuadLawState 1) x
  rightAdjoint (MkQuadLawFunctor _ x) = x
  homTensorIso = quadLawHomTensorIso
  homTensorInv = quadLawHomTensorInv
  verifyHomIso = proofQuadLawHomIso
  verifyHomInv = proofQuadLawHomInv

--------------------------------------------------------------------------------
-- 5. CONSTRUCTIVIST PARABOLIC DARK MATTER DRAIN & DISSIPATION SINK
--------------------------------------------------------------------------------

||| Drains Landauer information erasure tokens (Q_diss = kT ln 2 * ΔS_erased) or
||| non-equilibrium thermodynamic entropy directly into the Parabolic dissipation channel.
||| Since the Parabolic sector carries null momentum p_null = (0, 0) and det g = 0,
||| dissipation entropy is safely drained without corrupting coherent baryonic bound states (27 VM)
||| or gauge flux (128 DE).
public export
drainParabolicDissipation : (erasureTokens : BoxInt) ->
                           QuadStreamMultiset BoxInt ->
                           QuadStreamMultiset BoxInt
drainParabolicDissipation tokens (MkQuadStream e h p s) =
  MkQuadStream e h (AddM (intToBoxInt 0) tokens p) s

||| Zero-allocation deforested streaming transducer draining parabolic dissipation with %spec fuel:
%spec fuel
public export
streamParabolicDissipationDrain : (fuel : Nat) -> (erasureTokens : BoxInt) ->
                                 FusedStream (QuadStreamChannel, BoxInt, BoxInt) ->
                                 FusedStream (QuadStreamChannel, BoxInt, BoxInt)
streamParabolicDissipationDrain fuel tokens strm =
  appendStream strm (stream [(ParabolicSector, intToBoxInt 0, tokens)])

--------------------------------------------------------------------------------
-- 6. 2LTT STAGED QUAD-STREAM LAW SPECIALIZATION & %spec PIPELINE
--------------------------------------------------------------------------------

||| 2LTT Staged QuadStream Law Operator at Level 0:
public export
StagedQuadLaw : Type
StagedQuadLaw = Lift (QuadStreamMultiset BoxInt -> QuadStreamMultiset BoxInt)

||| Pre-composes two QuadStream laws at compile time (Level 0):
public export
stageComposeQuadLaws : StagedQuadLaw -> StagedQuadLaw -> Code (QuadStreamMultiset BoxInt -> QuadStreamMultiset BoxInt)
stageComposeQuadLaws qL2 qL1 =
  quote (composeQuadLaws (splice qL1) (splice qL2))

||| Proof witness certifying 2LTT staged QuadStream law composition equivalence:
public export
0 prfStageComposeQuadLaws : (l1, l2 : QuadStreamMultiset BoxInt -> QuadStreamMultiset BoxInt) ->
                            splice (stageComposeQuadLaws (quote l2) (quote l1)) = composeQuadLaws l1 l2
prfStageComposeQuadLaws _ _ = Refl

||| Zero-allocation deforested law sector dispatcher with %spec channel, fuel:
%spec channel, fuel
public export
fusedQuadStreamLawTransducerDirect :
  (channel : QuadStreamChannel) ->
  (fuel : Nat) ->
  (BoxInt -> BoxInt) ->
  FusedStream (QuadStreamChannel, BoxInt, BoxInt) ->
  FusedStream (QuadStreamChannel, BoxInt, BoxInt)
fusedQuadStreamLawTransducerDirect ch fuel op strm =
  mapStream (\(c, v, w) => if c == ch then (c, op v, w) else (c, v, w)) strm

