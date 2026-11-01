module Stage1.Math.CosmicGenesis

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.UnixelFraction
import Stage1.LinAlgebra.MetricTensor
import Stage0.Multiset
import Stage1.Math.ConstructiveBaryogenesis
import Stage1.Math.InformationErasureCost
import Stage1.Math.HelmholtzFreeEnergy
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Stage1.FourGeometries
import Stage1.Math.OnSeq.SpreadStream
import Stage1.Carrier.Maxel
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 18: DISCRETE COSMIC GENESIS & PRIMORDIAL RELIC FREEZE-OUT
------------------------------------------------------------------------

||| Primordial Genesis State at Epoch 1:
||| - vmTokens: 0 visible matter tokens in active spatial lattice
||| - deSlots: 128 hyperbolic law storage ROM slots
||| - dmSlots: 55 parabolic dissipation sink residue slots
||| - masterBudget: 210 (Primorial 210 = 2 * 3 * 5 * 7)
public export
record GenesisState where
  constructor MkGenesisState
  vmTokens     : Stage0.BoxInt.BoxInt
  deSlots      : Nat
  dmSlots      : Nat
  masterBudget : Nat

public export
Eq GenesisState where
  (MkGenesisState v1 d1 m1 t1) == (MkGenesisState v2 d2 m2 t2) =
    v1 == v2 && d1 == d2 && m1 == m2 && t1 == t2


public export
genesisVacuum : GenesisState
genesisVacuum = MkGenesisState (Stage0.BoxInt.intToBoxInt 0) Stage1.FourGeometries.hyperbolicRomCapacity Stage1.FourGeometries.darkMatterTriangularResidue Stage1.FourGeometries.primorial210Budget

||| QuadStream Primordial Genesis State initialized to canonical Primorial 210 budget bounds.
public export
genesisQuadStream : QuadStreamMultiset BoxInt
genesisQuadStream =
  let e = AddM (intToBoxInt 0) (natToBoxInt Stage1.FourGeometries.ellipticLatticeCapacity) ZeroM
      h = AddM (intToBoxInt 0) (natToBoxInt Stage1.FourGeometries.hyperbolicRomCapacity) ZeroM
      p = AddM (intToBoxInt 0) (intToBoxInt 0) ZeroM
      s = AddM (intToBoxInt 0) (natToBoxInt Stage1.FourGeometries.darkMatterTriangularResidue) ZeroM
  in MkQuadStream e h p s

||| Audits the Primordial Genesis Budget Partition: 0 + 128 + 55 == 183 <= 210,
||| with full capacity allocated as 27 (VM Basis) + 128 (DE ROM) + 55 (DM Sink) = 210.
public export
isValidGenesisPartition : GenesisState -> Bool
isValidGenesisPartition (MkGenesisState vm de dm tot) =
  Stage0.BoxInt.boxIsZero vm &&
  de == Stage1.FourGeometries.hyperbolicRomCapacity &&
  dm == Stage1.FourGeometries.darkMatterTriangularResidue &&
  (Stage1.FourGeometries.ellipticLatticeCapacity + de + dm == tot) &&
  tot == Stage1.FourGeometries.primorial210Budget

||| Audits QuadStream Primordial Genesis Budget Partition: 27 + 128 + 55 == 210.
public export
isValidQuadStreamGenesisPartition : QuadStreamMultiset BoxInt -> Bool
isValidQuadStreamGenesisPartition qs =
  let part = quadStreamToCosmicPartition qs
  in (vmTokens part + deTokens part + dmTokens part) == natToBoxInt Stage1.FourGeometries.primorial210Budget

------------------------------------------------------------------------
-- 2. ANTIMATTER PAIR ANNIHILATION & RELIC ASYMMETRY FREEZE-OUT
------------------------------------------------------------------------

||| Computes the Primordial Antimatter Annihilation and Relic Baryon Freeze-Out:
||| Given initial symmetric pairs (B_+, B_-) with seed asymmetry B_+ > B_-:
||| 1. All B_- antimatter annihilates against B_- positive tokens.
||| 2. Exactly 2 * B_- photon tokens are released into the cosmic radiation bath (N_gamma).
||| 3. Remaining net baryon tokens B_net = B_+ - B_- freeze out as surviving matter.
public export
freezeOutAntimatterAnnihilation : BaryonState -> BaryonState
freezeOutAntimatterAnnihilation (MkBaryonState p n g) =
  let annihilatedPairs = if p >= n then n else p
      survivingP = p - annihilatedPairs
      survivingN = n - annihilatedPairs
      newPhotons = g + (Stage0.BoxInt.intToBoxInt 2 * annihilatedPairs)
  in MkBaryonState survivingP survivingN newPhotons

------------------------------------------------------------------------
-- 3. UNIDIRECTIONAL LANDAUER DISSIPATION & DARK MATTER LOGGING
--    (Null Momentum Relocation p_null = (0, 0))
------------------------------------------------------------------------

||| Relocates erased computational tokens from active VM into the Parabolic DM Sink:
||| By the Substrate Causal Arrow (g22 = 0), this flow is strictly irreversible.
public export
landauerFreezeOutStep : (erasedBits : Nat) -> (tempScale : Nat) -> (dmLedger : Nat) -> (Nat, Nat)
landauerFreezeOutStep bits tScale dmCount =
  let dissipatedTokens = bits * tScale
      newDM = dmCount + dissipatedTokens
  in (dissipatedTokens, newDM)

------------------------------------------------------------------------
-- 4. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 18: Discrete Cosmic Genesis & Primordial Relic Freeze-Out)
------------------------------------------------------------------------

||| Aggregates a list of multiset token bags using addMultiset fold.
public export
aggregateMultisets : List (Stage0.Multiset.Multiset Stage0.BoxInt.BoxInt String) -> Stage0.Multiset.Multiset Stage0.BoxInt.BoxInt String
aggregateMultisets [] = Stage0.Multiset.ZeroM
aggregateMultisets (x :: xs) = Stage0.Multiset.addMultiset x (aggregateMultisets xs)


||| Audits the Primordial Relic Freeze-Out & Landauer Dissipation Invariant:
public export
auditCosmicGenesisRelicFreezeOutProof : Bool
auditCosmicGenesisRelicFreezeOutProof =
  let (diss, dm) = landauerFreezeOutStep 10 27 55
      initB = MkBaryonState (Stage0.BoxInt.intToBoxInt 10) (Stage0.BoxInt.intToBoxInt 3) (Stage0.BoxInt.intToBoxInt 100)
      finB = freezeOutAntimatterAnnihilation initB
  in diss == 270 && dm == 325 && baryonPos finB == Stage0.BoxInt.intToBoxInt 7

||| Multi-Epoch Cosmic Baryon Evolution: Traces Sakharov asymmetry generation through freeze-out.
public export
evaluateCompositeBaryonEvolution : Bool
evaluateCompositeBaryonEvolution =
  let bViol = satisfiesBaryonViolation (Stage0.BoxInt.intToBoxInt 0) (Stage0.BoxInt.intToBoxInt 7)
      outEq = satisfiesOutOfEquilibrium (Stage0.BoxInt.intToBoxInt 0)
      initState = MkBaryonState (Stage0.BoxInt.intToBoxInt 10) (Stage0.BoxInt.intToBoxInt 3) (Stage0.BoxInt.intToBoxInt 100)
      cpViol = satisfiesCPViolation initState
      frozenState = freezeOutAntimatterAnnihilation initState
      netSurviving = baryonPos frozenState - baryonNeg frozenState
      photonsProduced = photonTokens frozenState
  in bViol && outEq && cpViol && (netSurviving == Stage0.BoxInt.intToBoxInt 7) && (photonsProduced == Stage0.BoxInt.intToBoxInt 106)

------------------------------------------------------------------------
-- 5. CANONICAL 210 x 210 COSMIC MASTER COMPANION MAXEL
------------------------------------------------------------------------

||| Canonical 210 x 210 Master Companion Maxel for the Primorial 210 cosmic ground state.
||| Folds Cigler-Herbig divisor companion blocks across all divisors d | 210
||| with diagonal cumulative coordinate shifting in O(1) heap allocation.
public export
masterPrimorial210CompanionMaxel : Maxel
masterPrimorial210CompanionMaxel = cyclotomicDirectSumMaxelHylo 210

||| Certified Cyclotomic Spread Decomposition for the Master Substrate Primorial 210 state.
public export
certifiedPrimorial210Spread : CertifiedCyclotomicSpread 210
certifiedPrimorial210Spread = certifiedCyclotomicSpread 210

||| QTT 0 Erased Compile-Time Proof: Master Primorial 210 totient capacity conservation.
public export
0 prfMasterPrimorial210DimensionConservation : Stage1.Math.CosmicGenesis.certifiedPrimorial210Spread.totientCapacity = 210
prfMasterPrimorial210DimensionConservation = Refl

||| Audits the Master Primorial 210 Companion Maxel and Certified Spread Capacity:
public export
auditMasterPrimorial210CompanionProof : Bool
auditMasterPrimorial210CompanionProof =
  let spread = certifiedPrimorial210Spread
  in spread.totientCapacity == 210 && spread.degree == 210

--------------------------------------------------------------------------------
-- 6. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
--------------------------------------------------------------------------------

||| Left adjoint Cosmic Genesis functor wrapping micro genesis state and payload a
public export
data CosmicGenesisFunctor : Type -> Type where
  MkCosmicGenesisFunctor : GenesisState -> a -> CosmicGenesisFunctor a

public export
Functor CosmicGenesisFunctor where
  map f (MkCosmicGenesisFunctor state x) = MkCosmicGenesisFunctor state (f x)

public export
(Eq a) => Eq (CosmicGenesisFunctor a) where
  (MkCosmicGenesisFunctor s1 x1) == (MkCosmicGenesisFunctor s2 x2) = s1 == s2 && x1 == x2

||| Right adjoint Cosmic Genesis functor wrapping macro genesis state and payload a
public export
data AbstractCosmicGenesisFunctor : Type -> Type where
  MkAbstractCosmicGenesisFunctor : GenesisState -> a -> AbstractCosmicGenesisFunctor a

public export
Functor AbstractCosmicGenesisFunctor where
  map f (MkAbstractCosmicGenesisFunctor state x) = MkAbstractCosmicGenesisFunctor state (f x)

public export
(Eq a) => Eq (AbstractCosmicGenesisFunctor a) where
  (MkAbstractCosmicGenesisFunctor s1 x1) == (MkAbstractCosmicGenesisFunctor s2 x2) = s1 == s2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro cosmic genesis multiset tensors
public export
cosmicGenesisHomTensorIso : MultisetTensor (CosmicGenesisFunctor a) b -> MultisetTensor a (AbstractCosmicGenesisFunctor b)
cosmicGenesisHomTensorIso ZeroM = ZeroM
cosmicGenesisHomTensorIso (AddM (MkCosmicGenesisFunctor state val, b) w rest) =
  AddM (val, MkAbstractCosmicGenesisFunctor state b) w (cosmicGenesisHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro cosmic genesis multiset tensors
public export
cosmicGenesisHomTensorInv : MultisetTensor a (AbstractCosmicGenesisFunctor b) -> MultisetTensor (CosmicGenesisFunctor a) b
cosmicGenesisHomTensorInv ZeroM = ZeroM
cosmicGenesisHomTensorInv (AddM (val, MkAbstractCosmicGenesisFunctor state b) w rest) =
  AddM (MkCosmicGenesisFunctor state val, b) w (cosmicGenesisHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofCosmicGenesisHomIso : (t : MultisetTensor (CosmicGenesisFunctor a) b) ->
                             cosmicGenesisHomTensorInv (cosmicGenesisHomTensorIso t) = t
proofCosmicGenesisHomIso ZeroM = Refl
proofCosmicGenesisHomIso (AddM (MkCosmicGenesisFunctor state val, b) w rest) =
  let rec = proofCosmicGenesisHomIso rest
  in cong (AddM (MkCosmicGenesisFunctor state val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofCosmicGenesisHomInv : (u : MultisetTensor a (AbstractCosmicGenesisFunctor b)) ->
                             cosmicGenesisHomTensorIso (cosmicGenesisHomTensorInv u) = u
proofCosmicGenesisHomInv ZeroM = Refl
proofCosmicGenesisHomInv (AddM (val, MkAbstractCosmicGenesisFunctor state b) w rest) =
  let rec = proofCosmicGenesisHomInv rest
  in cong (AddM (val, MkAbstractCosmicGenesisFunctor state b) w) rec

||| Category-Theoretic MultisetAdjunction instance CosmicGenesisFunctor ⊣ AbstractCosmicGenesisFunctor
public export
MultisetAdjunction CosmicGenesisFunctor AbstractCosmicGenesisFunctor where
  leftAdjoint x = MkCosmicGenesisFunctor genesisVacuum x
  rightAdjoint (MkCosmicGenesisFunctor _ x) = x
  homTensorIso = cosmicGenesisHomTensorIso
  homTensorInv = cosmicGenesisHomTensorInv
  verifyHomIso = proofCosmicGenesisHomIso
  verifyHomInv = proofCosmicGenesisHomInv

||| QTT 0 Erased Proof: Discrete Cosmic Genesis Adjunction Hom-Tensor Duality Invariant
public export
0 prfCosmicGenesisAdjunctionDuality : (t : MultisetTensor (CosmicGenesisFunctor a) b) ->
                                     cosmicGenesisHomTensorInv (cosmicGenesisHomTensorIso t) = t
prfCosmicGenesisAdjunctionDuality = proofCosmicGenesisHomIso






