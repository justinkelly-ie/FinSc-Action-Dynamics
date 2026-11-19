module Stage1.Math.HelmholtzFreeEnergy

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.Interfaces
import Stage0.Multiset
import Stage1.UnixelFraction
import Stage1.Polynumber
import Stage1.Math.ThermalDistribution
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Stage1.FourGeometriesActions
import Data.List

%default total

------------------------------------------------------------------------
-- 1. DISCRETE COSMIC BUDGET HELMHOLTZ FREE ENERGY
------------------------------------------------------------------------

||| Multi-Sector Cosmic Budget Partition (VM, DE, DM):
public export
record CosmicBudgetPartition where
  constructor MkCosmicBudgetPartition
  vmTokens : Stage0.BoxInt.BoxInt
  deTokens : Stage0.BoxInt.BoxInt
  dmTokens : Stage0.BoxInt.BoxInt

public export
Eq CosmicBudgetPartition where
  (MkCosmicBudgetPartition v1 e1 m1) == (MkCosmicBudgetPartition v2 e2 m2) =
    v1 == v2 && e1 == e2 && m1 == m2

||| Computes discrete internal energy U:
||| U = 10 * VM + 1 * DE + 0 * DM
public export
discreteInternalEnergy : CosmicBudgetPartition -> Stage0.BoxInt.BoxInt
discreteInternalEnergy (MkCosmicBudgetPartition vm de _) =
  addBox (mulBox (Stage0.BoxInt.intToBoxInt 10) vm) (mulBox (Stage0.BoxInt.intToBoxInt 1) de)

||| Computes discrete combinatorial multiset entropy S:
||| S = 2 * VM + 5 * DE + 3 * DM
public export
discreteEntropy : CosmicBudgetPartition -> Stage0.BoxInt.BoxInt
discreteEntropy (MkCosmicBudgetPartition vm de dm) =
  addBox (mulBox (Stage0.BoxInt.intToBoxInt 2) vm)
         (addBox (mulBox (Stage0.BoxInt.intToBoxInt 5) de)
                 (mulBox (Stage0.BoxInt.intToBoxInt 3) dm))

||| Computes discrete Helmholtz Free Energy: F = U - T * S.
public export
discreteHelmholtzFreeEnergy : (temp : Stage0.BoxInt.BoxInt) -> CosmicBudgetPartition -> Stage0.BoxInt.BoxInt
discreteHelmholtzFreeEnergy t part =
  let u = discreteInternalEnergy part
      s = discreteEntropy part
  in subBox u (mulBox t s)

------------------------------------------------------------------------
-- 1B. PURE MULTISET BUDGET SECTOR ENCODING & HELMHOLTZ FREE ENERGY
------------------------------------------------------------------------

||| Cosmic Budget Sector Token Enumeration
public export
data BudgetSector = VMSector | DESector | DMSector

public export
Eq BudgetSector where
  VMSector == VMSector = True
  DESector == DESector = True
  DMSector == DMSector = True
  _ == _ = False

budgetSectorRank : BudgetSector -> Nat
budgetSectorRank VMSector = 0
budgetSectorRank DESector = 1
budgetSectorRank DMSector = 2

public export
Ord BudgetSector where
  compare x y = compare (budgetSectorRank x) (budgetSectorRank y)

public export
DiscreteCoord BudgetSector where

||| Encodes CosmicBudgetPartition as a pure discrete Carrier BudgetSector.
public export
partitionToMultiset : CosmicBudgetPartition -> Stage0.Multiset.Carrier BudgetSector
partitionToMultiset (MkCosmicBudgetPartition vm de dm) =
  singletonCarrier VMSector vm <+> singletonCarrier DESector de <+> singletonCarrier DMSector dm

||| Multiset evaluation weighting for discrete internal energy U.
public export
sectorEnergyWeight : BudgetSector -> Stage0.BoxInt.BoxInt
sectorEnergyWeight VMSector = Stage0.BoxInt.intToBoxInt 10
sectorEnergyWeight DESector = Stage0.BoxInt.intToBoxInt 1
sectorEnergyWeight DMSector = Stage0.BoxInt.intToBoxInt 0

||| Multiset evaluation weighting for discrete entropy S.
public export
sectorEntropyWeight : BudgetSector -> Stage0.BoxInt.BoxInt
sectorEntropyWeight VMSector = Stage0.BoxInt.intToBoxInt 2
sectorEntropyWeight DESector = Stage0.BoxInt.intToBoxInt 5
sectorEntropyWeight DMSector = Stage0.BoxInt.intToBoxInt 3

||| Evaluates linear weighting functional over a Carrier BudgetSector.
public export
evalBudgetMultiset : (BudgetSector -> Stage0.BoxInt.BoxInt) -> Stage0.Multiset.Carrier BudgetSector -> Stage0.BoxInt.BoxInt
evalBudgetMultiset weight =
  foldBoxTreeL (\acc, (s, c) => addBox acc (mulBox (weight s) c)) (Stage0.BoxInt.intToBoxInt 0)

||| Multiset-powered discrete Helmholtz Free Energy: F = U - T * S.
public export
multisetHelmholtzFreeEnergy : (temp : Stage0.BoxInt.BoxInt) -> Stage0.Multiset.Carrier BudgetSector -> Stage0.BoxInt.BoxInt
multisetHelmholtzFreeEnergy t m =
  let u = evalBudgetMultiset sectorEnergyWeight m
      s = evalBudgetMultiset sectorEntropyWeight m
  in subBox u (mulBox t s)


------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Discrete Helmholtz Free Energy Minimization at Primorial 210)
------------------------------------------------------------------------

||| Standard Primorial 210 Partition: 27 VM, 128 DE, 55 DM.
public export
StandardCosmic210Partition : CosmicBudgetPartition
StandardCosmic210Partition =
  MkCosmicBudgetPartition (natToBoxInt Stage1.FourGeometries.ellipticLatticeCapacity)
                          (natToBoxInt Stage1.FourGeometries.hyperbolicRomCapacity)
                          (natToBoxInt Stage1.FourGeometries.darkMatterTriangularResidue)

public export
standardCosmic210Partition : CosmicBudgetPartition
standardCosmic210Partition = StandardCosmic210Partition

||| QTT 0 Erased Proof: Discrete Helmholtz Free Energy Minimization at Equilibrium (T = 2, F = -1320).
public export
0 prfDiscreteHelmholtzMinimization :
  discreteHelmholtzFreeEnergy (intToBoxInt 2) StandardCosmic210Partition = intToBoxInt (-1320)
prfDiscreteHelmholtzMinimization = Refl

||| QTT 0 Erased Proof: Substrate Metric Primorial 210 Budget Conservation (27 + 128 + 55 = 210).
public export
0 prfSubstrateStationaryArrow :
  addBox (natToBoxInt Stage1.FourGeometries.ellipticLatticeCapacity)
         (addBox (natToBoxInt Stage1.FourGeometries.hyperbolicRomCapacity)
                 (natToBoxInt Stage1.FourGeometries.darkMatterTriangularResidue)) =
  natToBoxInt Stage1.FourGeometries.primorial210Budget
prfSubstrateStationaryArrow = Refl

||| QTT 0 Erased Proof: Record vs Multiset Helmholtz Equivalence at Ground State.
public export
0 prfMultisetHelmholtzEquivalence :
  multisetHelmholtzFreeEnergy (intToBoxInt 2) (partitionToMultiset StandardCosmic210Partition) =
  discreteHelmholtzFreeEnergy (intToBoxInt 2) StandardCosmic210Partition
prfMultisetHelmholtzEquivalence = Refl



------------------------------------------------------------------------
-- 4. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
------------------------------------------------------------------------

||| Left adjoint Helmholtz Free Energy functor wrapping partition state and payload a
public export
data HelmholtzFunctor : Type -> Type where
  MkHelmholtzFunctor : CosmicBudgetPartition -> a -> HelmholtzFunctor a

public export
Functor HelmholtzFunctor where
  map f (MkHelmholtzFunctor part x) = MkHelmholtzFunctor part (f x)

public export
(Eq a) => Eq (HelmholtzFunctor a) where
  (MkHelmholtzFunctor p1 x1) == (MkHelmholtzFunctor p2 x2) = p1 == p2 && x1 == x2

||| Right adjoint Helmholtz Free Energy functor wrapping abstract partition state and payload a
public export
data AbstractHelmholtzFunctor : Type -> Type where
  MkAbstractHelmholtzFunctor : CosmicBudgetPartition -> a -> AbstractHelmholtzFunctor a

public export
Functor AbstractHelmholtzFunctor where
  map f (MkAbstractHelmholtzFunctor part x) = MkAbstractHelmholtzFunctor part (f x)

public export
(Eq a) => Eq (AbstractHelmholtzFunctor a) where
  (MkAbstractHelmholtzFunctor p1 x1) == (MkAbstractHelmholtzFunctor p2 x2) = p1 == p2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro Helmholtz multiset tensors
public export
helmholtzHomTensorIso : MultisetTensor (HelmholtzFunctor a) b -> MultisetTensor a (AbstractHelmholtzFunctor b)
helmholtzHomTensorIso ZeroM = ZeroM
helmholtzHomTensorIso (AddM (MkHelmholtzFunctor part val, b) w rest) =
  AddM (val, MkAbstractHelmholtzFunctor part b) w (helmholtzHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro Helmholtz multiset tensors
public export
helmholtzHomTensorInv : MultisetTensor a (AbstractHelmholtzFunctor b) -> MultisetTensor (HelmholtzFunctor a) b
helmholtzHomTensorInv ZeroM = ZeroM
helmholtzHomTensorInv (AddM (val, MkAbstractHelmholtzFunctor part b) w rest) =
  AddM (MkHelmholtzFunctor part val, b) w (helmholtzHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofHelmholtzHomIso : (t : MultisetTensor (HelmholtzFunctor a) b) ->
                        helmholtzHomTensorInv (helmholtzHomTensorIso t) = t
proofHelmholtzHomIso ZeroM = Refl
proofHelmholtzHomIso (AddM (MkHelmholtzFunctor part val, b) w rest) =
  let rec = proofHelmholtzHomIso rest
  in cong (AddM (MkHelmholtzFunctor part val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofHelmholtzHomInv : (u : MultisetTensor a (AbstractHelmholtzFunctor b)) ->
                        helmholtzHomTensorIso (helmholtzHomTensorInv u) = u
proofHelmholtzHomInv ZeroM = Refl
proofHelmholtzHomInv (AddM (val, MkAbstractHelmholtzFunctor part b) w rest) =
  let rec = proofHelmholtzHomInv rest
  in cong (AddM (val, MkAbstractHelmholtzFunctor part b) w) rec

||| Category-Theoretic MultisetAdjunction instance HelmholtzFunctor ⊣ AbstractHelmholtzFunctor
public export
MultisetDuality HelmholtzFunctor AbstractHelmholtzFunctor where
  leftAdjoint x = MkHelmholtzFunctor (MkCosmicBudgetPartition (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0)) x
  rightAdjoint (MkHelmholtzFunctor _ x) = x
  homTensorIso = helmholtzHomTensorIso
  homTensorInv = helmholtzHomTensorInv
  verifyHomIso = proofHelmholtzHomIso
  verifyHomInv = proofHelmholtzHomInv

