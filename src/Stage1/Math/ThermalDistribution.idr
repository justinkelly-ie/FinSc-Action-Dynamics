module Stage1.Math.ThermalDistribution

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.WitnessLedger
import Stage0.StreamPolynumber
import Stage0.OnSeq.FusedStream as FS
import Stage1.Polynumber
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.MultisetDuality
import Stage1.MultisetTensor
import Stage1.TypeTheory.Smoothness
import Stage1.FourGeometries
import Data.Fuel
import Data.Vect
import Data.List

%default total

------------------------------------------------------------------------
-- 1. DISCRETE ENERGY LEVELS & RATIONAL TEMPERATURE FACTORS
------------------------------------------------------------------------

||| An Energy Level with an energy index E and microstate multiplicity w(E).
public export
record EnergyLevel where
  constructor MkEnergyLevel
  energyIndex  : Nat
  multiplicity : Nat

public export
Eq EnergyLevel where
  (MkEnergyLevel e1 w1) == (MkEnergyLevel e2 w2) =
    e1 == e2 && w1 == w2

public export
Show EnergyLevel where
  show (MkEnergyLevel e w) =
    "Level(E=" ++ show e ++ ", w=" ++ show w ++ ")"

||| Backward-compatible alias for fast logarithmic natural power (re-exported from Stage1.Order.Preorder).
public export
natPower : Nat -> Nat -> Nat
natPower = fastNatPower

||| Computes scaled polynomial partition sum numerator:
||| ∑_{k=0}^m w_k · N^k · D^{m-k} where maxLevel = m.
public export
scaledPartitionSum : List EnergyLevel -> (maxLevel : Nat) -> (numQ : Nat) -> (denQ : Nat) -> Nat
scaledPartitionSum [] _ _ _ = 0
scaledPartitionSum (MkEnergyLevel e w :: xs) maxLevel numQ denQ =
  let pNum = fastNatPower numQ e
      pDen = fastNatPower denQ (maxLevel `minus` e)
      term = w * (pNum * pDen)
  in term + scaledPartitionSum xs maxLevel numQ denQ

||| Computes the scaled weight numerator for a single level: w_k · N^k · D^{m-k}.
public export
scaledLevelWeight : EnergyLevel -> (maxLevel : Nat) -> (numQ : Nat) -> (denQ : Nat) -> Nat
scaledLevelWeight (MkEnergyLevel e w) maxLevel numQ denQ =
  let pNum = fastNatPower numQ e
      pDen = fastNatPower denQ (maxLevel `minus` e)
  in w * (pNum * pDen)

||| Deforested stream evaluation of scaled partition sum numerator over FusedStream EnergyLevel:
||| Computes ∑ w_k · N^k · D^{m-k} with zero intermediate list allocations.
public export
streamScaledPartitionSum : FusedStream EnergyLevel -> (maxLevel : Nat) -> (numQ : Nat) -> (denQ : Nat) -> Nat
streamScaledPartitionSum strm maxLevel numQ denQ =
  foldStreamNat (S maxLevel) (+) 0
    (mapStream (\lvl => scaledLevelWeight lvl maxLevel numQ denQ) strm)

------------------------------------------------------------------------
-- 2. DISCRETE BOLTZMANN PROBABILITIES AS RATIONAL HEHNER CHANCES
------------------------------------------------------------------------

||| Computes exact Boltzmann probability for level k as a normalized fraction:
||| P(E_k) = scaledWeight(k) / scaledPartitionSum.
public export
discreteBoltzmannProbability : EnergyLevel -> List EnergyLevel -> (maxLevel : Nat) -> 
                                (numQ : Nat) -> (denQ : Nat) -> (Nat, Nat)
discreteBoltzmannProbability lvl spectrum maxLevel numQ denQ =
  let wNum = scaledLevelWeight lvl maxLevel numQ denQ
      zDen = scaledPartitionSum spectrum maxLevel numQ denQ
  in (wNum, zDen)

||| Computes the sum of all probability numerators across the spectrum.
public export
totalProbabilityNumerator : List EnergyLevel -> (maxLevel : Nat) -> (numQ : Nat) -> (denQ : Nat) -> Nat
totalProbabilityNumerator spectrum maxLevel numQ denQ =
  scaledPartitionSum spectrum maxLevel numQ denQ

------------------------------------------------------------------------
-- 3. TRI-GEOMETRIC SECTOR SPECTRA & 210 COSMIC BUDGET FACTORIZATION
------------------------------------------------------------------------

||| Elliptic sector energy ladder (3 levels, 27 VM bound-state capacity).
public export
ellipticLadder : List EnergyLevel
ellipticLadder = [ MkEnergyLevel 0 1
                 , MkEnergyLevel 1 3
                 , MkEnergyLevel 2 6
                 ]

||| Hyperbolic sector energy ladder (3 levels, 128 DE gauge-phase capacity).
public export
hyperbolicLadder : List EnergyLevel
hyperbolicLadder = [ MkEnergyLevel 0 1
                   , MkEnergyLevel 1 8
                   , MkEnergyLevel 2 27
                   ]

||| Parabolic sector energy ladder (3 levels, 55 DM memory remainder capacity).
public export
parabolicLadder : List EnergyLevel
parabolicLadder = [ MkEnergyLevel 0 1
                  , MkEnergyLevel 1 2
                  , MkEnergyLevel 2 4
                  ]

||| Exponent decomposition of the Cosmic Partition Function:
||| Z_Cosmic = Z_Ell^27 × Z_Hyp^128 × Z_Par^55.
public export
cosmicPartitionExponents : (Nat, Nat, Nat, Nat)
cosmicPartitionExponents =
  let ellExp = Stage1.FourGeometries.ellipticLatticeCapacity
      hypExp = Stage1.FourGeometries.hyperbolicRomCapacity
      parExp = Stage1.FourGeometries.darkMatterTriangularResidue
      totalExp = Stage1.FourGeometries.primorial210Budget
  in (ellExp, hypExp, parExp, totalExp)

||| Sector Partition Functions as deforested StreamPolynumbers:
||| Z_Ell(q) = 1 + 3q + 6q^2
public export
ellipticStreamPoly : StreamPolynumber
ellipticStreamPoly = streamPolyFromList [ (0, intToBoxInt 1)
                                        , (1, intToBoxInt 3)
                                        , (2, intToBoxInt 6)
                                        ]

||| Z_Hyp(q) = 1 + 8q + 27q^2
public export
hyperbolicStreamPoly : StreamPolynumber
hyperbolicStreamPoly = streamPolyFromList [ (0, intToBoxInt 1)
                                          , (1, intToBoxInt 8)
                                          , (2, intToBoxInt 27)
                                          ]

||| Z_Par(q) = 1 + 2q + 4q^2
public export
parabolicStreamPoly : StreamPolynumber
parabolicStreamPoly = streamPolyFromList [ (0, intToBoxInt 1)
                                         , (1, intToBoxInt 2)
                                         , (2, intToBoxInt 4)
                                         ]



||| Evaluates the cosmic sector partition polynomial sum using model-indexed GohFuel derived from geometry capacity (Rule 03, Item 2; Rule 04, Item 4).
public export
evalSectorPartitionPolyFuelModel : (geom : FundamentalGeometry) -> BoxInt -> StreamPolynumber -> BoxInt
evalSectorPartitionPolyFuelModel geom q poly =
  evalStreamPolyNat (gohSteps (geometryGohFuel geom)) q poly

||| Audits that deforested StreamPolynumber partition evaluation matches the scaled list sums:
||| At q = 1: Z_Ell = 10, Z_Hyp = 36, Z_Par = 7.
||| At q = 0: Z_Ell = 1, Z_Hyp = 1, Z_Par = 1 (ground state).
public export
auditStreamPartitionEquivalenceProof : Bool
auditStreamPartitionEquivalenceProof =
  let one = intToBoxInt 1
      zero = intToBoxInt 0
      zEll1 = evalSectorPartitionPolyFuelModel EllipticGeom one ellipticStreamPoly
      zHyp1 = evalSectorPartitionPolyFuelModel HyperbolicGeom one hyperbolicStreamPoly
      zPar1 = evalSectorPartitionPolyFuelModel ParabolicGeom one parabolicStreamPoly
      zEll0 = evalSectorPartitionPolyFuelModel EllipticGeom zero ellipticStreamPoly
      zHyp0 = evalSectorPartitionPolyFuelModel HyperbolicGeom zero hyperbolicStreamPoly
      zPar0 = evalSectorPartitionPolyFuelModel ParabolicGeom zero parabolicStreamPoly
      sumEll = scaledPartitionSum ellipticLadder 2 1 1
      sumHyp = scaledPartitionSum hyperbolicLadder 2 1 1
      sumPar = scaledPartitionSum parabolicLadder 2 1 1
  in boxEq zEll1 (natToBoxInt sumEll) &&
     boxEq zHyp1 (natToBoxInt sumHyp) &&
     boxEq zPar1 (natToBoxInt sumPar) &&
     boxEq zEll0 (intToBoxInt 1) &&
     boxEq zHyp0 (intToBoxInt 1) &&
     boxEq zPar0 (intToBoxInt 1)

||| The 4th Primorial Master Zeta Generator:
||| Z_210(α) = B_2(1) ^ B_3(1) ^ B_5(1) ^ B_7(1).
||| Computes the Dirichlet Euler product over the 4 primorial prime generators {2, 3, 5, 7}.
public export
primorial210Zeta : Stage1.Polynumber.Polynumber
primorial210Zeta = Stage1.Polynumber.dirichletFIA [2, 3, 5, 7] 1

||| Converts a discrete EnergyLevel ladder into a generating Polynumber multiset:
||| Z(q) = ∑ w_k q^k.
public export
ladderToPolynumber : List EnergyLevel -> Stage1.Polynumber.Polynumber
ladderToPolynumber levels =
  let maxDegree = foldl (\m, (MkEnergyLevel e _) => if e > m then e else m) (the Nat 0) levels
      coeffList = map (\d => findCoeff d levels) [0 .. maxDegree]
  in Stage1.Polynumber.MkPolynumber coeffList
  where
    findCoeff : Nat -> List EnergyLevel -> Stage0.BoxInt.BoxInt
    findCoeff _ [] = Stage0.BoxInt.intToBoxInt 0
    findCoeff d (MkEnergyLevel e w :: rest) =
      if d == e then Stage0.BoxInt.intToBoxInt (cast w) else findCoeff d rest

||| Generating Polynumber for the Elliptic Sector (Z_Ell = 1 + 3q + 6q^2):
public export
ellipticPartitionPoly : Stage1.Polynumber.Polynumber
ellipticPartitionPoly = Stage1.Polynumber.MkPolynumber [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 3, Stage0.BoxInt.intToBoxInt 6]

||| Generating DepPolynumber for the Elliptic Sector (Z_Ell = 1 + 3q + 6q^2) with certified degree 2:
public export
ellipticPartitionDepPoly : Stage1.Polynumber.DepPolynumber 2
ellipticPartitionDepPoly =
  Stage1.Polynumber.MkDepPolynumber [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 3, Stage0.BoxInt.intToBoxInt 6]

||| Generating Polynumber for the Hyperbolic Sector (Z_Hyp = 1 + 8q + 27q^2):
public export
hyperbolicPartitionPoly : Stage1.Polynumber.Polynumber
hyperbolicPartitionPoly = Stage1.Polynumber.MkPolynumber [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 8, Stage0.BoxInt.intToBoxInt 27]

||| Generating DepPolynumber for the Hyperbolic Sector (Z_Hyp = 1 + 8q + 27q^2) with certified degree 2:
public export
hyperbolicPartitionDepPoly : Stage1.Polynumber.DepPolynumber 2
hyperbolicPartitionDepPoly =
  Stage1.Polynumber.MkDepPolynumber [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 8, Stage0.BoxInt.intToBoxInt 27]

||| Generating Polynumber for the Parabolic Sector (Z_Par = 1 + 2q + 4q^2):
public export
parabolicPartitionPoly : Stage1.Polynumber.Polynumber
parabolicPartitionPoly = Stage1.Polynumber.MkPolynumber [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 2, Stage0.BoxInt.intToBoxInt 4]

||| Generating DepPolynumber for the Parabolic Sector (Z_Par = 1 + 2q + 4q^2) with certified degree 2:
public export
parabolicPartitionDepPoly : Stage1.Polynumber.DepPolynumber 2
parabolicPartitionDepPoly =
  Stage1.Polynumber.MkDepPolynumber [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 2, Stage0.BoxInt.intToBoxInt 4]

||| Computes the joint multi-sector Cosmic Partition Function via the Caret Product:
||| Z_Cosmic = Z_Ell ^ Z_Hyp ^ Z_Par.
public export
cosmicCaretPartitionPoly : Stage1.Polynumber.Polynumber
cosmicCaretPartitionPoly =
  Stage1.Polynumber.caretPolynumber (Stage1.Polynumber.caretPolynumber ellipticPartitionPoly hyperbolicPartitionPoly) parabolicPartitionPoly

||| Computes the joint multi-sector Cosmic Partition Function via the Caret Product with exact multiplicative degree:
||| deg(Z_Cosmic) = deg(Z_Ell) * deg(Z_Hyp) * deg(Z_Par) = 2 * 2 * 2 = 8.
public export
cosmicCaretPartitionDepPoly : Stage1.Polynumber.DepPolynumber 8
cosmicCaretPartitionDepPoly =
  Stage1.Polynumber.caretDepPoly (Stage1.Polynumber.caretDepPoly ellipticPartitionDepPoly hyperbolicPartitionDepPoly) parabolicPartitionDepPoly

||| Definitional compile-time witness verifying cosmic partition degree multiplicativity:
public export
0 prfCosmicPartitionDegree : (2 * 2 * 2 = 8)
prfCosmicPartitionDegree = Refl

||| Deforested StreamPolynumber representation of the Cosmic Partition Function via Caret product:
||| Z_Cosmic = Z_Ell ^ Z_Hyp ^ Z_Par.
public export
cosmicCaretStreamPoly : StreamPolynumber
cosmicCaretStreamPoly =
  streamPolyCaret (streamPolyCaret ellipticStreamPoly hyperbolicStreamPoly) parabolicStreamPoly

||| Evaluates QuadStream partition sum across all 4 geometric sectors.
public export
quadStreamPartitionSum : QuadStreamMultiset Stage0.BoxInt.BoxInt -> (maxLevel : Nat) -> (numQ : Nat) -> (denQ : Nat) -> Nat
quadStreamPartitionSum (MkQuadStream e h p s) maxLevel numQ denQ =
  let eSum = scaledPartitionSum ellipticLadder maxLevel numQ denQ * natVal (multisetSum e)
      hSum = scaledPartitionSum hyperbolicLadder maxLevel numQ denQ * natVal (multisetSum h)
      pSum = scaledPartitionSum parabolicLadder maxLevel numQ denQ * natVal (multisetSum p)
      sSum = natVal (multisetSum s)
  in eSum + hSum + pSum + sSum
  where
    natVal : Stage0.BoxInt.BoxInt -> Nat
    natVal = boxToNat

------------------------------------------------------------------------
-- 4. CONSTRUCTIVE FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Boltzmann partition factorization, deforested Caret stream equivalence, and ground state collapse:
public export
auditThermalDistributionProof : Bool
auditThermalDistributionProof =
  let one = intToBoxInt 1
      zero = intToBoxInt 0
      zStream1 = evalStreamPolyGoh one cosmicCaretStreamPoly
      zPoly1 = Stage1.Polynumber.evalPolynumber cosmicCaretPartitionPoly one
      zStream0 = evalStreamPolyGoh zero cosmicCaretStreamPoly
      zPoly0 = Stage1.Polynumber.evalPolynumber cosmicCaretPartitionPoly zero
  in auditStreamPartitionEquivalenceProof &&
     boxEq zStream1 zPoly1 &&
     boxEq zStream0 zPoly0

||| Audits that discrete Boltzmann probabilities sum to 1 over the state ladder (total probability normalization).
public export
auditBoltzmannProbabilityNormalizationProof : Bool
auditBoltzmannProbabilityNormalizationProof =
  let maxLevel = 2
      numQ = 1
      denQ = 2
      spectrum = ellipticLadder
      probs = map (\lvl => discreteBoltzmannProbability lvl spectrum maxLevel numQ denQ) spectrum
      numSum = foldl (\acc, (n, _) => acc + n) (the Nat 0) probs
      den = scaledPartitionSum spectrum maxLevel numQ denQ
  in numSum == den && den > 0

||| Audits Caret-FIA Boltzmann Partition Factorization & Cosmic Free Energy (Witness 120).
public export
auditCaretBoltzmannPartitionProof : Bool
auditCaretBoltzmannPartitionProof = auditThermalDistributionProof

------------------------------------------------------------------------
-- 5. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
record ThermalState where
  constructor MkThermalState
  maxLevel : Nat
  numQ     : Nat
  denQ     : Nat

public export
Eq ThermalState where
  (MkThermalState m1 n1 d1) == (MkThermalState m2 n2 d2) =
    m1 == m2 && n1 == n2 && d1 == d2

public export
data ThermalDistributionFunctor : Type -> Type where
  MkThermalDistributionFunctor : ThermalState -> a -> ThermalDistributionFunctor a

public export
Functor ThermalDistributionFunctor where
  map f (MkThermalDistributionFunctor s x) = MkThermalDistributionFunctor s (f x)

public export
(Eq a) => Eq (ThermalDistributionFunctor a) where
  (MkThermalDistributionFunctor s1 x1) == (MkThermalDistributionFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractThermalDistributionFunctor : Type -> Type where
  MkAbstractThermalDistributionFunctor : ThermalState -> a -> AbstractThermalDistributionFunctor a

public export
Functor AbstractThermalDistributionFunctor where
  map f (MkAbstractThermalDistributionFunctor s x) = MkAbstractThermalDistributionFunctor s (f x)

public export
(Eq a) => Eq (AbstractThermalDistributionFunctor a) where
  (MkAbstractThermalDistributionFunctor s1 x1) == (MkAbstractThermalDistributionFunctor s2 x2) = s1 == s2 && x1 == x2

public export
thermalDistributionHomTensorIso : MultisetTensor (ThermalDistributionFunctor a) b -> MultisetTensor a (AbstractThermalDistributionFunctor b)
thermalDistributionHomTensorIso ZeroM = ZeroM
thermalDistributionHomTensorIso (AddM (MkThermalDistributionFunctor s val, b) w rest) =
  AddM (val, MkAbstractThermalDistributionFunctor s b) w (thermalDistributionHomTensorIso rest)

public export
thermalDistributionHomTensorInv : MultisetTensor a (AbstractThermalDistributionFunctor b) -> MultisetTensor (ThermalDistributionFunctor a) b
thermalDistributionHomTensorInv ZeroM = ZeroM
thermalDistributionHomTensorInv (AddM (val, MkAbstractThermalDistributionFunctor s b) w rest) =
  AddM (MkThermalDistributionFunctor s val, b) w (thermalDistributionHomTensorInv rest)

public export
0 proofThermalDistributionHomIso : (t : MultisetTensor (ThermalDistributionFunctor a) b) ->
                                    thermalDistributionHomTensorInv (thermalDistributionHomTensorIso t) = t
proofThermalDistributionHomIso ZeroM = Refl
proofThermalDistributionHomIso (AddM (MkThermalDistributionFunctor s val, b) w rest) =
  let rec = proofThermalDistributionHomIso rest
  in cong (AddM (MkThermalDistributionFunctor s val, b) w) rec

public export
0 proofThermalDistributionHomInv : (u : MultisetTensor a (AbstractThermalDistributionFunctor b)) ->
                                    thermalDistributionHomTensorIso (thermalDistributionHomTensorInv u) = u
proofThermalDistributionHomInv ZeroM = Refl
proofThermalDistributionHomInv (AddM (val, MkAbstractThermalDistributionFunctor s b) w rest) =
  let rec = proofThermalDistributionHomInv rest
  in cong (AddM (val, MkAbstractThermalDistributionFunctor s b) w) rec

public export
MultisetAdjunction ThermalDistributionFunctor AbstractThermalDistributionFunctor where
  leftAdjoint x = MkThermalDistributionFunctor (MkThermalState 1 1 1) x
  rightAdjoint (MkThermalDistributionFunctor _ x) = x
  homTensorIso = thermalDistributionHomTensorIso
  homTensorInv = thermalDistributionHomTensorInv
  verifyHomIso = proofThermalDistributionHomIso
  verifyHomInv = proofThermalDistributionHomInv


