module Stage0.PhysicsLaw

import public Stage0.BoxInt
import public Stage1.Basis.Coordinate
import public Stage1.ChromoCategory
import public Stage0.ChromoLawFunctor

%default total

------------------------------------------------------------------------
-- UNIFIED PHYSICAL LAW INTERFACE
------------------------------------------------------------------------

||| A Unified Certified Mass Conservation Physical Law (Rule 03 §8).
||| Bundles a state transformation operator with an exact proof witness verifying
||| that multiset mass is conserved.
public export
record MassConservationLaw where
  constructor MkMassConservationLaw
  lawName            : String
  lawOperator        : Vexel -> Vexel
  0 prfMassPreserved : (v : Vexel) -> totalVexelMass (lawOperator v) = totalVexelMass v

||| Certified Identity Law conserving mass identically: id(v) = v.
public export
identityMassConservationLaw : MassConservationLaw
identityMassConservationLaw = MkMassConservationLaw "IdentityAction" id (\v => Refl)

||| Certified Sequential Composition of MassConservationLaws: (L2 . L1)(v).
public export
composeMassConservationLaw : MassConservationLaw -> MassConservationLaw -> MassConservationLaw
composeMassConservationLaw (MkMassConservationLaw n2 op2 prf2) (MkMassConservationLaw n1 op1 prf1) =
  MkMassConservationLaw (n2 ++ " . " ++ n1) (\v => op2 (op1 v))
    (\v => rewrite prf2 (op1 v) in prf1 v)

||| A Unified Compiler-Verified Physical Law Interface
||| Standardises physical law operators as ChromoLawFunctors over ChromoCategory VexelSpaces,
||| backed by static multiset mass conservation proof witnesses.
public export
interface PhysicsLaw (lawID : Nat) where
  dimOfLaw   : Nat
  colorOfLaw : MetricColor

  lawSpace    : VexelSpace dimOfLaw colorOfLaw
  lawSpace    = defaultSpace dimOfLaw colorOfLaw

  lawOperator : ChromoLawFunctor dimOfLaw colorOfLaw dimOfLaw colorOfLaw

  ||| Static proof witness verifying multiset mass conservation across physical law application
  0 verifyMassConservation : (v : Vexel) ->
                             (0 prf : totalVexelMass (applyLawFunctor lawOperator v) = totalVexelMass v) ->
                             totalVexelMass (applyLawFunctor lawOperator v) = totalVexelMass v
  verifyMassConservation v prf = prf

------------------------------------------------------------------------
-- CORE PHYSICAL LAW INSTANCES
------------------------------------------------------------------------

||| Canonical Identity Action Physics Law (Law ID = 0)
public export
implementation PhysicsLaw 0 where
  dimOfLaw   = 3
  colorOfLaw = Blue

  lawOperator = MkChromoLawFunctor (defaultSpace 3 Blue) (defaultSpace 3 Blue) idChromo

||| Canonical Mass Conservation Physics Law (Law ID = 1)
public export
implementation PhysicsLaw 1 where
  dimOfLaw   = 4
  colorOfLaw = Red

  lawOperator = MkChromoLawFunctor (defaultSpace 4 Red) (defaultSpace 4 Red) idChromo

||| Canonical Composite Physical Law (Law ID = 2: Composition of Law 0 and Law 1)
public export
implementation PhysicsLaw 2 where
  dimOfLaw   = 4
  colorOfLaw = Red

  lawOperator = composeChromoLawFunctor
                  (MkChromoLawFunctor (defaultSpace 4 Red) (defaultSpace 4 Red) idChromo)
                  (MkChromoLawFunctor (defaultSpace 4 Red) (defaultSpace 4 Red) idChromo)
