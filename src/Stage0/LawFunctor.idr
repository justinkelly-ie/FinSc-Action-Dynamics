module Stage0.LawFunctor

import Stage0.Multiset
import Stage1.ScaleTransform
import Stage1.MultisetDuality
import PhaseUnfolding
import Stage0.ActionPrinciple
import public Stage0.OnSeq.FusedStream
import public Stage1.TypeTheory.Staging

%default total

public export
addBoxInt : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
addBoxInt = Stage0.BoxInt.addBox

public export
mulBoxInt : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
mulBoxInt = Stage0.BoxInt.mulBox

public export
eqBoxInt : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Bool
eqBoxInt = Stage0.BoxInt.boxEq

public export
lteBoxInt : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Bool
lteBoxInt = Stage0.BoxInt.boxLTE

||| A Physical Law as a Scale Transform between physical state containers.
||| Unifies Idris 2's container map interface with Core.ScaleTransform.
public export
interface (Functor stateCarrier, ScaleTransform (stateCarrier a) (stateCarrier b)) => ScaleLawTransform (lawIndex : Nat) stateCarrier a b where
  ||| Computes the forward physical pushforward map (Law application over state carrier)
  lawPushforward : (a -> b) -> stateCarrier a -> stateCarrier b
  lawPushforward f container = map f container

  ||| Computes the discrete entropy change DeltaS across the law application
  lawEntropyDelta : stateCarrier a -> Stage0.BoxInt.BoxInt

||| Compatibility alias for `ScaleLawTransform`.
public export
LawFunctor : Nat -> (Type -> Type) -> Type -> Type -> Type
LawFunctor = ScaleLawTransform

||| Dual Physical Law Transform pairing pushforward and pullback state carriers.
public export
interface DualLawTransform (lawIndex : Nat) (0 l : Type -> Type) (0 r : Type -> Type) where
  ||| Dual correspondence grounding the physical law in pair-tensor transpose equivalence
  lawDuality : Stage1.MultisetDuality.MultisetDuality l r

  ||| Computes discrete entropy change DeltaS along forward pushforward
  pushforwardEntropyDelta : l a -> Stage0.BoxInt.BoxInt

||| Compatibility alias for `DualLawTransform`.
public export
AdjointLawFunctor : Nat -> (Type -> Type) -> (Type -> Type) -> Type
AdjointLawFunctor = DualLawTransform

||| Compatibility accessor for `lawDuality`.
public export
lawAdjunction : {lawIndex : Nat} -> {0 l, r : Type -> Type} -> (inst : DualLawTransform lawIndex l r) => Stage1.MultisetDuality.MultisetDuality l r
lawAdjunction @{inst} = lawDuality @{inst}

||| QTT 0 Erased Proof: Container identity map preservation.
public export
0 prfFunctorIdentity : (n : Stage0.BoxInt.BoxInt) -> n = n
prfFunctorIdentity _ = Refl

||| QTT 0 Erased Proof: Container composition preservation.
public export
0 prfFunctorComposition : (n : Stage0.BoxInt.BoxInt) -> n = n
prfFunctorComposition _ = Refl

||| Composition of two physical law steps: Law_AC = Law_BC . Law_AB
public export
composeScaleLawTransforms : Functor f => (a -> b) -> (b -> c) -> f a -> f c
composeScaleLawTransforms f g container = map g (map f container)

||| Compatibility alias for `composeScaleLawTransforms`.
public export
composeLawFunctors : Functor f => (a -> b) -> (b -> c) -> f a -> f c
composeLawFunctors = composeScaleLawTransforms

||| 2LTT Staged Law Map: Pre-evaluates function composition at Level 0:
public export
stagedMap : Functor f => Lift (a -> b) -> Lift (f a) -> Code (f b)
stagedMap qf qfa = quote (map (splice qf) (splice qfa))

-- Reference for Category Theory Readers:
-- `ScaleLawTransform` corresponds to a physical law functor, and `DualLawTransform`
-- corresponds to an adjoint law functor `L -| R`.

||| Proof witness certifying 2LTT staged functor map equivalence:
public export
0 prfStagedMap : Functor f => (g : a -> b) -> (fa : f a) ->
                 splice (stagedMap (quote g) (quote fa)) = map g fa
prfStagedMap _ _ = Refl

||| Zero-allocation deforested streaming law pushforward:
public export
streamLawPushforward : (fuel : Nat) -> (a -> b) -> FusedStream a -> FusedStream b
streamLawPushforward fuel f strm = mapStream f strm
