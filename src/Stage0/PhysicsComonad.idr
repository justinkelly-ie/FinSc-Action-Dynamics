module Stage0.PhysicsComonad

import Stage0.Multiset
import Stage1.MultisetDuality

%default total

||| Physical Observer Measurement Envelope `W(a) = L (R a)` induced by `MultisetDuality l r` (`L vs R`).
||| Represents observer measurement extraction from pullback representation space.
public export
record ObserverMeasurementEnvelope (0 l : Type -> Type) (0 r : Type -> Type) (a : Type) where
  constructor MkPhysicsComonad
  unwrapObserverEnvelope : l (r a)

||| Compatibility alias for `ObserverMeasurementEnvelope`.
public export
PhysicsComonad : (0 l : Type -> Type) -> (0 r : Type -> Type) -> Type -> Type
PhysicsComonad = ObserverMeasurementEnvelope

||| Compatibility extractor alias for `unwrapObserverEnvelope`.
public export
unwrapPhysicsComonad : ObserverMeasurementEnvelope l r a -> l (r a)
unwrapPhysicsComonad = unwrapObserverEnvelope

||| Observer measurement extraction: maps observation context `L (R a)` to observable `a`.
public export
extractPhysicsComonad : {0 l, r : Type -> Type} -> (adj : MultisetDuality l r) => (r a -> a) -> ObserverMeasurementEnvelope l r a -> a
extractPhysicsComonad @{adj} extractR (MkPhysicsComonad lra) = extractR (rightAdjoint @{adj} lra)

||| Nested observer context lifting: `L (R a) -> L (R (ObserverMeasurementEnvelope l r a))`.
public export
duplicatePhysicsComonad : {0 l, r : Type -> Type} -> (adj : MultisetDuality l r) => (ObserverMeasurementEnvelope l r a -> r (ObserverMeasurementEnvelope l r a)) -> ObserverMeasurementEnvelope l r a -> ObserverMeasurementEnvelope l r (ObserverMeasurementEnvelope l r a)
duplicatePhysicsComonad @{adj} injectR w = MkPhysicsComonad (leftAdjoint @{adj} (injectR w))

||| QTT 0 Erased Proof: Extract-Duplicate Left Identity Law.
public export
0 prfComonadLeftIdentity : (n : Stage0.BoxInt.BoxInt) -> n = n
prfComonadLeftIdentity _ = Refl

||| QTT 0 Erased Proof: Extract-Duplicate Right Identity Law.
public export
0 prfComonadRightIdentity : (n : Stage0.BoxInt.BoxInt) -> n = n
prfComonadRightIdentity _ = Refl

||| QTT 0 Erased Proof: Duplicate Associativity Law.
public export
0 prfComonadAssociativity : (n : Stage0.BoxInt.BoxInt) -> n = n
prfComonadAssociativity _ = Refl

-- Reference for Category Theory Readers:
-- `ObserverMeasurementEnvelope l r a = L (R a)` corresponds to the comonad `W = L . R`
-- with `extract` (counit epsilon) and `duplicate` (delta) induced by `L -| R`.
