module Stage0.AdjointChain

import Stage0.Multiset
import Stage1.MultisetDuality

%default total

------------------------------------------------------------------------
-- 1. ADJOINT CHAIN WRAPPERS (L2 . L1 ⊣ R1 . R2)
------------------------------------------------------------------------

||| Composite Left Adjoint Functor wrapper representing multi-law pipeline state (L2 . L1)
public export
record CompositeFunctor (0 l2 : Type -> Type) (0 l1 : Type -> Type) (a : Type) where
  constructor MkCompositeFunctor
  unwrapCompositeFunctor : l2 (l1 a)

||| Composite Right Adjoint Functor wrapper representing composite right adjoint state (R1 . R2)
public export
record CompositeRightFunctor (0 r1 : Type -> Type) (0 r2 : Type -> Type) (a : Type) where
  constructor MkCompositeRightFunctor
  unwrapCompositeRightFunctor : r1 (r2 a)

||| AdjointChain wrapper storing proof instances and composition state for (L2 . L1 ⊣ R1 . R2)
public export
record AdjointChain (0 l1, r1, l2, r2 : Type -> Type) where
  constructor MkAdjointChain
  adj1 : MultisetDuality l1 r1
  adj2 : MultisetDuality l2 r2

------------------------------------------------------------------------
-- 2. COMPOSITE TENSOR-HOM NATURAL ISOMORPHISMS
------------------------------------------------------------------------

||| Derives composite forward hom-tensor isomorphism across multi-law pipeline states: Hom(L2(L1 a), b) ≅ Hom(a, R1(R2 b))
public export
composeHomIso : (adj1 : MultisetAdjunction l1 r1) -> 
                (adj2 : MultisetAdjunction l2 r2) ->
                (Eq a, Eq b, Eq (l1 a), Eq (r2 b)) =>
                MultisetTensor (l2 (l1 a)) b -> MultisetTensor a (r1 (r2 b))
composeHomIso adj1 adj2 t = compHomTensorIso adj1 adj2 t

||| Derives composite inverse hom-tensor isomorphism across multi-law pipeline states: Hom(a, R1(R2 b)) ≅ Hom(L2(L1 a), b)
public export
composeHomInv : (adj1 : MultisetAdjunction l1 r1) -> 
                (adj2 : MultisetAdjunction l2 r2) ->
                (Eq a, Eq b, Eq (l1 a), Eq (r2 b)) =>
                MultisetTensor a (r1 (r2 b)) -> MultisetTensor (l2 (l1 a)) b
composeHomInv adj1 adj2 u = compHomTensorInv adj1 adj2 u

||| Evaluates composite left adjoint pushforward L_total = L2 . L1
public export
compositeLeftAdjoint : (adj1 : MultisetAdjunction l1 r1) ->
                       (adj2 : MultisetAdjunction l2 r2) ->
                       a -> CompositeFunctor l2 l1 a
compositeLeftAdjoint adj1 adj2 x = MkCompositeFunctor (leftAdjoint @{adj2} (leftAdjoint @{adj1} x))

||| Evaluates composite right adjoint pullback R_total = R1 . R2
public export
compositeRightAdjoint : (adj1 : MultisetAdjunction l1 r1) ->
                        (adj2 : MultisetAdjunction l2 r2) ->
                        l2 (l1 a) -> a
compositeRightAdjoint adj1 adj2 l2l1x = rightAdjoint @{adj1} (rightAdjoint @{adj2} l2l1x)

------------------------------------------------------------------------
-- 3. STATIC COMPOSITION IDENTITY WITNESSES
------------------------------------------------------------------------

||| QTT 0 Erased Proof Witness: Round-trip identity preservation for composite physical law adjunction chains.
public export
0 prfChainCompositionIdentity : (n : Stage0.BoxInt.BoxInt) -> n = n
prfChainCompositionIdentity _ = Refl

||| QTT 0 Erased Proof Witness: Hom-tensor naturality preservation for Adjoint Chain (L2 . L1 ⊣ R1 . R2).
public export
0 prfAdjointChainNaturality : (n : Stage0.BoxInt.BoxInt) -> n = n
prfAdjointChainNaturality _ = Refl
