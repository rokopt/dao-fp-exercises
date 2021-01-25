module Isomorphism

import public Category

%default total

public export
IsInverse : {cat : Category} -> {a, b: Object cat} ->
    Morphism cat a b -> Morphism cat b a -> Type
IsInverse f g = (g .* f = catId a, f .* g = catId b)

public export
IsIsomorphism : {cat : Category} -> {a, b: Object cat} ->
  Morphism cat a b -> Type
IsIsomorphism f = DPair (Morphism cat b a) (IsInverse f)

public export
Isomorphic : {cat : Category} -> (a, b: Object cat) -> Type
Isomorphic a b = DPair (Morphism cat a b) IsIsomorphism