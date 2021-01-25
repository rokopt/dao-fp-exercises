module Category

import TypesAndFunctions

%default total

{- Often needed to do category theory in Idris. -}
public export
functionalExtensionality : {a, b : Type} -> FunctionalExtensionality a b
functionalExtensionality = believe_me

public export
record Category where
  constructor MkCategory
  Object : Type
  Morphism : Object -> Object -> Type
  Identity : (a : Object) -> Morphism a a
  After : {a, b, c : Object} -> Morphism b c -> Morphism a b -> Morphism a c
  LeftIdentity : {a, b : Object} -> (m : Morphism a b) ->
    After (Identity b) m = m
  RightIdentity : {a, b : Object} -> (m : Morphism a b) ->
    After m (Identity a) = m
  Associativity : {a, b, c, d : Object} ->
    (h : Morphism c d) -> (g : Morphism b c) -> (f : Morphism a b) ->
    After (After h g) f = After h {a} {b=c} {c=d} (After {a} {b} {c} g f)

public export
catId : {cat : Category} -> (a : Object cat) -> Morphism cat a a
catId {cat} a = Identity cat a

infix 25 .*
public export
(.*) : {cat : Category} -> {a, b, c : Object cat} ->
  Morphism cat b c -> Morphism cat a b -> Morphism cat a c
g .* f = After cat g f

public export
postCompose : {cat : Category} -> {a, b, c : Object cat} ->
  Morphism cat b c -> Morphism cat a b -> Morphism cat a c
postCompose f = (.*) f

public export
preCompose : {cat : Category} -> {a, b, c : Object cat} ->
  Morphism cat a b -> Morphism cat b c -> Morphism cat a c
preCompose f = \h => h .* f