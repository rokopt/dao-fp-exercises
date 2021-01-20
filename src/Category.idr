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

public export
IsInverse : {cat : Category} -> {a, b: Object cat} ->
    Morphism cat a b -> Morphism cat b a -> Type
IsInverse f g = (g .* f = catId a, f .* g = catId b)

public export
IsIsomorphism : {cat : Category} -> {a, b: Object cat} ->
  Morphism cat a b -> Type
IsIsomorphism f = DPair (Morphism cat b a) (Category.IsInverse f)

public export
Isomorphic : {cat : Category} -> (a, b: Object cat) -> Type
Isomorphic a b = DPair (Morphism cat a b) IsIsomorphism

public export
IsUnique : {cat : Category} -> {a, b : Object cat} ->
  (property : Morphism cat a b -> Type) -> (f : Morphism cat a b) -> Type
IsUnique {cat} {a} {b} property f =
    (property f, (g : Morphism cat a b) -> property g -> g = f)

public export
IsOnlyMorphism : {cat : Category} -> {a, b : Object cat} ->
    Morphism cat a b -> Type
IsOnlyMorphism f = IsUnique (\_ => ()) f

public export
OnlyMorphismIsUnique : {cat : Category} -> {a, b : Object cat} ->
    {f : Morphism cat a b} -> IsOnlyMorphism {cat} {a} {b} f ->
    (g, h : Morphism cat a b) -> g = h
OnlyMorphismIsUnique (_, onlyAB) g h = rewrite (onlyAB h ()) in (onlyAB g ())

public export
IsTerminal : {cat : Category} -> (a : Object cat) -> Type
IsTerminal {cat} a = (b : Object cat) -> DPair (Morphism cat b a) IsOnlyMorphism

public export
IdOnlyTerminalEndomorphism : {cat : Category} -> {a : Object cat} ->
  (aIsTerminal : IsTerminal {cat} a) -> (f : Morphism cat a a) ->
  f = Identity cat a
IdOnlyTerminalEndomorphism {cat} {a} aIsTerminal f =
  OnlyMorphismIsUnique (snd (aIsTerminal a)) f (Identity cat a)