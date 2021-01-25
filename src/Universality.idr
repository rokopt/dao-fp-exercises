module Universality

import public Category

%default total

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