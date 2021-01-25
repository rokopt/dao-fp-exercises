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
Naturality : {cat : Category} -> {a, b, x, y : Object cat} ->
  (f : Morphism cat a b) -> (g : Morphism cat y x) ->
  (preCompose {cat} {a=y} {b=x} {c=b} g) .
    (postCompose {cat} {a=x} {b=a} {c=b} f) =
  (postCompose {cat} {a=y} {b=a} {c=b} f) .
    (preCompose {cat} {a=y} {b=x} {c=a} g)
Naturality f g =
  functionalExtensionality (\h : Morphism cat x a => Associativity cat f h g)

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

public export
SubjectChange : {cat : Category} -> (subjectA, subjectB : Object cat) -> Type
SubjectChange {cat} subjectA subjectB =
  (observer : Object cat) ->
  Morphism cat observer subjectA -> Morphism cat observer subjectB

public export
ObserverChange : {cat : Category} -> (observerA, observerB : Object cat) -> Type
ObserverChange {cat} observerA observerB =
  (subject : Object cat) ->
  Morphism cat observerA subject -> Morphism cat observerB subject

public export
IsBijectionForEach : {a : Type} -> {b, c : a -> Type} ->
  ((x : a) -> b x -> c x) -> Type
IsBijectionForEach alpha = (x : a) -> IsBijection (alpha x)

public export
InvertibleSubjectChange : {cat : Category} ->
  (subjectA, subjectB : Object cat) -> Type
InvertibleSubjectChange subjectA subjectB =
  DPair (SubjectChange subjectA subjectB) IsBijectionForEach

public export
InvertibleObserverChange : {cat : Category} ->
  (observerA, observerB : Object cat) -> Type
InvertibleObserverChange observerA observerB =
  DPair (ObserverChange observerA observerB) IsBijectionForEach

public export
SubjectChangeIsNatural : {cat : Category} ->
  {subjectA, subjectB : Object cat} ->
  SubjectChange {cat} subjectA subjectB -> Type
SubjectChangeIsNatural {cat} alpha =
  (x, y : Object cat) -> (g : Morphism cat y x) ->
    alpha y . preCompose g = preCompose g . alpha x

public export
ObserverChangeIsNatural : {cat : Category} ->
  {observerA, observerB : Object cat} ->
  ObserverChange {cat} observerA observerB -> Type
ObserverChangeIsNatural {cat} beta =
  (x, y : Object cat) -> (g : Morphism cat x y) ->
    postCompose g . beta x = beta y . postCompose g

public export
SubjectChangeInducedMorphism : {cat : Category} ->
  {subjectA, subjectB : Object cat} ->
  (alpha : SubjectChange {cat} subjectA subjectB) ->
  Morphism cat subjectA subjectB
SubjectChangeInducedMorphism {subjectA} {subjectB} alpha =
  alpha subjectA (catId subjectA)

public export
SubjectChangeIsPostComposition : {cat : Category} ->
  {subjectA, subjectB : Object cat} ->
  (alpha : SubjectChange {cat} subjectA subjectB) ->
  (natural : SubjectChangeIsNatural {cat} {subjectA} {subjectB} alpha) ->
  (x : Object cat) -> alpha x =
    postCompose {cat} {a=x} {b=subjectA} {c=subjectB}
      (SubjectChangeInducedMorphism {cat} {subjectA} {subjectB} alpha)
SubjectChangeIsPostComposition {subjectA} {subjectB} alpha natural x =
  functionalExtensionality (\g =>
    replace
      {p=(\g' =>
        alpha x g' = After cat (alpha subjectA (Identity cat subjectA)) g)}
    (LeftIdentity cat g)
    (appEq {x=(catId subjectA)} (natural _ _ g)))

public export
ObserverChangeInducedMorphism : {cat : Category} ->
  {observerA, observerB : Object cat} ->
  (beta : ObserverChange {cat} observerA observerB) ->
  Morphism cat observerB observerA
ObserverChangeInducedMorphism {observerA} {observerB} beta =
  beta observerA (catId observerA)

public export
ObserverChangeIsPreComposition : {cat : Category} ->
  {observerA, observerB : Object cat} ->
  (beta : ObserverChange {cat} observerA observerB) ->
  (natural : ObserverChangeIsNatural {cat} {observerA} {observerB} beta) ->
  (y : Object cat) -> beta y =
    preCompose {cat} {a=observerB} {b=observerA} {c=y}
      (ObserverChangeInducedMorphism {cat} {observerA} {observerB} beta)
ObserverChangeIsPreComposition {observerA} {observerB} beta natural y =
  functionalExtensionality (\f =>
    replace
      {p=(\f' =>
        beta y f' = After cat f (beta observerA (Identity cat observerA)))}
    (RightIdentity cat f)
    (sym (appEq {x=(catId observerA)} (natural _ _ f))))