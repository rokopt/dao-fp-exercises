module Naturality

import public TypesAndFunctions
import public Category

%default total

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