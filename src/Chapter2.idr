module Chapter2

%default total

public export
FunctionalExtensionality : (a, b : Type) -> Type
FunctionalExtensionality a b =
  {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

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

catId : {cat : Category} -> (a : Object cat) -> Morphism cat a a
catId {cat} a = Identity cat a

infix 25 .*
(.*) : {cat : Category} -> {a, b, c : Object cat} ->
  Morphism cat b c -> Morphism cat a b -> Morphism cat a c
g .* f = After cat g f

postCompose : {cat : Category} -> {a, b, c : Object cat} ->
  Morphism cat b c -> Morphism cat a b -> Morphism cat a c
postCompose f = (.*) f

preCompose : {cat : Category} -> {a, b, c : Object cat} ->
  Morphism cat a b -> Morphism cat b c -> Morphism cat a c
preCompose f = \h => h .* f

Exercise_2_1_1 : {cat : Category} -> {a, b, c, d : Object cat} ->
  (g : Morphism cat c d) -> (f : Morphism cat b c) ->
  postCompose {cat} {a} {b} {c=d} ((.*) {cat} {a=b} {b=c} {c=d} g f) =
    (postCompose {cat} {a} {b=c} {c=d} g) . (postCompose {cat} {a} {b} {c} f)
Exercise_2_1_1 {cat} _ _ = functionalExtensionality (Associativity cat _ _)

Exercise_2_1_2 : {cat : Category} -> {a, b, c, d : Object cat} ->
  (h : Morphism cat c d) -> (g : Morphism cat b c) -> (f : Morphism cat a b) ->
  postCompose {cat} {a} {b} {c=d} (postCompose {cat} {a=b} {b=c} {c=d} h g) f =
    postCompose h {cat} {a} {b=c} {c=d} (postCompose {cat} {a} {b} {c} g f)
Exercise_2_1_2 {cat} = Associativity cat

Exercise_2_1_3 : {cat : Category} -> {a, b, c, d : Object cat} ->
  (g : Morphism cat b c) -> (f : Morphism cat a b) ->
  preCompose {cat} {a} {b=c} {c=d} ((.*) {cat} {a} {b} {c} g f) =
    (preCompose {cat} {a} {b} {c=d} f) .
      (preCompose {cat} {a=b} {b=c} {c=d} g)
Exercise_2_1_3 {a} {b} {c} {d} {cat} _ _ =
  functionalExtensionality (\_ => sym (Associativity cat _ _ _))

{- Post-composition with the identity leaves arrows unchanged.
 - (So post-composition with the identity is itself the identity on
 - the type of arrows terminating in a.) -}
Exercise_2_3_1_post : {cat : Category} -> {a, b : Object cat} ->
  (f : Morphism cat b a) ->
  postCompose {cat} {a=b} {b=a} {c=a} (catId {cat} a) f = f
Exercise_2_3_1_post f = LeftIdentity cat f

{- Pre-composition with the identity leaves arrows unchanged.
 - (So pre-composition with the identity is itself the identity on
 - the type of arrows originating in a.) -}
Exercise_2_3_1_pre : {cat : Category} -> {a, b : Object cat} ->
  (f : Morphism cat a b) ->
  preCompose {cat} {a} {b=a} {c=b} (catId {cat} a) f = f
Exercise_2_3_1_pre f = RightIdentity cat f