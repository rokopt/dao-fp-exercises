module TypesAndFunctions

%default total

public export
appEq : {a, b : Type} -> {f, g : a -> b} -> {x : a} -> f = g -> f x = g x
appEq Refl = Refl

public export
FunctionalExtensionality : (a, b : Type) -> Type
FunctionalExtensionality a b =
  {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

public export
IsLeftInverse : {a, b : Type} -> (a -> b) -> (b -> a) -> Type
IsLeftInverse f g = (x : a) -> g (f x) = x

public export
IsRightInverse : {a, b : Type} -> (a -> b) -> (b -> a) -> Type
IsRightInverse {a} {b} f g = IsLeftInverse {b=a} {a=b} g f

public export
IsInverse : {a, b : Type} -> (a -> b) -> (b -> a) -> Type
IsInverse f g = (IsLeftInverse f g, IsRightInverse f g)

public export
IsBijection : {a, b : Type} -> (a -> b) -> Type
IsBijection {a} {b} f = DPair (b -> a) (IsInverse f)

public export
Bijection : (a, b : Type) -> Type
Bijection a b = DPair (a -> b) IsBijection