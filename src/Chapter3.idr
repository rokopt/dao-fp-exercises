module Chapter3

import TypesAndFunctions
import Category

%default total

Exercise_3_1_1 : {cat : Category} -> {a, b, c : Object cat} ->
  Isomorphic {cat} a b -> Bijection (Morphism cat a c) (Morphism cat b c)
Exercise_3_1_1 {cat}
  (abIsomorphism ** baIsomorphism ** (isLeftInverse, isRightInverse)) =
    ((\f : Morphism cat a c => f .* baIsomorphism) **
     (\g : Morphism cat b c => g .* abIsomorphism) **
     (\f' : Morphism cat a c =>
       let
         assoc = Associativity cat f' baIsomorphism abIsomorphism
         rightId = RightIdentity cat f'
       in
       replace {p=(\f'' => f'' = f')} (sym assoc)
         (replace {p=(\z => f' .* z = f')} (sym isLeftInverse) rightId),
      \g' : Morphism cat b c =>
       let
         assoc = Associativity cat g' abIsomorphism baIsomorphism
         rightId = RightIdentity cat g'
       in
       replace {p=(\g'' => g'' = g')} (sym assoc)
         (replace {p=(\z => g' .* z = g')} (sym isRightInverse) rightId)))

Exercise_3_1_2 : {cat : Category} -> (a : Object cat) -> Isomorphic {cat} a a
Exercise_3_1_2 a = (catId a ** catId a ** (LeftIdentity _ _, LeftIdentity _ _))

Exercise_3_1_3 : {cat : Category} -> {a, b : Object cat} ->
  IsTerminal {cat} a -> IsTerminal {cat} b -> Isomorphic {cat} a b
Exercise_3_1_3 aIsTerminal bIsTerminal =
  case (aIsTerminal b, bIsTerminal a) of
    ((baIso ** (_, onlyBA)), (abIso ** (_, onlyAB))) =>
      (abIso ** baIso **
        (IdOnlyTerminalEndomorphism aIsTerminal (baIso .* abIso),
         IdOnlyTerminalEndomorphism bIsTerminal (abIso .* baIso)))

Exercise_3_1_4 : {cat : Category} -> {a, b : Object cat} ->
  (aIsTerminal : IsTerminal {cat} a) -> (bIsTerminal : IsTerminal {cat} b) ->
  IsUnique {cat} {a} {b}
    (IsIsomorphism {cat} {a} {b})
    (fst (Exercise_3_1_3 {cat} {a} {b} aIsTerminal bIsTerminal))
Exercise_3_1_4 {cat} {a} {b} aIsTerminal bIsTerminal =
  case (aIsTerminal b, bIsTerminal a) of
    ((baIso ** (_, onlyBA)), (abIso ** (_, onlyAB))) =>
      (?Exercise_3_1_4_hole_property,
       ?Exericse_3_1_4_hole_unique)