module Chapter3

import Category

%default total

Exercise_3_1_2 : {cat : Category} -> (a : Object cat) -> Isomorphic {cat} a a
Exercise_3_1_2 a = (catId a ** catId a ** (LeftIdentity _ _, LeftIdentity _ _))

Exercise_3_1_3 : {cat : Category} -> {a, b : Object cat} ->
  IsTerminal {cat} a -> IsTerminal {cat} b -> Isomorphic {cat} a b
Exercise_3_1_3 aIsTerminal bIsTerminal = ?Exercise_3_1_3_hole

Exercise_3_1_4 : {cat : Category} -> {a, b : Object cat} ->
  (aIsTerminal : IsTerminal {cat} a) -> (bIsTerminal : IsTerminal {cat} b) ->
  IsUnique {cat} {a} {b}
    (IsIsomorphism {cat} {a} {b})
    (fst (Exercise_3_1_3 {cat} {a} {b} aIsTerminal bIsTerminal))
Exercise_3_1_4 aIsTerminal bIsTerminal = ?Exercise_3_1_4_hole