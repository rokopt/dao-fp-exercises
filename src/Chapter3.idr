module Chapter3

import Category

%default total

Exercise_3_1_2 : {cat : Category} -> (a : Object cat) -> Isomorphic {cat} a a
Exercise_3_1_2 a = (catId a ** catId a ** (LeftIdentity _ _, LeftIdentity _ _))