module Chapter4

import TypesAndFunctions

%default total

Exercise_4_1_1_not : Bool -> Bool
Exercise_4_1_1_not b = if b then False else True

Exercise_4_1_1_id : Bool -> Bool
Exercise_4_1_1_id b = b

Exercise_4_1_1_const_true : Bool -> Bool
Exercise_4_1_1_const_true _ = True

Exercise_4_1_1_const_false : Bool -> Bool
Exercise_4_1_1_const_false _ = False

Exercise_4_4_1_Either_a_Void_To_a : {a : Type} -> Either a Void -> a
Exercise_4_4_1_Either_a_Void_To_a (Left x) = x
Exercise_4_4_1_Either_a_Void_To_a (Right y) = void y

Exercise_4_4_1_a_To_Either_a_Void : {a : Type} -> a -> Either a Void
Exercise_4_4_1_a_To_Either_a_Void x = Left x

Exericse_4_4_1_Either_a_Void_to_a_To_Either_a_Void_id : (a : Type) ->
    IsLeftInverse
        (Exercise_4_4_1_Either_a_Void_To_a {a})
        (Exercise_4_4_1_a_To_Either_a_Void {a})
Exericse_4_4_1_Either_a_Void_to_a_To_Either_a_Void_id a (Left _) = Refl
Exericse_4_4_1_Either_a_Void_to_a_To_Either_a_Void_id a (Right _) impossible

Exercise_4_4_1_a_To_Either_a_Void_to_a_id : (a : Type) ->
    IsRightInverse
        (Exercise_4_4_1_Either_a_Void_To_a {a})
        (Exercise_4_4_1_a_To_Either_a_Void {a})
Exercise_4_4_1_a_To_Either_a_Void_to_a_id a _ = Refl

Exercise_4_4_1_are_inverses : (a : Type) ->
    IsInverse
        (Exercise_4_4_1_Either_a_Void_To_a {a})
        (Exercise_4_4_1_a_To_Either_a_Void {a})
Exercise_4_4_1_are_inverses a =
    (Exericse_4_4_1_Either_a_Void_to_a_To_Either_a_Void_id a,
     Exercise_4_4_1_a_To_Either_a_Void_to_a_id a)
