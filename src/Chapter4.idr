module Chapter4

%default total

Exercise_4_1_1_not : Bool -> Bool
Exercise_4_1_1_not b = if b then False else True

Exercise_4_1_1_id : Bool -> Bool
Exercise_4_1_1_id b = b

Exercise_4_1_1_const_true : Bool -> Bool
Exercise_4_1_1_const_true _ = True

Exercise_4_1_1_const_false : Bool -> Bool
Exercise_4_1_1_const_false _ = False
