import .love03_forward_proofs_demo


/-! # LoVe Homework 4: Functional Programming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points): Reverse of a List

Recall the `reverse` operation and the `reverse_append` and `reverse_reverse`
lemmas from the demo of lecture 3. -/

#check reverse
#check reverse_append
#check reverse_append₂
#check reverse_reverse

/-! 1.1 (3 points). Prove the following distributive property using the
calculational style for the induction step. -/

lemma reverse_append₃ {α : Type} :
  ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs :=
sorry

/-! 1.2 (3 points). Prove the induction step in the proof below using the
calculational style, following this proof sketch:

      reverse (reverse (x :: xs))
    =     { by definition of `reverse` }
      reverse (reverse xs ++ [x])
    =     { using the lemma `reverse_append` }
      reverse [x] ++ reverse (reverse xs)
    =     { by the induction hypothesis }
      reverse [x] ++ xs
    =     { by definition of `++` and `reverse` }
      [x] ++ xs
    =     { by computation }
      x :: xs -/

lemma reverse_reverse₂ {α : Type} :
  ∀xs : list α, reverse (reverse xs) = xs
| []        := by refl
| (x :: xs) :=
sorry


/-! ## Question 2 (3 points): Gauss's Summation Formula -/

-- `sum_upto f n = f 0 + f 1 + ⋯ + f n`
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/-! 3.1 (2 point). Prove the following lemma, discovered by Carl Friedrich Gauss
as a pupil.

Hint: The `mul_add` and `add_mul` lemmas might be useful to reason about
multiplication. -/

#check mul_add
#check add_mul

lemma sum_upto_eq :
  ∀m : ℕ, 2 * sum_upto (λi, i) m = m * (m + 1) :=
sorry

/-! 3.2 (1 point). Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (f g : ℕ → ℕ) :
  ∀n : ℕ, sum_upto (λi, f i + g i) n = sum_upto f n + sum_upto g n :=
sorry


/-! ## Question 3 (2 bonus points): Structures and Type Classes

3.1 (0 points). Using the `structure` command, define the type `ℤ3` of triples of
integers. Recall that a point in ℤ³ has x, y, and z coordinates. -/

#check ℤ

structure ℤ3 :=
sorry

/-! 3.2 (1 bonus point). Define an addition function on ℝ³. -/

def ℤ3.add (p q : ℤ3) : ℤ3 :=
sorry

/-! 3.3 (1 bonus point). Write an instance that shows ℝ³ instantiates the
`has_add` type class. -/

#print has_add

-- enter your answer here

end LoVe
