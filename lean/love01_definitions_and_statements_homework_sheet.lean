import .lovelib


/-! # LoVe Homework 1: Definitions and Statements

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (1 points): Snoc

1.1 (1 point). Define the function `snoc` that appends a single element to the
end of a list. Your function should be defined by recursion and not using `++`
(`list.append`). -/

def snoc {α : Type} : list α → α → list α :=
sorry

/-! 1.2 (0 point). Convince yourself that your definition of `snoc` works by
testing it on a few examples. -/

#reduce snoc [1] 2
-- invoke `#reduce` or `#eval` here


/-! ## Question 2 (3 points): Map

2.1 (1 point). Define a generic `map` function that applies a function to every
element in a list. -/

def map {α : Type} {β : Type} (f : α → β) : list α → list β :=
sorry

/-! 2.2 (2 points). State (without proving them) the so-called functorial
properties of `map` as lemmas. Schematically:

     map (λx, x) xs = xs
     map (λx, g (f x)) xs = map g (map f xs)

Try to give meaningful names to your lemmas. Also, make sure to state the second
property as generally as possible, for arbitrary types. -/

-- enter your lemma statements here


/-! ## Question 3 (5 points): λ-Terms

We start by declaring four new opaque types. -/

constants α β γ δ : Type

/-! 3.1 (2 points). Complete the following definitions, by providing terms with
the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def B : (α → β) → (γ → α) → γ → β :=
sorry

def S : (α → β → γ) → (α → β) → α → γ :=
sorry

def more_nonsense : ((α → β) → γ → δ) → γ → β → δ :=
sorry

def even_more_nonsense : (α → β) → (α → γ) → α → β → γ :=
sorry

/-! 3.2 (1 point). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse". -/

def weak_peirce : ((((α → β) → α) → α) → β) → β :=
sorry

/-! 3.3 (2 points). Show the typing derivation for your definition of `B` above,
using ASCII or Unicode art. You might find the characters `–` (to draw
horizontal bars) and `⊢` useful.

Feel free to introduce abbreviations to avoid repeating large contexts `Γ`. -/

-- write your solution here

end LoVe
