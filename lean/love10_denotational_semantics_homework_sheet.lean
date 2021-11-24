import .love10_denotational_semantics_demo


/-! # LoVe Homework 10: Denotational Semantics

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

/-! The following command enables noncomputable decidability on every `Prop`.
The `priority 0` attribute ensures this is used only when necessary; otherwise,
it would make some computable definitions noncomputable for Lean. Depending on
how you solve question 2.2, this command might help you. -/

local attribute [instance, priority 0] classical.prop_decidable

/-! Denotational semantics are well suited to functional programming. In this
exercise, we will study some representations of functional programs in Lean and
their denotational semantics.

The `nondet` type represents functional programs that can perform
nondeterministic computations: A program can choose between many different
computation paths / return values. Returning no results at all is represented
by `fail`, and nondeterministic choice between two options (identified by the
`bool` values `tt` and `ff`) is represented by `choice`. -/

inductive nondet (α : Type) : Type
| pure    : α → nondet
| fail {} : nondet
| choice  : (bool → nondet) → nondet

namespace nondet


/-! ## Question 1 (4 points): The `nondet` Monad

The `nondet` inductive type forms a monad. The `pure` operator is `nondet.pure`.
`bind` is as follows: -/

def bind {α β : Type} : nondet α → (α → nondet β) → nondet β
| (pure x)   f := f x
| fail       f := fail
| (choice k) f := choice (λb, bind (k b) f)

instance : has_pure nondet :=
{ pure := @pure }

instance : has_bind nondet :=
{ bind := @bind }

/-! 1.1 (3 points). Prove the three monad laws for `nondet`.

Hints:

* To unfold the definition of `>>=`, invoke `simp [(>>=)]`.

* To prove `f = g` from `∀x, f x = g x`, use the theorem `funext`. -/

lemma pure_bind {α β : Type} (x : α) (f : α → nondet β) :
  pure x >>= f = f x :=
sorry

lemma bind_pure {α : Type} :
  ∀mx : nondet α, mx >>= pure = mx :=
sorry

lemma bind_assoc {α β γ : Type} :
  ∀(mx : nondet α) (f : α → nondet β) (g : β → nondet γ),
    ((mx >>= f) >>= g) = (mx >>= (λa, f a >>= g)) :=
sorry

/-! The function `portmanteau` computes a portmanteau of two lists: A
portmanteau of `xs` and `ys` has `xs` as a prefix and `ys` as a suffix, and they
overlap. We use `starts_with xs ys` to test that `ys` has `xs` as a prefix. -/

def starts_with : list ℕ → list ℕ → bool
| (x :: xs) []        := ff
| []        ys        := tt
| (x :: xs) (y :: ys) := (x = y) && starts_with xs ys

#eval starts_with [1, 2] [1, 2, 3]
#eval starts_with [1, 2, 3] [1, 2]

def portmanteau : list ℕ → list ℕ → list (list ℕ)
| []        ys := []
| (x :: xs) ys :=
  list.map (list.cons x) (portmanteau xs ys) ++
  (if starts_with (x :: xs) ys then [ys] else [])

/-! Here are some examples of portmanteaux: -/

#reduce portmanteau [0, 1, 2, 3] [2, 3, 4]
#reduce portmanteau [0, 1] [2, 3, 4]
#reduce portmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4]

/-! 1.2 (1 point). Translate the `portmanteau` program from the `list` monad to
the `nondet` monad. -/

def nondet_portmanteau : list ℕ → list ℕ → nondet (list ℕ) :=
sorry


/-! ## Question 2 (5 points): Nondeterminism, Denotationally

2.1 (2 points). Give a denotational semantics for `nondet`, mapping it into a
`list` of all results. `pure` returns one result, `fail` returns zero, and
`choice` combines the results of either option. -/

def list_sem {α : Type} : nondet α → list α :=
sorry

/-! Check that the following lines give the same output as for `portmanteau` (if
you have answered question 1.2): -/

#reduce list_sem (nondet_portmanteau [0, 1, 2, 3] [2, 3, 4])
#reduce list_sem (nondet_portmanteau [0, 1] [2, 3, 4])
#reduce list_sem (nondet_portmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4])

/-! 2.2 (2 points). Often, we are not interested in getting all outcomes, just
the first successful one. Give a semantics for `nondet` that produces the first
successful result, if any. Your solution should *not* use `list_sem`. -/

noncomputable def option_sem {α : Type} : nondet α → option α :=
sorry

/-! 2.3 (1 point). Prove the theorem `list_option_compat` below, showing that
the two semantics you defined are compatible. -/

lemma head'_orelse_eq_head'_append {α : Type} (xs ys : list α) :
  (list.head' xs <|> list.head' ys) = list.head' (xs ++ ys) :=
by induction' xs; simp

theorem list_option_compat {α : Type} :
  ∀mx : nondet α, option_sem mx = list.head' (list_sem mx) :=
sorry

end nondet

end LoVe
