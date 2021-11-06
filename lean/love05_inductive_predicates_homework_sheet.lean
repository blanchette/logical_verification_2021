import .lovelib


/-! # LoVe Homework 5: Inductive Predicates

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (3 points + 1 bonus point): A Type of λ-Terms

Recall the type of λ-terms from question 3 of exercise 4: -/

inductive term : Type
| var : string → term
| lam : string → term → term
| app : term → term → term

/-! 1.1 (1 point). Define an inductive predicate `is_lam` that returns `true` if
its argument is of the form `term.lam …` and that returns false otherwise. -/

-- enter your definition here

/-! 1.2 (2 points). Validate your answer to question 1.1 by proving the following
lemmas: -/

lemma is_lam_lam (s : string) (t : term) :
  is_lam (term.lam s t) :=
sorry

lemma not_is_lam_var (s : string) :
  ¬ is_lam (term.var s) :=
sorry

lemma not_is_lam_app (t u : term) :
  ¬ is_lam (term.app t u) :=
sorry

/-! 1.3 (1 bounus point). Define an inductive predicate `is_βnf` that determines
whether a λ-term is in β-normal form. A λ-term is in β-normal form if it
contains no subterm of the form `(λx, t) u`, i.e., a λ-expression applied to an
argument. Another way to characterize the β-normal form is to say that no
β-reduction is possible in the term.

Hint: Use `is_lam` somewhere. -/

-- enter your definition here


/-! ## Question 2 (6 points): Transitive Closure

In mathematics, the transitive closure `R⁺` of a binary relation `R` over a
set `A` can be defined as the smallest solution satisfying the following rules:

    (base) for all `a, b ∈ A`, if `a R b`, then `a R⁺ b`;
    (step) for all `a, b, c ∈ A`, if `a R b` and `b R⁺ c`, then `a R⁺ c`.

In Lean, we can define this notion as follows, by identifying the set `A` with
the type `α`: -/

inductive tc_v1 {α : Type} (r : α → α → Prop) : α → α → Prop
| base {a b : α}   : r a b → tc_v1 a b
| step {a b c : α} : r a b → tc_v1 b c → tc_v1 a c

/-! 2.1 (1 point). Rule `(step)` makes it convenient to extend transitive chains
by adding links to the left. Another way to define the transitive closure `R⁺`
would use replace `(step)` with the following right-leaning rule:

    (pets) for all `a, b, c ∈ A`, if `a R⁺ b` and `b R c`, then `a R⁺ c`.

Define a predicate `tc_v2` that embodies this alternative definition. -/

-- enter your definition here

/-! 2.2 (1 point). Yet another definition of the transitive closure `R⁺` would
use the following symmetric rule instead of `(step)` or `(pets)`:

    (trans) for all `a, b, c ∈ A`, if `a R⁺ b` and `b R⁺ c`, then `a R⁺ c`.

Define a predicate `tc_v3` that embodies this alternative definition. -/

-- enter your definition here

/-! 2.3 (1 point). Prove that `(step)` also holds as a lemma about `tc_v3`. -/

lemma tc_v3_step {α : Type} (r : α → α → Prop) (a b c : α) (rab : r a b)
    (tbc : tc_v3 r b c) :
  tc_v3 r a c :=
sorry

/-! 2.4 (1 point). Prove the following lemma by rule induction: -/

lemma tc_v1_pets {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b, tc_v1 r a b → r b c → tc_v1 r a c :=
sorry

/-! 2.5 (2 points). Prove the same lemma again on "paper".

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `linarith`
need not be justified if you think they are obvious (to humans), but you should
say which key lemmas they depend on. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

-- enter your paper proof here

end LoVe
