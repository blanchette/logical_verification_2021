import .lovelib


/-! # LoVe Homework 7: Metaprogramming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (9 points): A `harmless` Tactic

We develop a tactic that applies all harmless introduction and elimination
rules for the connectives and quantifiers exhaustively. A rule is said to be
__harmless__ if, given a provable goal, it always gives rise to provable
subgoals. In addition, we will require that harmless rules do not introduce
metavariables (since these can easily be instantiated accidentally with the wrong
terms).

We proceed in three steps.

1.1 (3 points). Develop a `harmless_intros` tactic that applies the introduction
rules for `true`, `∧`, and `↔` and that invokes `tactic.intro` (or
`tactic.intro1`) for `→`/`∀`. The tactic generalizes `intro_ands` from the
exercise.

Hint: You can use the `<|>` operator between the tactics used for different
logical symbols. -/

#check tactic.repeat
#check tactic.applyc
#check tactic.intro
#check tactic.intro1

meta def harmless_intros : tactic unit :=
sorry

lemma abcd (a b c d : Prop) :
  a → ¬ b ∧ (c ↔ d) :=
begin
  harmless_intros,
  /- The proof state should be roughly as follows:

  a b c d : Prop,
  a_1 : a,
  a_2 : b
  ⊢ false

  a b c d : Prop,
  a_1 : a,
  a_2 : c
  ⊢ d

  a b c d : Prop,
  a_1 : a,
  a_2 : d
  ⊢ c -/
  repeat { sorry }
end

/-! 1.2 (4 points). Develop a `harmless_destructs` tactic that eliminates
`false`, `∧`, `∨`, `↔`, and `∃`. The tactic generalizes `destruct_ands` from the
exercise. -/

meta def harmless_destructs : tactic unit :=
sorry

lemma abcdef (a b c d e f : Prop) (p : ℕ → Prop)
    (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
    (hex : ∃x, p x) :
  false :=
begin
  harmless_destructs,
  /- The proof state should be roughly as follows:

  2 goals
  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  hand_left : a,
  hor : c,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  hand_left : a,
  hor : d,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false -/
  repeat { sorry }
end

/-! 1.3 (2 points). Implement a `harmless` tactic that first performs
introduction, then elimination, and finally proves all the subgoals that can be
discharged directly by `tactic.assumption`. The tactic generalizes `destro_and`
from the exercise.

Hint: Depending on how you structure your code, the `tactic.try` combinator
might be useful. -/

meta def harmless : tactic unit :=
sorry

lemma abcdef₂ (a b c d e f : Prop) (p : ℕ → Prop)
    (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
    (hex : ∃x, p x) :
  a → ¬ b ∧ (c ↔ d) :=
begin
  harmless,
  /- The proof state should be roughly as follows:

  3 goals
  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  a_1 : a,
  a_2 : b,
  hand_left : a,
  hor : c,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  a_1 : a,
  a_2 : b,
  hand_left : a,
  hor : d,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  a_1 : a,
  a_2 : c,
  hand_left : a,
  hor : c,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ d -/
  repeat { sorry }
end


/-! ## Question 2 (2 bonus points): An `auto` Tactic

2.1 (1 bonus point). Develop an Isabelle-style `auto` tactic.

This tactic would apply all harmless introduction and elimination rules. In
addition, it would try potentially harmful rules (such as `or.intro_left` and
`false.elim`) but backtrack at some point (or try several possibilities in
parallel). Iterative deepening may be a valid approach, or best-first search, or
breadth-first search. The tactic should also try to apply assumptions whose
conclusion matches the goal, but backtrack if necessary.

See also "Automatic Proof and Disproof in Isabelle/HOL"
(https://www.cs.vu.nl/~jbe248/frocos2011-dis-proof.pdf) by Blanchette, Bulwahn,
and Nipkow, and the references they give.

2.2 (1 bonus point). Test your tactic on some benchmarks.

You can try your tactic on logic puzzles of the kinds we proved in exercise 2
and homework 2. Please include these below. -/

end LoVe
