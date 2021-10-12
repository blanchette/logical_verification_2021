import .love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 2: Backward Proofs

Homework must be done individually. -/

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace backward_proofs


/-! ## Question 1 (4 points): Connectives and Quantifiers

1.1 (3 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`. -/

lemma B (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
sorry

lemma S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
sorry

lemma more_nonsense (a b c d : Prop) :
  ((a → b) → c → d) → c → b → d :=
sorry

lemma even_more_nonsense (a b c : Prop) :
  (a → b) → (a → c) → a → b → c :=
sorry

/-! 1.2 (1 point). Prove the following lemma using basic tactics. -/

lemma weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b :=
sorry


/-! ## Question 2 (5 points): Logical Connectives

2.1 (1 point). Prove the following property about double negation using basic
tactics.

Hints:

* Keep in mind that `¬ a` is the same as `a → false`. You can start by
  invoking `rw not_def` four times if this helps you.

* You will need to apply the elimination rule for `false` at a key point in the
  proof. -/

lemma herman (a : Prop) :
  ¬¬ (¬¬ a → a) :=
sorry

/-! 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.

Hints:

* One way to find the definitions of `double_negation` and `excluded_middle`
  quickly is to

  1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
  2. move the cursor to the identifier `double_negation` or `excluded_middle`;
  3. click the identifier.

* You can use `rw double_negation` to unfold the definition of
  `double_negation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check double_negation
#check excluded_middle

lemma em_of_dn :
  double_negation → excluded_middle :=
sorry

/-! 2.3 (2 points). We have proved three of the six possible implications between
`excluded_middle`, `peirce`, and `double_negation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check peirce_of_em
#check dn_of_peirce
#check em_of_dn

/-! 2.3 (2 points). We have proved three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check peirce_of_em
#check dn_of_peirce
#check em_of_dn

-- enter your solution here

end backward_proofs

end LoVe
