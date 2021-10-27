import .love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 3: Forward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (3 points): Fokkink Logic Puzzles

If you have studied Logic and Sets with Prof. Fokkink, you will know he is fond
of logic puzzles. This question is a tribute.

Consider the following tactical proof: -/

lemma about_implication :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
begin
  intros a b hor ha,
  apply or.elim hor,
  { intro hna,
    apply false.elim,
    apply hna,
    exact ha },
  { intro hb,
    exact hb }
end

/-! 1.1 (1 point). Prove the same lemma again, this time by providing a proof
term.

Hint: There is an easy way. -/

lemma about_implication₂ :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
sorry

/-! 1.2 (2 points). Prove the same Fokkink lemma again, this time by providing a
structured proof, with `assume`s and `show`s. -/

lemma about_implication₃ :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
sorry


/-! ## Question 2 (6 points): Connectives and Quantifiers

2.1 (4 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other lemmas than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

lemma all_or_commute {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
sorry

/-! 2.2 (2 points). We have proved or stated three of the six possible
implications between `excluded_middle`, `peirce`, and `double_negation`. Prove
the three missing implications using structured proofs, exploiting the three
theorems we already have. -/

namespace backward_proofs

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn :
  double_negation → peirce :=
sorry

lemma em_of_peirce :
  peirce → excluded_middle :=
sorry

lemma dn_of_em :
  excluded_middle → double_negation :=
sorry

end backward_proofs

end LoVe
