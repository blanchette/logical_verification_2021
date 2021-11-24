import .love05_inductive_predicates_demo


/-! # LoVe Homework 11: Logical Foundations of Mathematics

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (7 points): Even Numbers as a Subtype

Usually, the most convenient way to represent even natural numbers is to use the
larger type `ℕ`, which also includes the odd natural numbers. If we want to
quantify only over even numbers `n`, we can add an assumption `even n` to our
lemma statement.

An alternative is to encode evenness in the type, using a subtype. We will
explore this approach.

1.1 (1 point). Define the type `evℕ` of even natural numbers, using the `even`
predicate introduced in the lecture 5 demo. -/

#print even

def evℕ : Type :=
sorry

/-! 1.2 (1 point). Prove the following lemma about the `even` predicate. You will
need it to answer question 1.3. -/

lemma even.add {m n : ℕ} (hm : even m) (hn : even n) :
  even (m + n) :=
sorry

/-! 1.3 (1 point). Define zero and addition of even numbers by filling in the
`sorry` placeholders. -/

def evℕ.zero : evℕ :=
sorry

def evℕ.add (m n : evℕ) : evℕ :=
sorry

/-! 1.4 (4 points). Prove that addition of even numbers is commutative and
associative, and has 0 as an identity element. -/

lemma evℕ.add_comm (m n : evℕ) :
  evℕ.add m n = evℕ.add n m :=
sorry

lemma evℕ.add_assoc (l m n : evℕ) :
  evℕ.add (evℕ.add l m) n = evℕ.add l (evℕ.add m n) :=
sorry

lemma evℕ.add_iden_left (n : evℕ) :
  evℕ.add evℕ.zero n = n :=
sorry

lemma evℕ.add_iden_right (n : evℕ) :
  evℕ.add n evℕ.zero = n :=
sorry


/-! ## Question 2 (2 points + 1 bonus point): Hilbert Choice

2.1 (1 bonus point). Prove the following lemma. -/

lemma exists_minimal_arg.aux (f : ℕ → ℕ) :
  ∀x m, f m = x → ∃n, ∀i, f n ≤ f i
| x m eq :=
  begin
    cases' classical.em (∃n, f n < x),
    sorry, sorry
  end

/-! Now this interesting lemma falls off: -/

lemma exists_minimal_arg (f : ℕ → ℕ) :
  ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
exists_minimal_arg.aux f _ 0 (by refl)

/-! 2.2 (1 point). Use what you learned in the lecture to define the following
function, which returns the (or an) index of the minimal element in `f`'s
image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
sorry

/-! 2.3 (1 point). Prove the following characteristic lemma about your
definition. -/

lemma minimal_arg_spec (f : ℕ → ℕ) :
  ∀i : ℕ, f (minimal_arg f) ≤ f i :=
sorry

end LoVe
