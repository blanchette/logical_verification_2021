import .love05_inductive_predicates_demo


/-! # LoVe Exercise 5: Inductive Predicates -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Even and Odd

The `even` predicate is true for even numbers and false for odd numbers. -/

#check even

/-! We define `odd` as the negation of `even`: -/

def odd (n : ℕ) : Prop :=
  ¬ even n

/-! 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases'` is useful to reason about hypotheses of the form `even …`. -/

@[simp] lemma odd_1 :
  odd 1 :=
begin
  intro h,
  cases' h
end

/-! 1.2. Prove that 3 and 5 are odd. -/

lemma odd_3 :
  odd 3 :=
begin
  intro h,
  cases' h,
  cases' h
end

lemma odd_5 :
  odd 5 :=
begin
  intro h,
  cases' h,
  cases' h,
  cases' h
end

/-! 1.3. Complete the following proof by structural induction. -/

lemma even_two_times :
  ∀m : ℕ, even (2 * m)
| 0       := even.zero
| (m + 1) :=
  begin
    apply even.add_two,
    simp,
    apply even_two_times
  end

/-! 1.4. Complete the following proof by rule induction.

Hint: You can use the `cases'` tactic (or `match … with`) to destruct an
existential quantifier and extract the witness. -/

lemma even_imp_exists_two_times :
  ∀n : ℕ, even n → ∃m, n = 2 * m :=
begin
  intros n hen,
  induction' hen,
  case zero {
    apply exists.intro 0,
    refl },
  case add_two : k hek ih {
    cases' ih with w hk,
    apply exists.intro (w + 1),
    rw hk,
    linarith }
end

/-! 1.5. Using `even_two_times` and `even_imp_exists_two_times`, prove the
following equivalence. -/

lemma even_iff_exists_two_times (n : ℕ) :
  even n ↔ ∃m, n = 2 * m :=
begin
  apply iff.intro,
  { apply even_imp_exists_two_times },
  { intro h,
    cases' h,
    simp *,
    apply even_two_times }
end

/-! 1.6 (**optional**). Give a structurally recursive definition of `even` and
test it with `#eval`.

Hint: The negation operator on `bool` is called `not`. -/

def even_rec : nat → bool
| 0       := tt
| (n + 1) := not (even_rec n)

#eval even_rec 0
#eval even_rec 1
#eval even_rec 2
#eval even_rec 3
#eval even_rec 4


/-! ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check score

/-! 2.1. Define an inductive predicate that returns true if the server is ahead
of the receiver and that returns false otherwise. -/

inductive srv_ahead : score → Prop
| vs {m n : ℕ} : m > n → srv_ahead (score.vs m n)
| adv_srv      : srv_ahead score.adv_srv
| game_srv     : srv_ahead score.game_srv

/-! 2.2. Validate your predicate definition by proving the following lemmas. -/

lemma srv_ahead_vs {m n : ℕ} (hgt : m > n) :
  srv_ahead (score.vs m n) :=
srv_ahead.vs hgt

lemma srv_ahead_adv_srv :
  srv_ahead score.adv_srv :=
srv_ahead.adv_srv

lemma not_srv_ahead_adv_rcv :
  ¬ srv_ahead score.adv_rcv :=
begin
  intro h,
  cases' h
end

lemma srv_ahead_game_srv :
  srv_ahead score.game_srv :=
srv_ahead.game_srv

lemma not_srv_ahead_game_rcv :
  ¬ srv_ahead score.game_rcv :=
begin
  intro h,
  cases' h
end

/-! 2.3. Compare the above lemma statements with your definition. What do you
observe? -/

/-! The positive lemmas correspond exactly to the introduction rules of the
definition. By contrast, the negative lemmas have no counterparts in the
definition. -/


/-! ## Question 3: Binary Trees

3.1. Prove the converse of `is_full_mirror`. You may exploit already proved
lemmas (e.g., `is_full_mirror`, `mirror_mirror`). -/

#check is_full_mirror
#check mirror_mirror

lemma mirror_is_full {α : Type} :
  ∀t : btree α, is_full (mirror t) → is_full t :=
begin
  intros t fmt,
  have fmmt : is_full (mirror (mirror t)) :=
    is_full_mirror _ fmt,
  rw mirror_mirror at fmmt,
  assumption
end

/-! 3.2. Define a `map` function on binary trees, similar to `list.map`. -/

def map_btree {α β : Type} (f : α → β) : btree α → btree β
| btree.empty        := btree.empty
| (btree.node a l r) := btree.node (f a) (map_btree l) (map_btree r)

/-! 3.3. Prove the following lemma by case distinction. -/

lemma map_btree_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : btree α, map_btree f t = btree.empty ↔ t = btree.empty
| btree.empty        := by simp [map_btree]
| (btree.node _ _ _) := by simp [map_btree]

/-! 3.4 (**optional**). Prove the following lemma by rule induction. -/

lemma map_btree_mirror {α β : Type} (f : α → β) :
  ∀t : btree α, is_full t → is_full (map_btree f t) :=
begin
  intros t hfull,
  induction' hfull,
  case empty {
    simp [map_btree],
    exact is_full.empty },
  case node {
    simp [map_btree],
    apply is_full.node,
    { exact ih_hfull f },
    { exact ih_hfull_1 f },
    { simp [map_btree_eq_empty_iff],
      assumption } }
end

end LoVe
