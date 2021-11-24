import .love08_operational_semantics_exercise_sheet
import .love09_hoare_logic_demo


/-! # LoVe Homework 9: Hoare Logic

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points): Hoare Logic for Dijkstra's Guarded Command Language

Recall the definition of GCL from exercise 8: -/

namespace gcl

#check stmt
#check big_step

/-! The definition of Hoare triples for partial correctness is unsurprising: -/

def partial_hoare (P : state → Prop) (S : stmt state) (Q : state → Prop) :
  Prop :=
∀s t, P s → (S, s) ⟹ t → Q t

local notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` :=
partial_hoare P S Q

namespace partial_hoare

/-! 1.1 (4 points). Prove the following Hoare rules: -/

lemma consequence {P P' Q Q' : state → Prop} {S} (h : {* P *} S {* Q *})
    (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
  {* P' *} S {* Q' *} :=
sorry

lemma assign_intro {P : state → Prop} {x} {a : state → ℕ}:
  {* λs, P (s{x ↦ a s}) *} stmt.assign x a {* P *} :=
sorry

lemma assert_intro {P Q : state → Prop} :
  {* λs, Q s → P s *} stmt.assert Q {* P *} :=
sorry

lemma seq_intro {P Q R S T} (hS : {* P *} S {* Q *}) (hT : {* Q *} T {* R *}) :
  {* P *} stmt.seq S T {* R *} :=
sorry

lemma choice_intro {P Q Ss}
    (h : ∀i (hi : i < list.length Ss), {* P *} list.nth_le Ss i hi {* Q *}) :
  {* P *} stmt.choice Ss {* Q *} :=
sorry

/-! 1.2 (2 points). Prove the rule for `loop`. Notice the similarity with the
rule for `while` in the WHILE language. -/

lemma loop_intro {P S} (h : {* P *} S {* P *}) :
  {* P *} stmt.loop S {* P *} :=
sorry

end partial_hoare

end gcl


/-! ## Question 2 (3 points): Factorial

The following WHILE program is intended to compute the factorial of `n`, leaving
the result in `r`. -/

def FACT : stmt :=
stmt.assign "r" (λs, 1) ;;
stmt.while (λs, s "n" ≠ 0)
  (stmt.assign "r" (λs, s "r" * s "n") ;;
   stmt.assign "n" (λs, s "n" - 1))

/-! 2.1 (1 point). Define the factorial function. -/

def fact : ℕ → ℕ :=
sorry

/-! 2.2 (2 points). Prove the correctness of `FACT` using `vcg`. -/

lemma FACT_correct (n₀ : ℕ) :
  {* λs, s "n" = n₀ *} FACT {* λs, s "r" = fact n₀ *} :=
sorry

end LoVe
