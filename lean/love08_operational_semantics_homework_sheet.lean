import .love01_definitions_and_statements_demo


/-! # LoVe Homework 8: Operational Semantics

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (5 points): Arithmetic expressions

Recall the type of arithmetic expressions from lecture 1 and its evaluation
function: -/

#check aexp
#check eval

/-! Let us introduce the following abbreviation for an environment that maps
variable names to values: -/

def envir : Type :=
string → ℤ

/-! 1.1 (2 points). Complete the following Lean definition of a big-step-style
semantics for arithmetic expressions. The predicate `big_step` (`⟹`) relates
an arithmetic expression, an environment, and the value to which it the
expression evaluates in the given environment: -/

inductive big_step : aexp × envir → ℤ → Prop
| num {i env} : big_step (aexp.num i, env) i

infix ` ⟹ ` : 110 := big_step

/-! 1.2 (1 point). Prove the following lemma to validate your definition
above. -/

lemma big_step_add_two_two (env : envir) :
  (aexp.add (aexp.num 2) (aexp.num 2), env) ⟹ 4 :=
sorry

/-! 1.3 (2 points). Prove that the big-step semantics is sound with respect to
the `eval` function: -/

lemma big_step_sound (env : envir) (a : aexp) (i : ℤ) :
  (a, env) ⟹ i → eval env a = i :=
sorry


/-! ## Question 2 (4 points + 1 bonus points): Semantics of Regular Expressions

Regular expression are a very popular tool for software development. Often,
when textual input needs to be analyzed it is matched against a regular
expression. In this question, we define the syntax of regular expressions and
what it means for a regular expression to match a string.

We define `regex` to represent the following grammar:

    R ::= ∅       — `nothing`: matches nothing
        | ε       — `empty`: matches the empty string
        | a       — `atom`: matches the atom `a`
        | R ⬝ R    — `concat`: matches the concatenation of two regexes
        | R + R   — `alt`: matches either of two regexes
        | R*      — `star`: matches arbitrary many repetitions of a regex

Notice the rough correspondence with a WHILE language:

    `empty`  ~ `skip`
    `atom`   ~ assignment
    `concat` ~ sequential composition
    `alt`    ~ conditional statement
    `star`   ~ while loop -/

inductive regex (α : Type) : Type
| nothing {} : regex
| empty   {} : regex
| atom       : α → regex
| concat     : regex → regex → regex
| alt        : regex → regex → regex
| star       : regex → regex

/-! The `matches r s` predicate indicates that the regular expression `r` matches
the string `s`. -/

inductive matches {α : Type } : regex α → list α → Prop
| empty :
  matches regex.empty []
| atom (a : α) :
  matches (regex.atom a) [a]
| concat {r₁ r₂ : regex α} (s₁ s₂ : list α) (h₁ : matches r₁ s₁)
    (h₂ : matches r₂ s₂) :
  matches (regex.concat r₁ r₂) (s₁ ++ s₂)
| alt_left {r₁ r₂ : regex α} (s : list α) (h : matches r₁ s) :
  matches (regex.alt r₁ r₂) s
| alt_right {r₁ r₂ : regex α} (s : list α) (h : matches r₂ s) :
  matches (regex.alt r₁ r₂) s
| star_base {r : regex α} :
  matches (regex.star r) []
| star_step {r : regex α} (s s' : list α) (h₁ : matches r s)
    (h₂ : matches (regex.star r) s') :
  matches (regex.star r) (s ++ s')

/-! The introduction rules correspond to the following cases:

* match the empty string
* match one atom (e.g., character)
* match two concatenated regexes
* match the left option
* match the right option
* match the empty string (the base case of `R*`)
* match `R` followed again by `R*` (the induction step of `R*`)

2.1 (1 point). Explain why there is no rule for `nothing`. -/

-- enter your answer here

/-! 2.2 (3 points). Prove the following inversion rules. -/

@[simp] lemma matches_atom {α : Type} {s : list α} {a : α} :
  matches (regex.atom a) s ↔ s = [a] :=
sorry

@[simp] lemma matches_nothing {α : Type} {s : list α} :
  ¬ matches regex.nothing s :=
sorry

@[simp] lemma matches_empty {α : Type} {s : list α} :
  matches regex.empty s ↔ s = [] :=
sorry

@[simp] lemma matches_concat {α : Type} {s : list α} {r₁ r₂ : regex α} :
  matches (regex.concat r₁ r₂) s
  ↔ (∃s₁ s₂, matches r₁ s₁ ∧ matches r₂ s₂ ∧ s = s₁ ++ s₂) :=
sorry

@[simp] lemma matches_alt {α : Type} {s : list α} {r₁ r₂ : regex α} :
  matches (regex.alt r₁ r₂) s ↔ (matches r₁ s ∨ matches r₂ s) :=
sorry

/-! 2.3 (1 bonus points). Prove the following inversion rule. -/

lemma matches_star {α : Type} {s : list α} {r : regex α} :
  matches (regex.star r) s ↔
  (s = [] ∨ (∃s₁ s₂, matches r s₁ ∧ matches (regex.star r) s₂ ∧ s = s₁ ++ s₂)) :=
sorry

end LoVe
