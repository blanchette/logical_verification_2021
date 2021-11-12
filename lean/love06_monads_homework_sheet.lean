import .lovelib


/-! # LoVe Homework 6: Monads

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (3 points): `map` for Monads

We will define a `map` function for monads and derive its so-called functorial
properties from the three laws.

We use Lean's definition of monads. In combination, `monad` and `is_lawful_monad`
provide the same constants, laws, and syntactic sugar as the `lawful_monad` type
class from the lecture: -/

#check monad
#check is_lawful_monad

/-! 1.1 (1 point). Define `map` on `m`. This function should not be confused
with `mmap` from the lecture's demo.

Hint: The challenge is to find a way to create a value of type `m β`. Follow the
types. Inventory all the arguments and operations available (e.g., `pure`,
`>>=`) with their types and see if you can plug them together like Lego
bricks. -/

def map {m : Type → Type} [monad m] {α β : Type} (f : α → β) (ma : m α) :
  m β := :=
sorry

/-! 1.2 (1 point). Prove the identity law for `map`.

Hint: You will need `bind_pure`. -/

lemma map_id {m : Type → Type} [monad m] [is_lawful_monad m] {α : Type}
    (ma : m α) :
  map id ma = ma :=
sorry

/-! 1.3 (1 point). Prove the composition law for `map`. -/

lemma map_map {m : Type → Type} [monad m] [is_lawful_monad m] {α β γ : Type}
    (f : α → β) (g : β → γ) (ma : m α) :
  map g (map f ma) = map (g ∘ f) ma :=
sorry


/-! ## Question 2 (6 points): Monadic Structure on Lists

`list` can be seen as a monad, similar to `option` but with several possible
outcomes. It is also similar to `set`, but the results are ordered and finite.
The code below sets `list` up as a monad. -/

namespace list

def bind {α β : Type} : list α → (α → list β) → list β
| []        f := []
| (a :: as) f := f a ++ bind as f

def pure {α : Type} (a : α) : list α :=
[a]

lemma pure_eq_singleton {α : Type} (a : α) :
  pure a = [a] :=
by refl

instance : monad list :=
{ pure := @list.pure,
  bind := @list.bind }

/-! 2.1 (2 points). Prove the following properties of `bind` under the list
constructors and the append operation.

Hint: Use `simp [(>>=)]` if you want to unfold the definition of the bind
operator. -/

lemma bind_nil {α β : Type} (f : α → list β) :
  ([] >>= f) = [] :=
sorry

lemma bind_cons {α β : Type} (f : α → list β) (a : α) (as : list α) :
  (list.cons a as >>= f) = f a ++ (as >>= f) :=
sorry

lemma bind_append {α β : Type} (f : α → list β) :
  ∀as as' : list α, ((as ++ as') >>= f) = (as >>= f) ++ (as' >>= f) :=
sorry

/-! 2.2 (3 points). Prove the three laws for `list`.

Hint: The simplifier cannot see through the type class definition of `pure`. You
can use `pure_eq_singleton` to unfold the definition or `show` to state the
lemma statement using `bind` and `[…]`. -/

lemma pure_bind {α β : Type} (a : α) (f : α → list β) :
  (pure a >>= f) = f a :=
sorry

lemma bind_pure {α : Type} :
  ∀as : list α, (as >>= pure) = as :=
sorry

lemma bind_assoc {α β γ : Type} (f : α → list β) (g : β → list γ) :
  ∀as : list α, ((as >>= f) >>= g) = (as >>= (λa, f a >>= g)) :=
sorry

/-! 2.3 (1 point). Prove the following `list`-specific law. -/

lemma bind_pure_comp_eq_map {α β : Type} {f : α → β} :
  ∀as : list α, (as >>= (pure ∘ f)) = list.map f as :=
sorry

end list

end LoVe
