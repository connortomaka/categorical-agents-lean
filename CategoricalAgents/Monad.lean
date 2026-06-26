/-
  CategoricalAgents.Monad
  -----------------------
  Computational monads, the standard way to give *effects* (failure, state,
  non-determinism, I/O, ...) a type-safe interface. We use the `bind`/`pure`
  ("Kleisli triple") presentation and prove the three monad laws for a concrete
  instance. Kleisli composition is then shown associative — which is exactly
  what makes *effectful* agents composable in `CategoricalAgents.Agents`.
-/

namespace CategoricalAgents

universe u

/-- A monad on the category of types, presented by `pure` and `bind`, with the
    three monad laws as fields. -/
structure KMonad where
  M    : Type u → Type u
  pure : {A : Type u} → A → M A
  bind : {A B : Type u} → M A → (A → M B) → M B
  bind_pure_left  : ∀ {A B : Type u} (a : A) (k : A → M B),
                      bind (pure a) k = k a
  bind_pure_right : ∀ {A : Type u} (m : M A), bind m pure = m
  bind_assoc      : ∀ {A B C : Type u} (m : M A) (k : A → M B) (l : B → M C),
                      bind (bind m k) l = bind m (fun a => bind (k a) l)

namespace KMonad

/-- The `Option` monad: an agent that may legitimately produce "no result".
    All three laws hold by case analysis. -/
def option : KMonad where
  M := Option
  pure := fun a => some a
  bind := fun m k => match m with
            | none   => none
            | some a => k a
  bind_pure_left  := fun _ _ => rfl
  bind_pure_right := fun m => by cases m <;> rfl
  bind_assoc      := fun m _ _ => by cases m <;> rfl

/-- Kleisli composition of effectful maps (`f` then `g`, diagrammatic order). -/
def kleisli (T : KMonad) {A B C : Type u}
    (f : A → T.M B) (g : B → T.M C) : A → T.M C :=
  fun a => T.bind (f a) g

/-- Kleisli composition is associative. This is the law that lets us build
    arbitrarily deep effectful agent pipelines without the composition order
    ever mattering. -/
theorem kleisli_assoc (T : KMonad) {A B C D : Type u}
    (f : A → T.M B) (g : B → T.M C) (h : C → T.M D) :
    T.kleisli (T.kleisli f g) h = T.kleisli f (T.kleisli g h) := by
  funext a
  show T.bind (T.bind (f a) g) h = T.bind (f a) (fun b => T.bind (g b) h)
  rw [T.bind_assoc]

end KMonad

end CategoricalAgents
