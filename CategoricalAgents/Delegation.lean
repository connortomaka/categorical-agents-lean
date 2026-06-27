/-
  CategoricalAgents.Delegation
  ----------------------------
  Worked delegation & amalgamation: a manager decomposes a task, delegates to
  specialists, and amalgamates the typed results — run on real data, then the
  laws governing it, then the effectful (may-fail) case.
-/
import CategoricalAgents.Agents

namespace CategoricalAgents
namespace Delegation

open Agent

universe u

/- ========== Pure delegation & amalgamation ========== -/

def doubler : Agent Nat Nat := ⟨fun n => n * 2⟩
def addTen  : Agent Nat Nat := ⟨fun n => n + 10⟩

/-- Split a pair, double the left, add ten to the right, sum the results. -/
def manager : Agent (Nat × Nat) Nat :=
  delegate (fun p => p) doubler addTen (fun (a, b) => a + b)

/-- Run it: (5·2) + (3+10) = 23. -/
example : manager.run (5, 3) = 23 := rfl

/-- Behavioural spec for ALL inputs: no hidden state, no cross-talk. -/
theorem manager_spec (i : Nat × Nat) :
    manager.run i = doubler.run i.1 + addTen.run i.2 := rfl

/- ========== Delegation laws ========== -/

/-- Delegating to identity specialists collapses to "split, then merge". -/
theorem delegate_id {I A B O : Type u}
    (split : I → A × B) (merge : A × B → O) (i : I) :
    (delegate split (idA A) (idA B) merge).run i = merge (split i) := rfl

/-- Post-composing a manager with `k` fuses `k` into the amalgamation step —
    no extra pass over the data. -/
theorem delegate_seq {I A B A' B' O P : Type u}
    (split : I → A × B) (l : Agent A A') (r : Agent B B')
    (merge : A' × B' → O) (k : Agent O P) :
    (delegate split l r merge) >=> k
      = delegate split l r (fun ab => k.run (merge ab)) := rfl

/- ========== Nested: a manager whose specialist is itself a manager ========== -/

def bossManager : Agent ((Nat × Nat) × Nat) Nat :=
  delegate (fun p => p) manager (idA Nat) (fun (a, b) => a * b)

/-- (5·2 + 3+10) · 4 = 23 · 4 = 92. Delegation composes. -/
example : bossManager.run ((5, 3), 4) = 92 := rfl

/- ========== Harder: the Kleisli identity laws ========== -/
-- With the already-proven `kleisli_assoc`, these finish the proof that
-- effectful agents form a category: `pure` is a two-sided unit.

theorem kleisli_pure_left {T : KMonad} {A B : Type u} (g : A → T.M B) :
    T.kleisli T.pure g = g := by
  funext a
  show T.bind (T.pure a) g = g a
  rw [T.bind_pure_left]

theorem kleisli_pure_right {T : KMonad} {A B : Type u} (f : A → T.M B) :
    T.kleisli f T.pure = f := by
  funext a
  show T.bind (f a) T.pure = f a
  rw [T.bind_pure_right]

/- ========== Effectful delegation: amalgamation that can fail ========== -/

/-- A manager over any monad `T`: run both specialists, amalgamate — but if
    either specialist's effect fails/branches, the whole manager inherits it. -/
def effDelegate {T : KMonad} {I A B A' B' O : Type u}
    (split : I → A × B) (left : Eff T A A') (right : Eff T B B')
    (merge : A' × B' → O) : Eff T I O :=
  ⟨fun i => T.bind (left.run (split i).1) (fun a' =>
            T.bind (right.run (split i).2) (fun b' =>
              T.pure (merge (a', b'))))⟩

def leftE  : Eff KMonad.option Nat Nat := ⟨fun n => some (n * 2)⟩
def rightE : Eff KMonad.option Nat Nat :=
  ⟨fun n => match n with | 0 => none | _ => some (n + 10)⟩

def effManager : Eff KMonad.option (Nat × Nat) Nat :=
  effDelegate (fun p => p) leftE rightE (fun (a, b) => a + b)

/-- Both specialists succeed → amalgamated result. -/
example : effManager.run (5, 3) = some 23 := rfl

/-- Right specialist fails on 0 → the whole manager fails. No partial output. -/
example : effManager.run (5, 0) = none := rfl

/-- Effectful pipelines reparenthesise freely — reusing the proven kleisli_assoc. -/
example : Eff.seq (Eff.seq leftE leftE) leftE
        = Eff.seq leftE (Eff.seq leftE leftE) :=
  Eff.seq_assoc leftE leftE leftE

end Delegation
end CategoricalAgents
