/-
  CategoricalAgents.Agents
  ------------------------
 Attempt to model agents as typed morphisms and assemble them with
  combinators whose correctness is guaranteed by the type checker:

    * a pure agent `Agent I O` is a morphism of `TypeCat` — and, by
      Curry-Howard-Lambek, a *proof* that an `O` can be produced from an `I`;
    * sequential composition is associative and unital (the category laws);
    * a "manager" agent decomposes a task, delegates to specialists and
      amalgamates the results — and is correct by construction;
    * effectful agents over any monad compose lawfully via Kleisli composition.
-/
import CategoricalAgents.Basic
import CategoricalAgents.Monad

namespace CategoricalAgents

universe u

/-- A pure agent with typed input interface `I` and output interface `O`.
    These are precisely the morphisms of `TypeCat`; the wrapper just gives them
    a name and pipeline combinators. -/
structure Agent (I O : Type u) where
  run : I → O

namespace Agent

/-- The pass-through (identity) agent. -/
def idA (I : Type u) : Agent I I := ⟨fun i => i⟩

/-- Sequential composition: run `a`, feed its output to `b`. -/
def seq {I M O : Type u} (a : Agent I M) (b : Agent M O) : Agent I O :=
  ⟨fun i => b.run (a.run i)⟩

-- Pipeline operator: `a >=> b` runs `a`, then `b`.
infixr:60 " >=> " => seq

/-- Identity is a left unit for the pipeline. -/
theorem idA_seq {I O : Type u} (a : Agent I O) : idA I >=> a = a := rfl
/-- Identity is a right unit for the pipeline. -/
theorem seq_idA {I O : Type u} (a : Agent I O) : a >=> idA O = a := rfl
/-- Pipelines are associative: how you parenthesise a chain is irrelevant. -/
theorem seq_assoc {I A B O : Type u}
    (a : Agent I A) (b : Agent A B) (c : Agent B O) :
    (a >=> b) >=> c = a >=> (b >=> c) := rfl

/-- Curry-Howard-Lambek in miniature: *constructing* a value of type
    `Agent P R` is the same act as *proving* "from a `P` we can obtain an `R`".
    The pipeline below is simultaneously a program and a (constructive) proof. -/
example {P Q R : Type u} (pq : Agent P Q) (qr : Agent Q R) : Agent P R :=
  pq >=> qr

/-- A *manager* agent: decompose an `I` into two independent sub-problems,
    delegate them to specialist agents `left` and `right`, then amalgamate the
    typed results with `merge`. The combinator only type-checks when each
    specialist's interface lines up with the decomposition and the
    amalgamation — so a well-typed manager *cannot* route data to an
    incompatible specialist. That is correctness by construction. -/
def delegate {I A B A' B' O : Type u}
    (split : I → A × B)
    (left  : Agent A A')
    (right : Agent B B')
    (merge : A' × B' → O) : Agent I O :=
  ⟨fun i => merge (left.run (split i).1, right.run (split i).2)⟩

/-- Specification of the manager: its behaviour is exactly
    decompose → delegate → amalgamate, with no hidden state and no cross-talk
    between specialists. The proof is `rfl`: the implementation *is* the spec. -/
theorem delegate_spec {I A B A' B' O : Type u}
    (split : I → A × B) (left : Agent A A') (right : Agent B B')
    (merge : A' × B' → O) (i : I) :
    (delegate split left right merge).run i
      = merge (left.run (split i).1, right.run (split i).2) := rfl

/-- An *effectful* agent over a monad `T`: it may fail, branch, read state,
    etc., yet still composes lawfully. -/
structure Eff (T : KMonad) (I O : Type u) where
  run : I → T.M O

/-- Sequential composition of effectful agents, via Kleisli composition. -/
def Eff.seq {T : KMonad} {I M O : Type u}
    (a : Eff T I M) (b : Eff T M O) : Eff T I O :=
  ⟨T.kleisli a.run b.run⟩

/-- Effectful pipelines are associative — inherited directly from associativity
    of Kleisli composition (`CategoricalAgents.Monad`). The whole effect story
    is reused for free. -/
theorem Eff.seq_assoc {T : KMonad} {I A B O : Type u}
    (a : Eff T I A) (b : Eff T A B) (c : Eff T B O) :
    Eff.seq (Eff.seq a b) c = Eff.seq a (Eff.seq b c) := by
  show (⟨T.kleisli (T.kleisli a.run b.run) c.run⟩ : Eff T I O)
     = ⟨T.kleisli a.run (T.kleisli b.run c.run)⟩
  rw [T.kleisli_assoc]

end Agent

end CategoricalAgents
