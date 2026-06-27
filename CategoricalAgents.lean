/-
  CategoricalAgents
  -----------------
  A small, self-contained, Mathlib-free formalisation in Lean 4 of the
  category-theoretic machinery behind *verifiable multi-agent orchestration*:
  categories, functors, natural transformations, containers, monads, lenses,
  and agents-as-morphisms with verified delegation.

  Importing this module pulls in the whole development.
-/
import CategoricalAgents.Basic
import CategoricalAgents.Examples
import CategoricalAgents.Containers
import CategoricalAgents.Monad
import CategoricalAgents.Lens
import CategoricalAgents.Agents
import CategoricalAgents.Delegation
import CategoricalAgents.Migration
