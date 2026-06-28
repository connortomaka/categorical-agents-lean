# Categorical Agents (Lean 4)

A small, **self-contained, Mathlib-free** formalisation of the category-theoretic
foundations behind *verifiable multi-agent orchestration* — built in
[Lean 4](https://leanprover.github.io/) as a proof-checked toy project.

The thesis it makes concrete: the difference between an agent pipeline that
"usually works" and one that is **correct by construction** is not more compute —
it is a type system with categorical structure. When agent interfaces are
typed and composition is governed by category/functor/monad laws, an
ill-formed orchestration simply fails to type-check, and a well-formed one
carries a machine-checkable proof of its own coherence.

Everything here is checked by Lean's kernel. There are **no `sorry`s** and **no
axioms beyond Lean's core** — if `lake build` succeeds, every theorem in this
repository has been verified.

---

## Build & verify

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager). The exact compiler version is pinned in [`lean-toolchain`](./lean-toolchain).

```bash
git clone <this-repo-url>
cd categorical-agents-lean
lake build          # type-checks (i.e. proof-checks) the entire library
```

A successful build *is* the verification: Lean only accepts the library if
every definition is well-typed and every theorem's proof is complete. The
included [GitHub Actions workflow](./.github/workflows/ci.yml) runs exactly this
on every push, so a green check mark on the repo is a machine-verified proof
that the development is correct.

> **Note on the toolchain pin.** `lean-toolchain` targets `v4.15.0`. The code
> uses only stable core Lean features (structures, `rfl`, `rw`, `simp only`,
> `funext`, `cases`) with no external dependencies, so bumping the pin to a
> newer release should be a one-line change if needed.

---

## What's inside

| Module | Contents |
| --- | --- |
| [`Basic`](./CategoricalAgents/Basic.lean) | `Category`, `Funct` (functor) and `NatTrans` from first principles, with the identity/composite functors and the identity natural transformation, all laws proven. |
| [`Examples`](./CategoricalAgents/Examples.lean) | The category of Lean types & functions (`TypeCat`), the constant functor, and computational sanity checks. |
| [`Containers`](./CategoricalAgents/Containers.lean) | Containers (`Shape ◁ Pos`), their extension as a functor, container morphisms, and a proof that each induces a **natural** transformation. |
| [`Monad`](./CategoricalAgents/Monad.lean) | Monads in `bind`/`pure` form, the `Option` monad with all three laws proven, and **associativity of Kleisli composition**. |
| [`Lens`](./CategoricalAgents/Lens.lean) | Lenses (bidirectional `view`/`update`), the three lens laws, and a proof that **lawful lenses compose to a lawful lens**. |
| [`Agents`](./CategoricalAgents/Agents.lean) | Agents as typed morphisms; associative/unital pipelines; **verified delegation** (decompose → delegate → amalgamate, correct by construction); effectful agents over any monad. |
| [`Delegation`](./CategoricalAgents/Delegation.lean) | Delegation & amalgamation **run on concrete data**; the Kleisli identity laws (completing "effectful agents form a category"); and **effectful, fail-closed amalgamation** — if any specialist's effect fails, the whole manager fails, with no partial result. |
| [`Migration`](./CategoricalAgents/Migration.lean) | A small **data-integration / migration** application: two source schemas amalgamated into one, a validating variant that **fails closed** on inconsistent keys, and a lawful correction lens giving a verified bidirectional round-trip. |
| [`Schema`](./CategoricalAgents/Schema.lean) | **Spivak-style schemas as categories**: foreign keys as functions (referential integrity by construction), many-to-many relations reified as **junction spans**, and **cohesion-preserving migrations** whose commuting squares are proof obligations — composed into a multi-stage pipeline verified end-to-end by construction. |

Read top-to-bottom, the modules go: *the mathematics of composition* →
*concrete categories* → *interfaces as containers* → *effects as monads* →
*bidirectionality as lenses* → *agents that compose with proofs* →
*delegation & amalgamation, run and verified* → *data integration and
Spivak-style schema migration, cohesion preserved by construction*.

For the design rationale — why pure Lean with no Mathlib, the full
concept-to-construct mapping, and references — see
[`docs/DESIGN.md`](./docs/DESIGN.md).

---

## How the pieces map to verified agent orchestration

This project deliberately formalises the **public, well-established
mathematics** that a correctness-by-construction agent platform rests on. Each
construct earns its place:

- **Composition with contracts.** A category's morphisms compose only when
  their (co)domains line up, and the laws (`id_comp`, `comp_id`, `assoc`) make
  that composition coherent. Agents modelled as morphisms inherit this: a
  pipeline that type-checks is a pipeline whose interfaces are guaranteed
  compatible. See `Agent.seq` and the `>=>` operator.

- **Interfaces as containers.** An agent's request/response interface is
  naturally a *container*: a set of *shapes* (which messages it can emit) and,
  per shape, a set of *positions* (the typed holes to fill). Container
  morphisms — covariant on shapes, **contravariant on positions** — are exactly
  the type-safe re-implementations of one interface in terms of another, and
  `Hom.trans_natural` proves they never silently alter the data.

- **Effects, safely.** Real agents fail, branch, and carry state. Modelling
  those as a monad keeps them inside a typed framework; `KMonad.kleisli_assoc`
  shows effectful pipelines stay associative, so depth of delegation never
  breaks composition.

- **Bidirectional flow.** "Produce output, pass it forward" is unidirectional.
  Genuine delegation requires asking, receiving, and writing a result back —
  the shape of a *lens*. `Lens.comp_lawful` shows the bidirectional contract is
  preserved under composition.

- **Verified delegation & amalgamation.** A manager agent that splits a task,
  delegates to specialists, and recombines results is `Agent.delegate`. It only
  type-checks when every specialist's interface matches the decomposition, and
  `delegate_spec` proves the implementation *is* its specification. `Delegation`
  runs this on concrete data and extends it to **fail-closed** effectful
  amalgamation: if one specialist fails, the whole manager fails with no partial
  output.

- **Data migration with preserved cohesion.** Database schemas are categories,
  instances are data with typed foreign keys, and a migration is a typed
  morphism whose commuting squares (referential integrity) are *constructor
  obligations* — so a migration that loses cohesion cannot be built, and
  `Migration.comp` re-derives those proofs for a pipeline. Many-to-many
  relations become **junction spans** (foreign keys are functions, hence
  many-to-one; a span recovers many-to-many). This is the functorial-data-
  migration idea (Spivak / CQL) recast in a **pre-hoc, proof-carrying**
  verification stance: cohesion is verified *by construction*, not checked
  afterward. See `Schema.lean`.

- **Programs as proofs (Curry–Howard–Lambek).** A value of type `Agent I O` is
  literally a constructive proof that an `O` can be produced from an `I`.
  Building a valid orchestration and proving a theorem are the same act — the
  guiding idea behind theorem-prover-style verification of agent systems.

---

## References

- E. Riehl, *Category Theory in Context* (2016) — and its
  [Lean companion](https://github.com/rkirov/category-theory-in-context-lean).
- M. Abbott, T. Altenkirch, N. Ghani, *Containers: constructing strictly
  positive types*, TCS (2005).
- D. I. Spivak, *Functorial Data Migration*, arXiv:1503.03571 (2015), and the
  [CQL](https://github.com/CategoricalData/CQL) reference implementation
  (Conexus AI).
- The Curry–Howard–Lambek correspondence (logic ↔ type theory ↔ cartesian
  closed categories).
- [Mathlib4 `CategoryTheory`](https://github.com/leanprover-community/mathlib4) —
  the production-grade Lean library this project's definitions parallel.

---

## Scope, status & disclaimer

This is an **independent, educational portfolio project**. It is not affiliated
with, and contains no proprietary or confidential material from, any company;
it formalises only public mathematics. Universe handling is kept deliberately
simple (functors are taken between categories at a shared universe level, etc.),
which is enough for the constructions here but is not the full generality of a
production library like Mathlib.

The applied modules formalise the **faithful core** of each idea rather than its
full theory: monomorphic (not polymorphic) lenses; forward, fail-closed effects
(not full open games / optics with residuals); and the cohesion-preserving
**instance-and-migration layer** of functorial data migration (not the full
`Σ ⊣ Δ ⊣ Π` Kan-extension calculus). Natural next steps would be
vertical/horizontal composition of natural transformations, the State and Reader
monads, polymorphic (`get`/`put` of differing types) lenses, packaging container
extensions as first-class `Funct TypeCat TypeCat` values, and the `Σ`/`Π`
migration functors as left/right Kan extensions.
