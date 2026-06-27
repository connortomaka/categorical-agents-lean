# Design Notes

Explanation on approach and why it was built the way it is: the
mathematical choices, how each construction maps onto the problem of
**verifiable multi-agent orchestration**, and where the ideas come from in the
literature. The code in `CategoricalAgents/` is the formal artifact; this is the
prose that motivates it.

The guiding idea is the one made precise by the **Curry–Howard–Lambek
correspondence**: *programs*, *proofs*, and *morphisms in a category* are three
views of the same thing. If an agent is a typed morphism, then wiring agents
together is composing morphisms, and checking that a wiring is valid is checking
a proof. "Deploying a system" and "proving a theorem" become the same act, per the Kodamai white paper — so a
type checker that accepts the program *is* the theorem prover that certifies the
system. Everything below is an attempt to make that literal in Lean.

---

## Why pure Lean 4, w/o Mathlib

Mathlib already contains a vast, battle-tested `CategoryTheory` library. Building
on it would be the right call for research. This repo deliberately does **not**,
for three reasons:

1. **First-principles legibility.** The point here is to show
   that I can *state and prove* the laws, not import them. Every
   structure here (`Category`, `Funct`, `NatTrans`, `Container`, `KMonad`,
   `Lens`, `Agent`) carries its laws as explicit fields, and every law is
   discharged by a proof you can read in a few lines.
2. **Self-containment and build speed.** No dependency resolution, no Mathlib
   compile, no version drift. `lake build` checks the whole thing from nothing
   but the pinned toolchain, which keeps CI fast and reproducible. This was as
   primary and desirable as point 1's legibility assertion.

The cost is that the constructions are intentionally minimal (monomorphic
lenses, a hand-rolled `Option` monad, `Type`-valued categories). The design
favours *complete proofs of small things* over *sketches of big things*.

## A note on composition order

Throughout, composition is written in **diagrammatic / left-to-right** order:
`comp f g` means "do `f`, then `g`", and the agent pipeline operator `a >=> b`
reads "run `a`, then `b`". This is the opposite of the classical `g ∘ f`
convention but matches how an engineer reads a dataflow `input → f → g → output`.
Keeping one order everywhere is what lets `Agent.seq` reuse the category laws
without a flurry of `flip`s.

---

## The concept → construct map

The whitepaper names a set of mathematical pillars. Each one is realised by a
specific module here. The table is the spine of the project.

| Whitepaper concept | Construct in this repo | File |
|---|---|---|
| Compositionality; "morphisms and their composition" | `Category` with `id_comp`, `comp_id`, `assoc` | `Basic.lean` |
| Functors as the abstraction that "unifies diverse concepts" | `Funct`, `Funct.idF`, `Funct.comp` | `Basic.lean` |
| Natural transformations | `NatTrans`, `NatTrans.idT` | `Basic.lean` |
| Containers (Ghani et al.) as the basis of the Agentic Type System | `Container`, `Ext`, `Hom`, `Hom.trans` | `Containers.lean` |
| Computational monads for effects (state, I/O, failure, non-determinism) | `KMonad`, `KMonad.option`, `kleisli` | `Monad.lean` |
| Bidirectional flow ("request information, receive responses, write back") | `Lens`, `Lens.comp`, lens laws | `Lens.lean` |
| Agents as typed morphisms; correctness by construction | `Agent`, `seq`, `>=>` | `Agents.lean` |
| Verified delegation & amalgamation (Manager Agent) | `delegate`, `delegate_spec` | `Agents.lean` |
| Effectful agents that still compose lawfully | `Eff`, `Eff.seq`, `Eff.seq_assoc` | `Agents.lean` |
| Curry–Howard–Lambek / theorem-prover correspondence | the fact that all of the above is checked by `lake build` | everywhere |

### Categories, functors, naturality (`Basic.lean`)

`Category` is the minimal interface: objects, hom-types, identities,
composition, and the three coherence laws as proof obligations. `Funct.comp`'s
`map_id`/`map_comp` proofs are the smallest possible demonstration of
"compositionality is correct by construction": the laws of a composite functor
are *forced* by the laws of its factors, with no freedom to get it wrong. That is
exactly the property the whitepaper claims scales to 10,000 agents — here it is
in its irreducible form.

### Containers (`Containers.lean`)

Containers are the conceptual heart, and the reason is biographical as much as
mathematical: containers are Neil Ghani's invention, and the whitepaper names
them as the foundation of the Agentic Type System. A container `Shape ◁ Pos`
presents a strictly-positive (polynomial) functor as "a set of shapes, and for
each shape a set of positions to fill with data."

The agent reading: an agent's **interface** is a container. The *shape* is which
kind of request/response the agent can emit; the *positions* are the typed holes
that must be filled to complete it. A **container morphism** (`Hom`) is then a
type-safe way to implement one interface in terms of another. Crucially its
action on positions is **contravariant** — to supply a `D`-shaped response you
must say where each of its holes is sourced from the `C`-side. That
contravariance is the formal content of "composition *with contracts*" rather
than "data piped forward", and `Hom.trans_natural` proves the induced data
transformation never silently alters the payload.

### Monads (`Monad.lean`)

Real agents fail, branch, read state, call out to the world. The standard
type-theoretic account of such effects is the **computational monad** (Moggi).
`KMonad` carries the Kleisli-triple presentation (`pure`, `bind`, three laws);
`KMonad.option` is a worked instance modelling "this agent may legitimately
return no result." The single exported theorem that matters downstream is
`kleisli_assoc`: Kleisli composition is associative. That is the law that lets
effectful pipelines of any depth be reparenthesised freely.

### Lenses (`Lens.lean`)

The whitepaper is explicit that business logic is **bidirectional**, and that
unidirectional pipelines are one of the three failure modes of naive LLM
orchestration. Lenses are the canonical bidirectional structure: a `view` that
reads a focus out of a whole and an `update` that writes one back, subject to the
three well-behaved-lens laws (`get_put`, `put_get`, `put_put`). Lenses too are
part of Ghani's and Smithe's compositional-systems work. `comp_lawful` proves the
payoff: the composite of two lawful lenses is lawful, each law discharged purely
by rewriting with the factors' laws — bidirectional composition with contracts.

### Agents (`Agents.lean`)

This is where the pieces become the thing the whitepaper is about.

* `Agent I O` is a typed morphism `I → O`; by Curry–Howard–Lambek, constructing
  one is *proving* "from an `I` we can obtain an `O`." `seq` / `>=>` is
  composition, and `idA_seq`, `seq_idA`, `seq_assoc` are the category laws — so
  agents literally form a category and pipelines are correct by construction.
* `delegate` is the **Manager Agent**: decompose an input into independent
  sub-problems, hand them to specialist agents, amalgamate the typed results.
  The combinator only *type-checks* when each specialist's interface lines up
  with the decomposition and the merge — so a well-typed manager **cannot** route
  data to an incompatible specialist. `delegate_spec` proves its behaviour is
  exactly decompose → delegate → amalgamate, with no hidden state and no
  cross-talk. That is "verified delegation and amalgamation" in miniature.
* `Eff` lifts agents over an arbitrary `KMonad`, and `Eff.seq_assoc` shows
  effectful pipelines inherit associativity directly from `kleisli_assoc` — the
  effect story is reused for free, which is the whole point of doing it
  categorically.

---

## How the theorem-prover correspondence is *literal* here

The Kodamai whitepaper's  claim is that "deploying an agent system is equivalent
to proving the theorem of its correctness." In this repo that is:

* An agent is a term whose type is its specification.
* Composing agents builds a larger term whose type is the composite spec.
* `lake build` runs Lean's kernel, which accepts the term **iff** it
  type-checks — i.e. iff the corresponding theorem holds.
* The GitHub Actions workflow runs `lake build` on every push. A green check is
  therefore a machine-verified proof that every construction and every law in the
  development is correct.

So the CI badge is, quite precisely, the "theorem prover" certifying the
"system." That is the single idea the repo is built to demonstrate.

---

## Deliberate limitations (and the honest next steps)

These are scoped out on purpose; listing them is part of the design.

* **Monomorphic lenses.** `Lens S A` does not allow the focus type to change on
  update. Polymorphic (type-changing) lenses `Lens S T A B` are the natural
  generalisation.
* **`Type`-valued categories.** `Category.Obj : Type u` with `Hom` in `Type v`.
  No enriched or higher-categorical structure.
* **One concrete monad.** Only `Option` is instantiated; `State` and `Reader`
  would exercise `KMonad` more thoroughly.
* **Container extension not packaged as a `Funct`.** `Ext`/`map`/`map_id`/
  `map_comp` prove functoriality, but the bundling of `Ext` as a
  `Funct TypeCat TypeCat` is left as the obvious next construction.
* **No vertical/horizontal `NatTrans` composition.** Only identities are built.

None of these affect the proofs that *are* present; they are extensions, not
patches. Confirm correctness here, second pair of eyes preferance here.

---

## References

The constructions are standard; these are the sources behind them.

- Avigad, J., & Massot, P. (2026). Mathematics in Lean (Release v4.19.0).
  Lean community. https://leanprover-community.github.io/mathematics_in_lean/
- M. Abbott, T. Altenkirch, N. Ghani — *Containers: Constructing Strictly
  Positive Types* (TCS, 2005). The container model used in `Containers.lean`.
- E. Moggi — *Notions of Computation and Monads* (Information and Computation,
  1991). The computational-monad account of effects behind `Monad.lean`.
- J. Lambek & P. Scott — *Introduction to Higher Order Categorical Logic* (1986).
  The Curry–Howard–Lambek correspondence the whole design leans on.
- S. Mac Lane — *Categories for the Working Mathematician* (2nd ed., 1998). The
  category/functor/natural-transformation laws in `Basic.lean`.
- J. Gibbons & M. Johnson, and the Statebox/applied-category-theory line of work
  on lenses and bidirectional transformations behind `Lens.lean`.
- The Lean 4 / Mathlib `CategoryTheory` library — the reference implementation
  this repo intentionally rebuilds from scratch for legibility.

## Provenance

This is an independent educational portfolio project. It uses only publicly
available mathematics and contains no proprietary, internal, or confidential
material from any company. Any resemblance to a commercial platform is at the
level of shared, published mathematical ideas only.
