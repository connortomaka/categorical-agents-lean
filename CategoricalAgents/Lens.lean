/-
  CategoricalAgents.Lens
  ----------------------
  Lenses are the canonical model of *bidirectional* interaction: a `view` that
  reads a focused part out of a whole, and an `update` that writes a new part
  back into the whole. Unidirectional pipelines (output of one agent feeds the
  next) cannot express "request information, receive a response, write a result
  back" — lenses can, and they compose lawfully.
-/

namespace CategoricalAgents

universe u

/-- A (monomorphic) lens between a source `S` and a focus `A`. -/
structure Lens (S A : Type u) where
  view   : S → A
  update : S → A → S

namespace Lens

/-- The three lens laws, as a `Prop`-valued predicate on a lens. -/
structure Lawful {S A : Type u} (l : Lens S A) : Prop where
  /-- Writing back what you just read changes nothing. -/
  get_put : ∀ s, l.update s (l.view s) = s
  /-- Reading after a write returns exactly what you wrote. -/
  put_get : ∀ s a, l.view (l.update s a) = a
  /-- A later write overwrites an earlier one. -/
  put_put : ∀ s a a', l.update (l.update s a) a' = l.update s a'

/-- The identity lens. It is lawful, definitionally. -/
def idLens (S : Type u) : Lens S S where
  view   := fun s => s
  update := fun _ s => s

theorem idLens_lawful (S : Type u) : Lawful (idLens S) where
  get_put := fun _ => rfl
  put_get := fun _ _ => rfl
  put_put := fun _ _ _ => rfl

/-- Lens composition: focus through `l : Lens S A`, then `m : Lens A B`. -/
def comp {S A B : Type u} (l : Lens S A) (m : Lens A B) : Lens S B where
  view   := fun s => m.view (l.view s)
  update := fun s b => l.update s (m.update (l.view s) b)

/-- Composition of lawful lenses is lawful. Each law of the composite is
    discharged purely by rewriting with the laws of the factors — no case
    analysis, no holes. This is the bidirectional analogue of "composition with
    contracts". -/
theorem comp_lawful {S A B : Type u} {l : Lens S A} {m : Lens A B}
    (hl : Lawful l) (hm : Lawful m) : Lawful (comp l m) where
  get_put := by
    intro s
    show l.update s (m.update (l.view s) (m.view (l.view s))) = s
    rw [hm.get_put, hl.get_put]
  put_get := by
    intro s b
    show m.view (l.view (l.update s (m.update (l.view s) b))) = b
    rw [hl.put_get, hm.put_get]
  put_put := by
    intro s b b'
    show l.update (l.update s (m.update (l.view s) b))
            (m.update (l.view (l.update s (m.update (l.view s) b))) b')
       = l.update s (m.update (l.view s) b')
    rw [hl.put_get, hm.put_put, hl.put_put]

end Lens

end CategoricalAgents
