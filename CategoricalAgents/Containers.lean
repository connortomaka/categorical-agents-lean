/-
  CategoricalAgents.Containers
  ----------------------------
  Containers, in the sense of Abbott, Altenkirch and Ghani, present the
  strictly-positive (polynomial) functors as a pair `Shape ◁ Pos`: a set of
  shapes, and for each shape a set of positions to be filled with data.

  Why this module is the conceptual heart of the project: an agent's *interface*
  is naturally a container. The shape is "which kind of request/response this
  agent can emit", and the positions are "the typed holes that must be filled
  to complete it". Container morphisms are then exactly the type-safe ways one
  agent interface can be implemented in terms of another, and they induce
  natural transformations on the data — composition with contracts, by
  construction.
-/

namespace CategoricalAgents

universe u v w

/-- A container: a type of shapes, and for each shape a type of positions. -/
structure Container where
  Shape : Type u
  Pos   : Shape → Type v

namespace Container

/-- The extension of a container as a functor on types:
    `⟦S ◁ P⟧ X = Σ s : Shape, (Pos s → X)`.
    An element is "a shape, together with an `X` at every position". -/
def Ext (C : Container) (X : Type w) : Type (max (max u v) w) :=
  Σ s : C.Shape, C.Pos s → X

/-- Functorial action of the extension on a morphism: relabel the data at every
    position, leaving the shape untouched. -/
def map (C : Container) {X Y : Type w} (f : X → Y) : C.Ext X → C.Ext Y :=
  fun p => ⟨p.1, fun i => f (p.2 i)⟩

/-- The extension preserves identities. -/
theorem map_id (C : Container) {X : Type w} :
    C.map (fun x : X => x) = (fun e : C.Ext X => e) := by
  funext p
  rfl

/-- The extension preserves composition (`f` then `g`). -/
theorem map_comp (C : Container) {X Y Z : Type w} (f : X → Y) (g : Y → Z) :
    C.map (fun x => g (f x)) = (fun e => C.map g (C.map f e)) := by
  funext p
  rfl

/-- A morphism of containers `(S ◁ P) ⇒ (T ◁ Q)`: a map on shapes, together
    with a *contravariant* map on positions. This contravariance is the formal
    reason agent interfaces compose with contracts rather than just piping
    data forward. -/
structure Hom (C D : Container) where
  shape : C.Shape → D.Shape
  pos   : (s : C.Shape) → D.Pos (shape s) → C.Pos s

/-- A container morphism induces a polymorphic transformation of extensions. -/
def Hom.trans {C D : Container} (α : Hom C D) {X : Type w} :
    C.Ext X → D.Ext X :=
  fun p => ⟨α.shape p.1, fun i => p.2 (α.pos p.1 i)⟩

/-- ...and that transformation is natural: relabelling data and applying the
    morphism commute. A typed reshaping of an agent interface can never
    silently change the data flowing through it. -/
theorem Hom.trans_natural {C D : Container} (α : Hom C D)
    {X Y : Type w} (f : X → Y) (p : C.Ext X) :
    α.trans (C.map f p) = D.map f (α.trans p) := rfl

end Container

end CategoricalAgents
