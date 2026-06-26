/-
  CategoricalAgents.Basic
  -----------------------
  Category theory from first principles, in pure Lean 4 (no Mathlib dependency).

  Design note on composition order:
  we write composition in DIAGRAMMATIC (left-to-right) order, so `comp f g`
  means "do `f`, then `g`". This matches how an engineer reads an agent
  pipeline `input → f → g → output`, and is the convention used throughout
  this project (see `CategoricalAgents.Agents`).
-/

namespace CategoricalAgents

universe u v

/-- A category: a collection of objects, a hom-set for each ordered pair of
    objects, identities, composition, and the three coherence laws. -/
structure Category where
  Obj  : Type u
  Hom  : Obj → Obj → Type v
  id   : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_comp  : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  comp_id  : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  assoc    : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
               comp (comp f g) h = comp f (comp g h)

/-- A (covariant) functor between two categories: an action on objects and on
    morphisms that preserves identities and composition. -/
structure Funct (C D : Category) where
  obj : C.Obj → D.Obj
  map : {X Y : C.Obj} → C.Hom X Y → D.Hom (obj X) (obj Y)
  map_id   : ∀ (X : C.Obj), map (C.id X) = D.id (obj X)
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
               map (C.comp f g) = D.comp (map f) (map g)

namespace Funct

/-- The identity functor on a category. -/
def idF (C : Category) : Funct C C where
  obj := fun X => X
  map := fun f => f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Composition of functors (`F` then `G`, diagrammatic order).
    The functor laws for the composite follow mechanically from the laws of
    each factor — this is "compositionality is correct by construction" in
    its smallest possible form. -/
def comp {C D E : Category} (F : Funct C D) (G : Funct D E) : Funct C E where
  obj := fun X => G.obj (F.obj X)
  map := fun f => G.map (F.map f)
  map_id := by
    intro X
    show G.map (F.map (C.id X)) = E.id (G.obj (F.obj X))
    rw [F.map_id, G.map_id]
  map_comp := by
    intro X Y Z f g
    show G.map (F.map (C.comp f g))
       = E.comp (G.map (F.map f)) (G.map (F.map g))
    rw [F.map_comp, G.map_comp]

end Funct

/-- A natural transformation `F ⟹ G` between parallel functors: a family of
    components together with the naturality square. -/
structure NatTrans {C D : Category} (F G : Funct C D) where
  app : (X : C.Obj) → D.Hom (F.obj X) (G.obj X)
  naturality : ∀ {X Y : C.Obj} (f : C.Hom X Y),
      D.comp (F.map f) (app Y) = D.comp (app X) (G.map f)

namespace NatTrans

/-- The identity natural transformation `F ⟹ F`. Naturality is exactly the
    statement that `id` is a two-sided unit for composition. -/
def idT {C D : Category} (F : Funct C D) : NatTrans F F where
  app := fun X => D.id (F.obj X)
  naturality := by
    intro X Y f
    show D.comp (F.map f) (D.id (F.obj Y)) = D.comp (D.id (F.obj X)) (F.map f)
    rw [D.comp_id, D.id_comp]

end NatTrans

end CategoricalAgents
