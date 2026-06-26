/-
  CategoricalAgents.Examples
  --------------------------
  Concrete instances of the abstract structures from `Basic`: the category of
  Lean types and functions, the constant functor, and a couple of computational
  sanity checks that the definitions really do what they should.
-/
import CategoricalAgents.Basic

namespace CategoricalAgents

universe u

/-- The category `Type` whose objects are Lean types and whose morphisms are
    total functions. All three category laws hold definitionally (`rfl`),
    because function composition and the identity function already satisfy
    them by computation. -/
def TypeCat : Category where
  Obj := Type u
  Hom := fun A B => A → B
  id := fun _ => fun a => a
  comp := fun f g => fun a => g (f a)
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-- The constant functor at a fixed object `d`. Every morphism is sent to the
    identity on `d`; the functor laws reduce to the unit law for `id`. -/
def constF (C D : Category) (d : D.Obj) : Funct C D where
  obj := fun _ => d
  map := fun _ => D.id d
  map_id := fun _ => rfl
  map_comp := by
    intro X Y Z f g
    show D.id d = D.comp (D.id d) (D.id d)
    rw [D.id_comp]

/-- Sanity check: composition in `TypeCat` is ordinary function composition
    read left-to-right. `(+1)` then `(*2)` applied to `3` gives `8`. -/
example : (TypeCat.comp (fun (n : Nat) => n + 1) (fun n => n * 2)) 3 = 8 := rfl

/-- Sanity check: the identity functor really is the identity on morphisms. -/
example {C : Category} {X Y : C.Obj} (f : C.Hom X Y) :
    (Funct.idF C).map f = f := rfl

end CategoricalAgents
