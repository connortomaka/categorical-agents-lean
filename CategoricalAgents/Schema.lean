/-
  CategoricalAgents.Schema
  ------------------------
  Database schemas, Spivak-style. A schema instance is data with typed foreign
  keys. Foreign keys are FUNCTIONS, so referential integrity holds by
  construction and a foreign key is many-to-ONE. A many-to-MANY relation is
  reified as a junction table (a span) — the standard SQL bridge-table pattern,
  forced by the categorical structure. Migration is a structure-preserving map
  of instances; "internal cohesion" is the commuting squares, preserved under
  composition.
-/

namespace CategoricalAgents
namespace Schema

/-- An instance of a tiny org schema. `mgr : Emp → Emp` is the many-to-one
    self-relation (each employee has one manager). The many-to-many
    "works on" relation lives in the junction `Assign` via `Emp ← Assign → Proj`. -/
structure Org where
  Emp    : Type
  Proj   : Type
  Assign : Type
  name   : Emp → String
  mgr    : Emp → Emp
  aEmp   : Assign → Emp
  aProj  : Assign → Proj

/-- Many-to-many relation recovered from the junction. -/
def worksOn (O : Org) (e : O.Emp) (p : O.Proj) : Prop :=
  ∃ a : O.Assign, O.aEmp a = e ∧ O.aProj a = p

/- ---------- A concrete database ---------- -/

inductive Person | alice | bob | carol
inductive Proj2  | apollo | gemini
inductive Work2  | w1 | w2
open Person Proj2 Work2

/-- Alice is the top (her own manager); Bob reports to Alice, Carol to Bob.
    Bob works on Apollo, Carol on Gemini. -/
def acme : Org where
  Emp    := Person
  Proj   := Proj2
  Assign := Work2
  name   := fun p => match p with | alice => "Alice" | bob => "Bob" | carol => "Carol"
  mgr    := fun p => match p with | alice => alice | bob => alice | carol => bob
  aEmp   := fun w => match w with | w1 => bob | w2 => carol
  aProj  := fun w => match w with | w1 => apollo | w2 => gemini

-- Many-to-many facts, each witnessed by a junction row:
example : worksOn acme bob apollo   := ⟨w1, rfl, rfl⟩
example : worksOn acme carol gemini := ⟨w2, rfl, rfl⟩
-- Many-to-one facts:
example : acme.mgr carol = bob   := rfl   -- Carol reports to Bob
example : acme.mgr alice = alice := rfl   -- chain of command terminates

/- ---------- Migration: a cohesion-preserving map of databases ---------- -/

/-- A migration `S → T`: a function on every table that COMMUTES with every
    foreign key and attribute. Those squares are referential integrity carried
    across the translation. (A natural transformation between the instances.) -/
structure Migration (S T : Org) where
  emp    : S.Emp → T.Emp
  proj   : S.Proj → T.Proj
  assign : S.Assign → T.Assign
  mgr_comm   : ∀ e, emp (S.mgr e) = T.mgr (emp e)
  name_comm  : ∀ e, T.name (emp e) = S.name e
  aEmp_comm  : ∀ a, emp (S.aEmp a) = T.aEmp (assign a)
  aProj_comm : ∀ a, proj (S.aProj a) = T.aProj (assign a)

def Migration.id (O : Org) : Migration O O where
  emp := fun e => e ; proj := fun p => p ; assign := fun a => a
  mgr_comm := fun _ => rfl ; name_comm := fun _ => rfl
  aEmp_comm := fun _ => rfl ; aProj_comm := fun _ => rfl

/-- Migrations COMPOSE and cohesion is preserved through the chain. -/
def Migration.comp {S T U : Org} (f : Migration S T) (g : Migration T U) :
    Migration S U where
  emp := fun e => g.emp (f.emp e)
  proj := fun p => g.proj (f.proj p)
  assign := fun a => g.assign (f.assign a)
  mgr_comm := by intro e; show g.emp (f.emp (S.mgr e)) = U.mgr (g.emp (f.emp e)); rw [f.mgr_comm, g.mgr_comm]
  name_comm := by intro e; show U.name (g.emp (f.emp e)) = S.name e; rw [g.name_comm, f.name_comm]
  aEmp_comm := by intro a; show g.emp (f.emp (S.aEmp a)) = U.aEmp (g.assign (f.assign a)); rw [f.aEmp_comm, g.aEmp_comm]
  aProj_comm := by intro a; show g.proj (f.proj (S.aProj a)) = U.aProj (g.assign (f.assign a)); rw [f.aProj_comm, g.aProj_comm]

/- ---------- Translate Acme to ANOTHER database ---------- -/

inductive Id3 | e0 | e1 | e2
open Id3

/-- A second database keyed by ids instead of names, same relational structure. -/
def globex : Org where
  Emp    := Id3
  Proj   := Proj2
  Assign := Work2
  name   := fun e => match e with | e0 => "Alice" | e1 => "Bob" | e2 => "Carol"
  mgr    := fun e => match e with | e0 => e0 | e1 => e0 | e2 => e1
  aEmp   := fun w => match w with | w1 => e1 | w2 => e2
  aProj  := fun w => match w with | w1 => apollo | w2 => gemini

/-- The migration acme → globex: re-key employees to ids, keep the rest. Every
    cohesion square holds by computation — manager chain, names, and the
    many-to-many assignment links all transfer intact. -/
def acmeToGlobex : Migration acme globex where
  emp := fun p => match p with | alice => e0 | bob => e1 | carol => e2
  proj := fun p => p
  assign := fun a => a
  mgr_comm   := by intro e; cases e <;> rfl
  name_comm  := by intro e; cases e <;> rfl
  aEmp_comm  := by intro a; cases a <;> rfl
  aProj_comm := by intro a; cases a <;> rfl

end Schema
end CategoricalAgents
