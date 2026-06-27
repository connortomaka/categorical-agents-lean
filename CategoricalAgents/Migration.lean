/-
  CategoricalAgents.Migration
  ---------------------------
  A small data-migration / integration application. Two source schemas (from
  two "collaborating groups") are AMALGAMATED into one unified schema; a
  validating variant fails closed on inconsistent keys; and a correction lens
  gives a verified bidirectional round-trip on the migrated data.
-/
import CategoricalAgents.Agents
import CategoricalAgents.Lens

namespace CategoricalAgents
namespace Migration

open Agent
open Lens

/- ---------- Schemas ---------- -/

/-- Source A: a clinical record from one group. -/
structure Clinical where
  pid      : Nat
  ageYears : Nat

/-- Source B: a sequencing record from another group. -/
structure Sequencing where
  pid   : Nat
  reads : Nat

/-- Target: the unified schema after migration. -/
structure Unified where
  pid      : Nat
  ageYears : Nat
  reads    : Nat

/- ---------- Amalgamation (the integration step) ---------- -/

def normClinical : Agent Clinical (Nat × Nat) := ⟨fun c => (c.pid, c.ageYears)⟩
def normSeq      : Agent Sequencing Nat        := ⟨fun s => s.reads⟩

/-- Decompose the paired sources, normalise each specialist's record, then
    AMALGAMATE into the unified schema. This is `delegate` applied to data
    integration: a well-typed merge cannot route a clinical field into a
    sequencing slot. -/
def integrate : Agent (Clinical × Sequencing) Unified :=
  delegate (fun p => p) normClinical normSeq
    (fun ((pid, age), reads) => ⟨pid, age, reads⟩)

/-- Run the migration on a record pair. -/
example : integrate.run (⟨1, 30⟩, ⟨1, 500⟩) = ⟨1, 30, 500⟩ := rfl

/-- Behavioural spec for ALL inputs. -/
theorem integrate_spec (c : Clinical) (s : Sequencing) :
    integrate.run (c, s) = ⟨c.pid, c.ageYears, s.reads⟩ := rfl

/- ---------- Effectful migration: validate keys, fail closed ---------- -/

/-- Migrate only if the two sources agree on the patient id; otherwise fail —
    no silently mismatched merge written to the target. -/
def safeIntegrate : Eff KMonad.option (Clinical × Sequencing) Unified :=
  ⟨fun (c, s) =>
    if c.pid = s.pid then some ⟨c.pid, c.ageYears, s.reads⟩ else none⟩

/-- Keys agree → migrated record. -/
example : safeIntegrate.run (⟨1, 30⟩, ⟨1, 500⟩) = some ⟨1, 30, 500⟩ := rfl

/-- Keys disagree → migration fails, nothing written. -/
example : safeIntegrate.run (⟨1, 30⟩, ⟨2, 500⟩) = none := rfl

/- ---------- Bidirectional correction: a lawful lens into the target ---------- -/

/-- A lens onto the `reads` field of a migrated record: read it, or correct it
    while preserving the rest. -/
def readsLens : Lens Unified Nat where
  view   := fun u => u.reads
  update := fun u r => { u with reads := r }

theorem readsLens_lawful : Lawful readsLens where
  get_put := by intro u; cases u; rfl
  put_get := by intro u r; rfl
  put_put := by intro u r r'; rfl

/-- The migration didn't lose round-trippability: correct a field, read back
    exactly what you wrote. Derived from the lens law, not re-proven. -/
theorem reads_roundtrip (u : Unified) (r : Nat) :
    readsLens.view (readsLens.update u r) = r :=
  readsLens_lawful.put_get u r

/-- Correcting then re-correcting keeps only the latest value (no drift). -/
theorem reads_no_drift (u : Unified) (r r' : Nat) :
    readsLens.update (readsLens.update u r) r' = readsLens.update u r' :=
  readsLens_lawful.put_put u r r'

end Migration
end CategoricalAgents
