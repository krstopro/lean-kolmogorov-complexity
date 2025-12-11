import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Order.WithBot
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import KolmogorovComplexity.Basic

open KolmogorovComplexity

variable {S : Type*}
variable [Primcodable S]

theorem equivalent_refl : Reflexive (equivalent (S := S)) := by
  intro f
  constructor <;> (use 0; norm_num)

theorem equivalent_symm : Symmetric (equivalent (S := S)) := by
  intro f g ⟨h1, h2⟩
  exact ⟨h2, h1⟩

theorem equivalent_trans : Transitive (equivalent (S := S)) := by
  intro f g h ⟨h_fg, h_gf⟩ ⟨h_gh, h_hg⟩
  exact ⟨minorizes_trans f g h h_fg h_gh, minorizes_trans h g f h_hg h_gf⟩

instance : Equivalence (equivalent (S := S)) where
  refl := equivalent_refl
  symm := fun {_ _} h => equivalent_symm h
  trans := fun {_ _ _} hxy hyz => equivalent_trans hxy hyz

/-- Setoid instance for partial computable functions under equivalence. -/
def equivalenceSetoid (S : Type*) [Primcodable S] : Setoid (ℕ →. ℕ) where
  r := equivalent (S := S)
  iseqv := ⟨fun _ => equivalent_refl _, fun h => equivalent_symm h, fun h1 h2 => equivalent_trans h1 h2⟩

/-- The quotient type of partial computable functions by the equivalence relation. -/
def EquivalenceClass (S : Type*) [Primcodable S] :=
  Quotient (equivalenceSetoid S)

/-- The equivalence class of a partial computable function. -/
def toEquivalenceClass (f : ℕ →. ℕ) : EquivalenceClass S :=
  Quotient.mk (equivalenceSetoid S) f

/-- Two functions are in the same equivalence class iff they are equivalent. -/
theorem mem_same_class (f g : ℕ →. ℕ) :
    toEquivalenceClass (S := S) f = toEquivalenceClass (S := S) g ↔ equivalent (S := S) f g := by
  unfold toEquivalenceClass
  exact @Quotient.eq _ (equivalenceSetoid S) f g
