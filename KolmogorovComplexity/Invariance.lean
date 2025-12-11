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
