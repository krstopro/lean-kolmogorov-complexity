import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Order.WithBot
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace KolmogorovComplexity

open Part Set

variable {S : Type*}
variable {y : S}
variable [Primcodable S]

def l (n : ℕ) : ℕ := Nat.log2 (n + 1)

/--
  The complexity of object x with respect to f.
  Cf(x) = min { l(p) : f(p) = n(x) }
-/
noncomputable def complexity (f: ℕ →. ℕ) (x : S) :=
  sInf ((fun p => (l p : WithTop ℕ)) '' { p | Encodable.encode x ∈ f p })

def minorizes (f g : ℕ →. ℕ) : Prop :=
  ∃ c : ℕ, ∀ x : S, complexity f x ≤ complexity g x + c

def equivalent (f g : ℕ →. ℕ) : Prop :=
  minorizes (S := S) f g ∧ minorizes (S := S) g f

def additively_optimal (f : ℕ →. ℕ) (C : Set (ℕ →. ℕ)) : Prop :=
  ∀ g ∈ C, minorizes (S := S) f g

/-- There is an additively optimal universal partial computable function. -/
lemma lem_2_1_1 : ∃ f : ℕ →. ℕ, Partrec f ∧ additively_optimal (S := S) f { g : ℕ →. ℕ | Partrec g } := by
  sorry

end KolmogorovComplexity
