import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Order.WithBot
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace KolmogorovComplexity

open Part Set Encodable

variable {S : Type*}
variable [Primcodable S]
variable [Denumerable S]

def l (n : ℕ) : ℕ := Nat.log2 (n + 1)

/--
  The complexity of object x with respect to f.
  Cf(x) = min { l(p) : f(p) = n(x) }
-/
noncomputable def complexity (f: ℕ →. ℕ) (x : S) :=
  sInf ((fun p => (l p : WithTop ℕ)) '' { p | encode x ∈ f p })

def minorizes (f g : ℕ →. ℕ) : Prop :=
  ∃ c : ℕ, ∀ x : S, complexity f x ≤ complexity g x + c

def equivalent (f g : ℕ →. ℕ) : Prop :=
  minorizes (S := S) f g ∧ minorizes (S := S) g f

def additively_optimal (f : ℕ →. ℕ) (C : Set (ℕ →. ℕ)) : Prop :=
  ∀ g ∈ C, minorizes (S := S) f g

/-- There is an additively optimal universal partial computable function. -/
lemma lem_2_1_1 : ∃ f : ℕ →. ℕ, Partrec f ∧ additively_optimal (S := S) f { g : ℕ →. ℕ | Partrec g } := by
  use
    let code_left := Nat.Partrec.Code.comp Nat.Partrec.Code.left Nat.Partrec.Code.id
    let code_right := Nat.Partrec.Code.comp Nat.Partrec.Code.right Nat.Partrec.Code.id
    let code := Nat.Partrec.Code.pair code_left code_right
    Nat.Partrec.Code.eval code
  constructor
  · simp
    constructor
    refine Nat.Partrec.pair ?_ ?_
    · apply Nat.Partrec.Code.exists_code.mpr
      use Nat.Partrec.Code.left.comp Nat.Partrec.Code.id
    · apply Nat.Partrec.Code.exists_code.mpr
      use (Nat.Partrec.Code.right.comp Nat.Partrec.Code.id)
    · apply Nat.Partrec.Code.exists_code.mpr
      simp
      use Nat.Partrec.Code.id
      funext n
      exact Nat.Partrec.Code.eval_id n
  · unfold additively_optimal
    intro g g_mem
    unfold minorizes
    sorry

def description (φ : ℕ →. ℕ) (x y: S) (p : ℕ ) : Prop :=
  Partrec φ ∧ φ (Nat.pair (encode y) p) = encode x

noncomputable def description_complexity (φ: ℕ →. ℕ) (x y : S) :=
  sInf ((fun p => (l p : WithTop ℕ)) '' { p | description φ x y p })

def description_minorizes (φ γ : ℕ →. ℕ) : Prop :=
  ∃ χ : ℕ, ∀ x y : S, description_complexity φ x y ≤ description_complexity γ x y + χ

def description_additively_optimal (φ₀ : ℕ →. ℕ) (C : Set (ℕ →. ℕ)) : Prop :=
  ∀ φ ∈ C, description_minorizes (S := S) φ₀ φ

def description_additively_optimal_class :=
  {φ | Partrec φ ∧ description_additively_optimal (S:= S) φ {γ : ℕ →. ℕ | Partrec γ}}

theorem the_2_1_1 : ∃ φ₀ : ℕ →. ℕ, Partrec φ₀ ∧ description_additively_optimal (S:= S) φ₀ {φ : ℕ →. ℕ | Partrec φ} :=
  sorry

def φ₀ : ℕ →. ℕ := sorry

noncomputable def conditional_complexity (x y : S) :=
  description_complexity φ₀ x y

noncomputable def unconditional_complexity (x : S) := by
  choose ε _ _ using Denumerable.decode_inv (α := S) 0
  exact conditional_complexity x ε

end KolmogorovComplexity
