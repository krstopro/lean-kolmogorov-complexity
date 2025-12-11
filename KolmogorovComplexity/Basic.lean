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
variable [Primcodable S]
variable [Denumerable S]

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

omit [Denumerable S] in
lemma minorizes_trans (f g h : ℕ →. ℕ) (h_fg : minorizes (S := S) f g) (h_gh : minorizes (S := S) g h)
    : minorizes (S := S) f h := by
  obtain ⟨c_fg, h_fg_⟩ := h_fg
  obtain ⟨c_gh, h_gh_⟩ := h_gh
  use c_fg + c_gh
  intro x
  calc complexity f x
      ≤ complexity g x + c_fg := h_fg_ x
    _ ≤ (complexity h x + c_gh) + c_fg := by
        rw [add_comm (complexity g x), add_comm (complexity h x + c_gh)]
        exact add_le_add_right (h_gh_ x) c_fg
    _ = complexity h x + (c_gh + c_fg) := by rw [add_assoc]
    _ = complexity h x + (c_fg + c_gh) := by congr 1; ring

omit [Denumerable S] in
theorem equivalent_refl : Reflexive (equivalent (S := S)) := by
  intro f
  constructor <;> (use 0; norm_num)

omit [Denumerable S] in
theorem equivalent_symm : Symmetric (equivalent (S := S)) := by
  intro f g ⟨h1, h2⟩
  exact ⟨h2, h1⟩

omit [Denumerable S] in
theorem equivalent_trans : Transitive (equivalent (S := S)) := by
  intro f g h ⟨h_fg, h_gf⟩ ⟨h_gh, h_hg⟩
  exact ⟨minorizes_trans f g h h_fg h_gh, minorizes_trans h g f h_hg h_gf⟩

instance : Equivalence (equivalent (S := S)) where
  refl := equivalent_refl
  symm := fun {_ _} h => equivalent_symm h
  trans := fun {_ _ _} hxy hyz => equivalent_trans hxy hyz

def additively_optimal (f : ℕ →. ℕ) (C : Set (ℕ →. ℕ)) : Prop :=
  ∀ g ∈ C, minorizes (S := S) f g

/-- There is an additively optimal universal partial computable function. -/
lemma lem_2_1_1 : ∃ f : ℕ →. ℕ, Partrec f ∧ additively_optimal (S := S) f { g : ℕ →. ℕ | Partrec g } := by
  sorry

def description (f : ℕ →. ℕ) (x y: S) (p : ℕ ) : Prop :=
  Partrec f ∧ f (Nat.pair (Encodable.encode y) p) = Encodable.encode x

noncomputable def description_complexity (f: ℕ →. ℕ) (x y : S) :=
  sInf ((fun p => (l p : WithTop ℕ)) '' { p | Encodable.encode x ∈ f (Nat.pair (Encodable.encode y) p) })

def φ₀ : ℕ →. ℕ := sorry

noncomputable def conditional_complexity (x y : S) :=
  description_complexity φ₀ x y

noncomputable def unconditional_complexity (x : S) := by
  choose ε _ _ using Denumerable.decode_inv (α := S) 0
  exact conditional_complexity x ε

end KolmogorovComplexity
