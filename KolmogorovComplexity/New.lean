import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Order.WithBot
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace KolmogorovComplexity

open Classical

/--
  The complexity of object x with respect to f.
  Cf(x) = min { l(p) : f(p) = n(x) }
-/

noncomputable def complexity (f: ℕ →. ℕ) (x : ℕ) : ℕ∞ :=
  if h : ∃ p : ℕ, x ∈ f p then
    (Nat.find h).size
  else
    ⊤

-- def minorizes (f g : ℕ →. ℕ) : Prop :=
--   ∃ c : ℕ, ∀ x : ℕ, complexity f x ≤ complexity g x + c

-- def equivalent (f g : ℕ →. ℕ) : Prop :=
--   minorizes (S := S) f g ∧ minorizes (S := S) g f

def additively_optimal (f : ℕ →. ℕ) : Prop :=
  ∀ g : ℕ →. ℕ, Partrec g → ∃ c : ℕ, ∀ x : ℕ, complexity f x ≤ complexity g x + c

axiom universal_partrec : ℕ →. ℕ
axiom universal_partrec_is_partrec : Partrec universal_partrec
axiom universal_partrec_is_universal :
  ∀ g : ℕ →. ℕ, Partrec g → ∃ e : ℕ, ∀ x : ℕ, universal_partrec (Nat.pair e x) = g x

lemma pair_adds_constant_overhead (e : ℕ) :
  ∃ c : ℕ, ∀ p : ℕ, (Nat.pair e p).size ≤ p.size + c := by
  sorry

lemma exists_additively_optimal_partrec:
  ∃ f : ℕ →. ℕ, Partrec f ∧ additively_optimal f := by
  use universal_partrec
  constructor
  · exact universal_partrec_is_partrec
  · intro g hg
    obtain ⟨e, he⟩ := universal_partrec_is_universal g hg
    obtain ⟨c, hc⟩ := pair_adds_constant_overhead e
    use c
    intro x
    unfold complexity
    by_cases hx : ∃ q : ℕ, x ∈ g q
    · -- Case: witness exists for g
      let q := Nat.find hx
      have hq : x ∈ g q := Nat.find_spec hx
      let p := Nat.pair e q
      have hp : x ∈ universal_partrec p := by
        rw [he]
        exact hq

      -- Now prove the inequality
      split_ifs with hu_desc hg_desc
      · -- Both have descriptions
        -- Show that the minimal description for universal_partrec is at most p
        have h_find : Nat.find hu_desc ≤ p := Nat.find_min' hp

        -- Convert to size inequality
        have h_size : (Nat.find hu_desc).size ≤ p.size := Nat.size_le_size h_find
    sorry

end KolmogorovComplexity
