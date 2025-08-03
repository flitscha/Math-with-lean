import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Basic

namespace Cone

-- Wir arbeiten über einem beliebigen ℝ-Vektorraum
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
R^n definieren wir als die Menge der funktionen f : {1,...,n} -> ℝ
-/
abbrev Rn (n : ℕ) := Fin n → ℝ
notation "ℝ^" n => Rn n

/--
Ein `cone S` ist die Menge aller positiven Skalierungen von Elementen aus `S`.
Das funktioniert für jede Teilmenge `S` eines ℝ-Vektorraums `V`.
-/
def cone (S : Set V) : Set V :=
  { y | ∃ (t : ℝ) (x : S), 0 ≤ t ∧ y = t • x }

/--
Eine Menge `C` ist ein Kegel, wenn sie unter positiver Skalierung abgeschlossen ist.
-/
def IsCone (C : Set V) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ (t : ℝ), 0 ≤ t → t • x ∈ C


theorem cone_tmp {S : Set V} (h_cone : IsCone S) {x : V} (hx : x ∈ S)
    {t : ℝ} (ht : 0 ≤ t) : t • x ∈ S :=
  h_cone hx t ht


/-- `cone S` ist immer ein Kegel. -/
theorem cone_isCone (S : Set V) : IsCone (cone S) := by
  intro x hx t ht
  simp [cone] at hx ⊢
  obtain ⟨t', h₁, x, h₂, _, _⟩ := hx
  use t * t'
  constructor
  apply mul_nonneg ht h₁
  use x
  constructor
  exact h₂
  rw [smul_smul]


end Cone
