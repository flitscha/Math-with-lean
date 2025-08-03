import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Fin.Basic
import Math.Cone.Basic
import Math.Cone.Parametrisation

namespace Cone

/--
Wir definieren einen LorentzVector als tupel (t, x)
Dadurch wird die definition vom Lorentz-Kegel eleganter.
-/
abbrev LorentzVector (n : ℕ) := ℝ × ℝ^n

/--
Um einen lorentz Vektor als Element im R^(n+1) zu sehen:
-/

def flat_lorentz_vector {n : ℕ} (v : LorentzVector n) : ℝ^(n+1) :=
  fun k =>
    match k with
    | ⟨0, _⟩   => v.1
    | ⟨i+1, h⟩ => v.2 ⟨i, Nat.lt_of_succ_lt_succ h⟩

lemma flat_lorentz_vector_zero {n : ℕ} (v : LorentzVector n) :
  flat_lorentz_vector v 0 = v.1 := rfl

/--
Der Lorentz-Kegel in `ℝ^(n+1)`: Alle Vektoren `(t,x)` mit `t ≥ ‖x‖`.
t ist die "höhe" vom Kegel.
@euclNormSq n (fun i => x i.succ) ist die euklidische Norm vom restvector `x`.
-/
def lorentzCone (n : Nat) : Set (LorentzVector n) :=
  { p | 0 ≤ p.1 ∧ p.1^2 ≥ ‖p.2‖^2 }

/-- Der Lorentz-Kegel ist ein Kegel. -/
theorem lorentzCone_isCone (n : Nat) : IsCone (lorentzCone n) := by
  simp [IsCone, lorentzCone]
  intro t x -- vector (t, x) in Rⁿ⁺¹
  intro h1 h2 -- conditions, that x is in the lorentz cone
  intro r hr -- arbitrary r >= 0
  constructor
  apply mul_nonneg hr h1
  have h_rhs : (r * t) ^ 2 = r^2 * t^2 := by apply mul_pow
  have h_lhs : ‖r • x‖ ^ 2 = r^2 * ‖x‖^2 := by {
    rw [norm_smul, mul_pow, Real.norm_eq_abs, pow_abs, abs_of_nonneg]
    apply pow_two_nonneg
  }
  rw [h_rhs, h_lhs]
  apply mul_le_mul_of_nonneg_left
  exact h2
  apply pow_two_nonneg


-- Problem: umgekehrt: 0 ist die z-achse!
noncomputable def lorentzPolyMap (n : ℕ) : PolyMap n (n+1) :=
  fun i =>
    if h : i.val < n then
      MvPolynomial.X (Fin.castLT i h)
    else
      ∑ j : Fin n, (MvPolynomial.X j) ^ 2



/--
theorem lorentz_isPolynomiallyParam (n : Nat) :
    IsPolynomiallyParamCone (flat_lorentz_vector '' (lorentzCone n)) := by {
  simp [lorentzCone]
  simp [Set.image]
  simp [IsPolynomiallyParamCone]
  -- define the polynomial function φ
  use n
  use lorentzPolyMap n
  ext x
  simp [cone, Set.range, PolyMap.eval]
  constructor
  -- ⊆
  intro h
  obtain ⟨t, ht, a, h⟩ := h
  simp [h]
  --let w : ℝ^n := fun i => 1
  use t, a
  constructor
  constructor
  exact ht
  sorry
  ext y
  simp [PolyMap.eval, lorentzPolyMap]

  --have hh : flat_lorentz_vector (t, a) y =
  --simp [flat_lorentz_vector]
  cases y using Fin.cases with
  | zero =>
    have hh : flat_lorentz_vector (t, a) 0 = t := rfl
    simp [hh]
    split_ifs
    simp [Fin.castLT]
    simp [Fin.mk]


  | succ i =>
    sorry


  /-| zero =>
    split_ifs
    rw [MvPolynomial.eval_X]

    simp [Fin.castLT]
    simp [match]
    simp

    sorry
  | succ i =>
    simp
    simp"""-/




  sorry
}
-/
