import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Math.Cone.Basic
import Math.Cone.Parametrisation

namespace Cone

/--
Der positive Orthant in `ℝⁿ`: Alle Vektoren mit nichtnegativen Koordinaten.
-/
def posOrthant (n : Nat) : Set (ℝ^n) :=
  { x | ∀ i, 0 ≤ x i }


/-- Der positive Orthant ist ein Kegel. -/
theorem posOrthant_isCone (n : Nat) : IsCone (posOrthant n) := by
  rw [IsCone, posOrthant]
  intro x hx t ht
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro i
  specialize hx i
  have h_nonneg : 0 ≤ t * x i := mul_nonneg ht hx
  simp [smul_eq_mul]
  exact h_nonneg


-- Der positive Orthant ist polynomiell parametrisierbar.
theorem posOrthant_isPolynomiallyParam (n : Nat) :
    IsPolynomiallyParamCone (posOrthant n) := by {
  use n
  let φ : PolyMap n n := fun i => (MvPolynomial.X i) ^ 2
  use φ
  simp [cone, posOrthant]
  ext x
  constructor
  -- wir zeigen die Richtung: x ∈ cone(φ(ℝⁿ)) => x ∈ posOrthant n
  simp
  intro t ht y h k
  simp [h]
  simp [φ, PolyMap.eval]
  apply mul_nonneg ht
  apply pow_two_nonneg

  -- Rückrichtung
  simp
  intro h
  use 1
  simp
  use fun i => Real.sqrt (x i)
  funext i
  simp [φ, PolyMap.eval]
  symm
  apply Real.sq_sqrt (h i)
}


end Cone
