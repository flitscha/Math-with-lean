import Mathlib.Data.Real.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Math.Cone.Basic

namespace Cone


/--
Polynomielle Abbildungen R^m -> R^n
Das heißt, jede der n komponenten ist ein Polynom in m Variablen.
Formal: eine Abbildung {1,..,n} -> {Menge der Polynome mit m Variablen}
-/
def PolyMap (m n : ℕ) := Fin n → MvPolynomial (Fin m) ℝ

-- Auswertung der polynomiellen Abbildung
def PolyMap.eval {m n : ℕ} (φ : PolyMap m n) (x : ℝ^m) : ℝ^n :=
  fun i => MvPolynomial.eval x (φ i)

/--
Polynomiell parametrisierbarere Mengen:
Ein Kegel C ⊆ ℝⁿ ist Polynomiell parametrisierbar, falls es ein
Polynom φ : ℝᵐ -> ℝⁿ gibt, sodass cone(φ(ℝᵐ)) = C
-/
def IsPolynomiallyParamCone {n : ℕ} (C : Set (ℝ^n)) : Prop :=
  ∃ m : ℕ, ∃ (φ : PolyMap m n),
  cone (PolyMap.eval φ '' (Set.univ : Set (ℝ^m))) = C


end Cone
