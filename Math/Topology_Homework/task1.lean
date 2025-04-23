import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Homeomorph

open Topology

/-
$\textbf{Blatt 4, Aufgabe 5}$
Es seien $(X_i)_{i \in I}$ kompakte Hausdorff-Räume. Zeigen Sie, dass die Produkttopologie
die eindeutige Topologie auf $\prod_{i \in I} X_i$ mit den folgenden Eigenschaften:

(a) Die Projektionen $\pi_j : \prod_{i \in I} X_i \to X_j$ sind alle stetig.

(b) $\prod_{i \in I} X_i$ ist kompakt.
-/
theorem uniqueness_of_product_topology {I : Type*} {X : I → Type*}
[∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
(T : TopologicalSpace (∀ i, X i))
(h_a : ∀ j, Continuous (fun (f : ∀ i, X i) => f j))
(h_b : CompactSpace (∀ i, X i)) :
T = Pi.topologicalSpace := by {

  let Xₚ := (∀ i, X i) -- zugrundeliegende Menge der Produkttopologie
  let π (i : I) := fun f : Xₚ => f i -- die Projektion auf die i-te Komponente

  /-
  $\textbf{Beweis:}$
  Wir definieren das kartesische Produkt $\mathcal{X} := \prod_{i \in I} X_i$.
  Sei $\mathcal{T}$ eine Topologie auf $\mathcal{X}$ mit den Eigenschaften (a) und (b).
  Wir zeigen, dass $\mathcal{T}$ gleich der Produkttopologie ist.
  Zuerst zeigen wir die Inklusion $\mathcal{T} \subseteq \mathcal{T}_\Pi$.
  Die Produkttopologie ist per Definition die gröbste Topologie, sodass alle Projektionen stetig sind.
  Da nach Voraussetzung jede Projektion $\pi_j$ bezüglich $\mathcal{T}$ stetig ist, folgt: $\mathcal{T} \subseteq \mathcal{T}_\Pi$.
  -/
  have h_hinrichtung : T ≤ Pi.topologicalSpace := by {
    rw [Pi.topologicalSpace] -- gröbste Topologie, wo alle projektionen stetig sind
    apply le_iInf
    intro i
    apply continuous_iff_le_induced.mp
    apply h_a
  }

  apply le_antisymm
  apply h_hinrichtung


  /-
  Für die Rückrichtung zeigen wir: $\mathcal{T}_\Pi \subseteq \mathcal{T}$.
  Dazu zeigen wir, dass die Identitätsabbildung $\mathrm{id} : (\mathcal{X}, \mathcal{T}_\Pi) \to (\mathcal{X}, \mathcal{T})$ stetig ist.
  -/
  let idd : Xₚ -> Xₚ := @id Xₚ

  /-
  Da $\mathcal{T} \subseteq \mathcal{T}_\Pi$, ist die Identität in die andere Richtung stetig,
  also $\mathrm{id} : (\mathcal{X}, \mathcal{T}) \to (\mathcal{X}, \mathcal{T}_\Pi)$.
  -/
  have h_id : @Continuous Xₚ Xₚ T Pi.topologicalSpace idd := by {
    apply continuous_id_iff_le.mpr h_hinrichtung
  }
  clear h_hinrichtung

  /-
  Wir zeigen, dass $(\mathcal{X}, \mathcal{T}_\Pi)$ ein Hausdorffraum ist.

  Seien $x, y \in \mathcal{X}$ mit $x \ne y$.
  Dann existiert ein Index $i \in I$ mit $x_i \ne y_i$.
  -/
  have h_hausdorff : @T2Space Xₚ Pi.topologicalSpace := by {
    rw [t2Space_iff]
    intro x y h_not_eq

    have h : ∃ i, x i ≠ y i := by {
      by_contra h
      push_neg at h
      have h_eq : x = y := funext h
      exact h_not_eq h_eq
    }
    obtain ⟨i, h⟩ := h

    /-
    Da $X_i$ ein Hausdorffraum ist, gibt es disjunkte offene Mengen $U, V \subseteq X_i$,
    sodass $x_i \in U$, $y_i \in V$ und $U \cap V = \emptyset$.
    -/
    obtain ⟨U, V, h_U_open, h_V_open, h_xU, h_yV, h_disj⟩ := t2_separation h

    /-
    Dann sind $U' := \pi_i^{-1}(U)$ und $V' := \pi_i^{-1}(V)$ offene Mengen in der Produkttopologie,
    die $x$ und $y$ enthalten, und disjunkt sind.
    -/
    let U' : Set Xₚ := (π i)⁻¹' U
    let V' : Set Xₚ := (π i)⁻¹' V
    letI : TopologicalSpace Xₚ := Pi.topologicalSpace -- wir arbeiten mit der Produkttopologie
    have h_U'_open : @IsOpen Xₚ Pi.topologicalSpace U' := by {
      apply Continuous.isOpen_preimage
      exact continuous_apply i
      exact h_U_open
    }
    have h_V'_open : @IsOpen Xₚ Pi.topologicalSpace V' := by {
      apply Continuous.isOpen_preimage
      exact continuous_apply i
      exact h_V_open
    }

    have h_disj' : Disjoint U' V' := by {
      apply h_disj.preimage
    }

    /-
    Damit haben wir gezeigt, dass die Produkttopologie ein Hausdorffraum ist.
    -/
    use U', V'
    exact ⟨h_U'_open, h_V'_open, h_xU, h_yV, h_disj'⟩
  }

  /-
  Jetzt wenden wir Satz 5.19 an. Er besagt, dass eine stetige, bijektive Abbildung
  zwischen einem kompaktem Raum und einem Hausdorffraum ein Homöomorphismus ist.

  Wir wenden den Satz auf die Identitätsabbildung $\mathrm{id} : (\mathcal{X}, \mathcal{T}_\Pi) \to (\mathcal{X}, \mathcal{T})$ an.
  Somit ist auch die Identität in die andere Richtung stetig.
  Daraus folgt: $\mathcal{T}_\Pi \subseteq \mathcal{T}$.
  -/
  have h := @Continuous.continuous_symm_of_equiv_compact_to_t2 Xₚ Xₚ T
    Pi.topologicalSpace h_b h_hausdorff (Equiv.refl Xₚ) h_id
  simp at h
  apply continuous_id_iff_le.mp h
}
