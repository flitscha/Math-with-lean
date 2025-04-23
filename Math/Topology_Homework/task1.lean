import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Homeomorph

open Topology


theorem uniqueness_of_product_topology {I : Type*} {X : I → Type*}
[∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
(T : TopologicalSpace (∀ i, X i))
(h_a : ∀ j, Continuous (fun (f : ∀ i, X i) => f j))
(h_b : CompactSpace (∀ i, X i)) :
T = Pi.topologicalSpace := by {

  let α := (∀ i, X i)
  let π (i : I) := fun f : α => f i -- die Projektion auf die i-te Komponente

  -- Hinrichtung 💀: ⊆
  have h_hinrichtung : T ≤ Pi.topologicalSpace := by {
    rw [Pi.topologicalSpace] -- gröbste Topologie, wo alle projektionen stetig sind
    apply le_iInf
    intro i
    apply continuous_iff_le_induced.mp
    apply h_a
  }

  apply le_antisymm
  apply h_hinrichtung


  -- Rückrichtung
  let idd : α -> α := @id α

  have h_id : @Continuous α α T Pi.topologicalSpace idd := by {
    apply continuous_id_iff_le.mpr h_hinrichtung
  }
  clear h_hinrichtung

  -- wir zeigen, dass die Produkttopologie ein Hausdorff-Raum ist
  have h_hausdorff : @T2Space α Pi.topologicalSpace := by {
    rw [t2Space_iff]
    intro x y h_not_eq

    -- da x ≠ y, gibt es eine Komponente i, wo x_i ≠ y_i
    have h : ∃ i, x i ≠ y i := by {
      by_contra h
      push_neg at h
      have h_eq : x = y := funext h
      exact h_not_eq h_eq
    }
    obtain ⟨i, h⟩ := h

    -- Wir benutzen, dass X_i haussdorff ist. Wir können x_i und y_i trennen
    obtain ⟨U, V, h_U_open, h_V_open, h_xU, h_yV, h_disj⟩ := t2_separation h

    -- Jetzt konstruieren wir die offenen Mengen im Produktraum
    let U' : Set α := (π i)⁻¹' U
    let V' : Set α := (π i)⁻¹' V
    letI : TopologicalSpace α := Pi.topologicalSpace -- wir arbeiten mit der Produkttopologie
    have h_U'_open : @IsOpen α Pi.topologicalSpace U' := by {
      apply Continuous.isOpen_preimage
      exact continuous_apply i
      exact h_U_open
    }
    have h_V'_open : @IsOpen α Pi.topologicalSpace V' := by {
      apply Continuous.isOpen_preimage
      exact continuous_apply i
      exact h_V_open
    }

    -- Diese Mengen sind disjunkt
    have h_disj' : Disjoint U' V' := by {
      apply h_disj.preimage
    }

    -- jetzt können wir schließen, dass U' und V' die punkte x und y trennen.
    use U', V'
    exact ⟨h_U'_open, h_V'_open, h_xU, h_yV, h_disj'⟩
  }

  -- jetzt können wir Satz 5.19 anwenden.
  -- dadurch erhalten wir, dass die Identität auch in die andere richtung stetig ist.
  have h := @Continuous.continuous_symm_of_equiv_compact_to_t2 α α T
    Pi.topologicalSpace h_b h_hausdorff (Equiv.refl α) h_id
  simp at h
  apply continuous_id_iff_le.mp h
}
