import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.CompactOpen

open Topology

variable {ι : Type*} {π : ι → Type*}
variable [∀ i, TopologicalSpace (π i)]




theorem homeomorphism_compact_to_hausdorff {X Y : Type*}
[TopologicalSpace X] [TopologicalSpace Y] (h_compact: CompactSpace X) (h_hausdorff : T2Space Y)
(f : X -> Y) (h_cont : Continuous f) (h_bij : Function.Bijective f) :
∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id ∧ Continuous g := by {

  sorry
}


theorem uniqueness_of_product_topology {I : Type*} {π : I → Type*}
[∀ i, TopologicalSpace (π i)] [∀ i, CompactSpace (π i)] [∀ i, T2Space (π i)]
(T : TopologicalSpace (∀ i, π i))
(h_a : ∀ j, Continuous (fun (f : ∀ i, π i) => f j))
(h_b : CompactSpace (∀ i, π i)) :
T = Pi.topologicalSpace := by {

  let α := (∀ i, π i)

  -- Hinrichtung: ⊆
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
    let projection_i : α -> π i := (fun (f : ∀ j, π j) => f i)
    let U' : Set α := projection_i ⁻¹' U
    let V' : Set α := projection_i ⁻¹' V
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

  -- Wir verwenden Satz 5.19, um zu zeigen, dass die Identität ein Homöomorphismus ist.
  have h : ∃ g : α → α, id ∘ g = id ∧ g ∘ id = id ∧ (@Continuous α α Pi.topologicalSpace T g) := by {
    apply @homeomorphism_compact_to_hausdorff α α T Pi.topologicalSpace
    exact h_b
    exact h_hausdorff
    apply h_id
    apply Function.bijective_id
  }

  obtain ⟨g, h1, h2, h⟩ := h
  have hh : g = id := by {
    rw [← h1]
    simp
  }

  rw [hh] at h
  apply continuous_id_iff_le.mp h
}
