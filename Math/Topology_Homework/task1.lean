import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.CompactOpen

open Topology

variable {ι : Type*} {π : ι → Type*}
variable [∀ i, TopologicalSpace (π i)]




theorem homeomorphism_compact_to_hausdorff {X Y : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y]
(f : X -> Y) (h_cont : Continuous f) (h_bij : Function.Bijective f) :
∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id ∧ Continuous g := by {

  sorry
}


theorem uniqueness_of_product_topology {I : Type*} {π : I → Type*}
[∀ i, TopologicalSpace (π i)] [∀ i, CompactSpace (π i)] [∀ i, T2Space (π i)]
(T : TopologicalSpace (∀ i, π i))
--(h_a : ∀ j, @Continuous (∀ i, π i) (π j) T (by infer_instance) (fun f => f j))
--(h_b : @CompactSpace (∀ i, π i) T) :
(h_a : ∀ j, Continuous (fun (f : ∀ i, π i) => f j))
(h_b : CompactSpace (∀ i, π i)) :
T = Pi.topologicalSpace := by {

  let α := (∀ i, π i)

  apply le_antisymm

  -- Hinrichtung: ⊆
  rw [Pi.topologicalSpace] -- gröbste Topologie, wo alle projektionen stetig sind
  apply le_iInf
  intro i
  apply continuous_iff_le_induced.mp
  apply h_a

  -- Rückrichtung

  let idd : α -> α := @id α

  have h_id : @Continuous α α T Pi.topologicalSpace idd := by {
    -- identity map : T -> Product is continuous
    apply continuous_iff_le_induced.mpr
    simp [Pi.topologicalSpace]
    sorry
  }

  have h_compact : @CompactSpace (∀ i, π i) Pi.topologicalSpace := by {
    -- Satz von Tychonoff
    apply Pi.compactSpace
  }

  have h_hausdorff : @T2Space (∀ i, π i) T := by {
    apply t2Space_iff_disjoint_nhds.mpr
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
    obtain ⟨U, V, hUx, hVy, h_disj⟩ := t2_separation h

    -- Jetzt konstruieren wir die offenen Mengen im Produktraum
    let projection_i : α -> π i := (fun (f : ∀ j, π j) => f i)
    let U' : Set α := projection_i ⁻¹' U
    let V' : Set α := projection_i ⁻¹' V
    have h_prod_open_x : @IsOpen α Pi.topologicalSpace U' := by {
      sorry
    }
    have h_prod_open_y : @IsOpen α Pi.topologicalSpace V' := by {
      sorry
    }

    -- Diese mengen beinhalten x und y
    have h_x_mem : x ∈ U' := by {
      sorry
    }
    have h_y_mem : y ∈ V' := by {
      sorry
    }

    -- Und diese Mengen sind disjunkt
    have h_disj' : Disjoint U' V' := by {
      sorry
    }

    -- jetzt können wir schließen, dass U' und V' die punkte x und y trennen.
  }

  -- Satz 5.19
  have h : ∃ g : α → α, idd ∘ g = id ∧ g ∘ idd = id ∧ (@Continuous α α Pi.topologicalSpace T g) := by {
    apply @homeomorphism_compact_to_hausdorff α α T Pi.topologicalSpace
    apply h_id
    sorry
  }

  obtain ⟨g, h1, h2, h⟩ := h
  have hh : g = id := by {
    sorry
  }

  rw [hh] at h
  apply continuous_id_iff_le.mp h
}
