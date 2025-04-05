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
    sorry
  }

  have h_compact : @CompactSpace (∀ i, π i) Pi.topologicalSpace := by {
    -- Satz von Tychonoff
    apply Pi.compactSpace
  }

  have h_hausdorff : @T2Space (∀ i, π i) T := by {
    sorry
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
