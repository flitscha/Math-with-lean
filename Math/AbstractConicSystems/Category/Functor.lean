import Math.AbstractConicSystems.Category.StarAutonomous
import Mathlib.CategoryTheory.Monoidal.Functor

open CategoryTheory
open MonoidalCategory
open StarAutonomous

variable (C : Type v₁) (D : Type v₂)
  [Category C] [MonoidalCategory C] [SymmetricCategory C] [StarAutonomousCategory C]
  [Category D] [MonoidalCategory D] [SymmetricCategory D] [StarAutonomousCategory D]

/--
A **star monoidal functor** is a strong monoidal functor between star autonomous categories
which is compatible with the duality functors (`star`) via a natural isomorphism.
-/
structure LaxStarMonoidalFunctor extends MonoidalFunctor C D where
  star_map : ∀ X : C, obj (dualObj X) ⟶ dualObj (obj X)
  star_map_natural :
    ∀ {X Y : C} (f : X ⟶ Y),
      map (dualMap f) ≫ star_map X = star_map Y ≫ dualMap (map f)


structure StarMonoidalFunctor extends LaxStarMonoidalFunctor C D where
  -- the star map is an isomorphism
  star_map_isIso : ∀ X : C, IsIso (star_map X) := by infer_instance


-- for a star monoidal functor, the star_map is an isomorphism
instance {F : StarMonoidalFunctor C D} (X : C) : IsIso (F.star_map X) :=
  F.star_map_isIso X

instance (F : StarMonoidalFunctor C D) (X Y : C) : IsIso (F.μ X Y) :=
  F.μ_isIso X Y


/--
For a star monoidal functor, we obtain natural isomorphisms:
`D(F(a ⊗ b), F(c)) ≅ D(F(a), F((b ⊗ c⋆)⋆))`
-/
noncomputable def functorDualityIso (F : StarMonoidalFunctor C D) (a b c : C) :
    ((F.obj (a ⊗ b)) ⟶ F.obj c) ->
    (F.obj a ⟶ F.obj ((b ⊗ c⋆)⋆)) :=
  fun h =>
    (duality_map (F.obj a) (F.obj b) (F.obj c))
    (F.μ a b ≫ h) ≫
    dualMap (𝟙 (F.obj b) ⊗ (F.star_map c)) ≫
    dualMap (inv (F.μ b (c⋆))) ≫
    inv (F.star_map (b ⊗ c⋆))


/--
noncomputable def functorDualityIso_readable (F : StarMonoidalFunctor C D) (a b c : C) :
    ((F.obj (a ⊗ b)) ⟶ F.obj c) ->
    (F.obj a ⟶ F.obj ((b ⊗ c⋆)⋆)) := by {
  intro f
  let f1 := F.μ a b
  let f2 := f1 ≫ f

  let f_dual := duality_map (F.obj a) (F.obj b) (F.obj c)

  let f3 := f_dual f2

  -- changing F and ⋆
  let f_swap := 𝟙 (F.obj b) ⊗ (F.star_map c)
  let f_swap_star := dualMap f_swap
  let f4 := f3 ≫ f_swap_star

    -- moving the F out
  let f_mu := dualMap (inv (F.μ b (c⋆)))
  let f5 := f4 ≫ f_mu

  -- changing F and ⋆ again
  let f_swap2 := inv (F.star_map (b ⊗ c⋆))
  let f6 := f5 ≫ f_swap2
  exact f6
}
-/


structure StarAutonomousFunctor extends StarMonoidalFunctor C D where
  duality_compatibility :
    ∀ {a b c : C} (h : a ⊗ b ⟶ c),
      map ((duality_map a b c) h) =
      -- idk how to use the defined functorDualityIso
      (duality_map (obj a) (obj b) (obj c))
      (μ a b ≫ map h) ≫
      dualMap (𝟙 (obj b) ⊗ (star_map c)) ≫
      dualMap (inv (μ b (c⋆))) ≫
      inv (star_map (b ⊗ c⋆))
