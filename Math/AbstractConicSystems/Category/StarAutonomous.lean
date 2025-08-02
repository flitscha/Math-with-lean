import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Iso


open CategoryTheory
open MonoidalCategory
open Opposite


structure StarAutonomousCategoryStruct (C : Type u) [Category.{v} C]
[MonoidalCategory C] [SymmetricCategory C] where
  starFunctor : Cᵒᵖ ⥤ C

  duality_equiv :
    ∀ (a b c : C),
      (a ⊗ b ⟶ c) ≃
      (a ⟶ starFunctor.obj (op (b ⊗ (starFunctor.obj (op c)))))


class StarAutonomousCategory (C : Type u)
  [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  extends StarAutonomousCategoryStruct C where

  [full_star : Functor.Full starFunctor]
  [faithful_star : Functor.Faithful starFunctor]

  -- the functors are contravariant
  naturality_a :
  ∀ {a a' b c : C} (f : a' ⟶ a) (h : a ⊗ b ⟶ c),
    (duality_equiv a' b c).toFun ((f ⊗ 𝟙 b) ≫ h) =
    f ≫ (duality_equiv a b c).toFun h

  -- the functors are contravariant
  naturality_b :
  ∀ {a b b' c : C} (f : b' ⟶ b) (h : a ⊗ b ⟶ c),
    (duality_equiv a b' c).toFun ((𝟙 a ⊗ f) ≫ h) =

    (duality_equiv a b c).toFun h ≫
    starFunctor.map (op (f ⊗ 𝟙 (starFunctor.obj (op c))))

  -- the functors are covariant
  naturality_c :
  ∀ {a b c c' : C} (f : c ⟶ c') (h : a ⊗ b ⟶ c),
    (duality_equiv a b c').toFun (h ≫ f) =

    (duality_equiv a b c).toFun h ≫
    starFunctor.map (op (𝟙 b ⊗ (starFunctor.map (op f))))



namespace StarAutonomous

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [StarAutonomousCategory C]

-- The star functor of a star-autonomous category.
abbrev star : Cᵒᵖ ⥤ C := StarAutonomousCategory.toStarAutonomousCategoryStruct.starFunctor

abbrev dualObj (X : C) : C :=
  star.obj (Opposite.op X)

scoped notation X "⋆" => dualObj X

@[simp]
lemma dualObj_eq_star (X : C) :
  X⋆ = star.obj (Opposite.op X) := rfl

abbrev dualMap {X Y : C} (f : X ⟶ Y) : dualObj Y ⟶ dualObj X :=
  star.map (Opposite.op f)

abbrev duality_map (a b c : C) :
    (a ⊗ b ⟶ c) → (a ⟶ (b ⊗ c⋆)⋆) :=
  (StarAutonomousCategory.toStarAutonomousCategoryStruct.duality_equiv a b c).toFun

abbrev duality_map_inv (a b c : C) :
    (a ⟶ (b ⊗ c⋆)⋆) → (a ⊗ b ⟶ c) :=
  (StarAutonomousCategory.toStarAutonomousCategoryStruct.duality_equiv a b c).invFun

end StarAutonomous
