import Math.AbstractConicSystems.Category.StarAutonomous

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.FiniteDimensional

open CategoryTheory
open Opposite
open StarAutonomous
open MonoidalCategory
open scoped TensorProduct
open CategoryTheory.FullSubcategory


-- the Category of finite dimensional, real vector sapces
abbrev FVec := FullSubcategory (fun M : ModuleCat ℝ => FiniteDimensional ℝ M)


-- Auxiliary function to lift an isomorphism in the subcategory into the original category.
def isoMk {C : Type u} [Category C] {Z : C → Prop} {X Y : FullSubcategory Z}
  (f : X.obj ≅ Y.obj) : X ≅ Y :=
{ hom := f.hom,
  inv := f.inv,
  hom_inv_id := f.hom_inv_id,
  inv_hom_id := f.inv_hom_id }


-- we show, that the subcategory FVec is still monoidal.
-- (In Mathlib it has already been shown that the category of R-modules is monoidal)
noncomputable instance : MonoidalCategory FVec where
  -- define the structure
  tensorObj X Y := ⟨X.obj ⊗ Y.obj, by {
    haveI := X.property
    haveI := Y.property
    let bX := Basis.ofVectorSpace ℝ X.obj
    let bY := Basis.ofVectorSpace ℝ Y.obj
    let b := bX.tensorProduct bY
    exact FiniteDimensional.of_fintype_basis b
  }⟩
  tensorHom f g := ModuleCat.monoidalCategory.tensorHom f g
  whiskerLeft (X : FVec) {Y Z : FVec} (f : Y ⟶ Z) :=
    ModuleCat.monoidalCategory.whiskerLeft X.obj f
  whiskerRight {X Y : FVec} (f : X ⟶ Y) Z :=
    ModuleCat.monoidalCategory.whiskerRight f Z.obj
  tensorUnit := ⟨𝟙_ (ModuleCat ℝ), by {
    exact FiniteDimensional.finiteDimensional_self ℝ
  }⟩

  associator X Y Z := isoMk (MonoidalCategory.associator (C := ModuleCat ℝ) X.obj Y.obj Z.obj)
  leftUnitor X := isoMk (MonoidalCategory.leftUnitor (C := ModuleCat ℝ) X.obj)
  rightUnitor X := isoMk (MonoidalCategory.rightUnitor (C := ModuleCat ℝ) X.obj)

  -- proof the properties
  tensorHom_def := by intros; apply ModuleCat.monoidalCategory.tensorHom_def
  tensor_id := by intros; apply ModuleCat.monoidalCategory.tensor_id
  tensor_comp := by intros; apply ModuleCat.monoidalCategory.tensor_comp
  whiskerLeft_id := by intros; apply ModuleCat.monoidalCategory.whiskerLeft_id
  id_whiskerRight := by intros; apply ModuleCat.monoidalCategory.id_whiskerRight
  associator_naturality := by intros; apply ModuleCat.monoidalCategory.associator_naturality
  leftUnitor_naturality := by intros; apply ModuleCat.monoidalCategory.leftUnitor_naturality
  rightUnitor_naturality := by intros; apply ModuleCat.monoidalCategory.rightUnitor_naturality
  pentagon := by intros; apply ModuleCat.monoidalCategory.pentagon
  triangle := by intros; apply ModuleCat.monoidalCategory.triangle
