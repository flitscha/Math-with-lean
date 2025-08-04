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


-- the Category of finite dimensional, real vector sapces
structure FVec where
  carrier : Type u
  [add_comm_group : AddCommGroup carrier]
  [module : Module ℝ carrier]
  [finite_dimensional : FiniteDimensional ℝ carrier]


attribute [instance] FVec.add_comm_group FVec.module FVec.finite_dimensional

-- CoeSort for simpler notation. (now we can use V : FVec)
instance : CoeSort FVec (Type u) := ⟨FVec.carrier⟩


def FVec.hom (V W : FVec) := V →ₗ[ℝ] W

-- FVec is a category
instance : Category FVec where
  Hom := FVec.hom
  id V := LinearMap.id
  comp f g := g.comp f


-- now we want to make FVec to a monoidal category

-- we define the tensorproduct on objects first
noncomputable def FVec.tensorObj (X Y : FVec) : FVec :=
{ carrier := X ⊗[ℝ] Y,
  add_comm_group := inferInstance,
  module := inferInstance,
  finite_dimensional := inferInstance
}

-- tensorproduct on hom-sets
noncomputable def FVec.tensorHom {X₁ X₂ Y₁ Y₂ : FVec}
  (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : FVec.tensorObj X₁ Y₁ ⟶ FVec.tensorObj X₂ Y₂ :=
TensorProduct.map f g

-- define the unit
noncomputable def FVec.unit : FVec :=
{ carrier := ℝ,
  add_comm_group := inferInstance,
  module := inferInstance,
  finite_dimensional := by infer_instance
}

-- (f : X ⟶ Y)   ↦  (f ⨂ id : X ⊗ Z ⟶ Y ⊗ Z)
noncomputable def whiskerRight_FVec {X Y : FVec} (f : X ⟶ Y) (Z : FVec) :
FVec.tensorObj X Z ⟶ FVec.tensorObj Y Z := TensorProduct.map f (LinearMap.id)

-- (g : Y ⟶ Z)  ↦   (id ⊗ g : X ⊗ Y ⟶ X ⊗ Z)
noncomputable def whiskerLeft_FVec (X : FVec) {Y Z : FVec} (g : Y ⟶ Z) :
FVec.tensorObj X Y ⟶ FVec.tensorObj X Z := TensorProduct.map (LinearMap.id) g


noncomputable def associatorIso (X Y Z : FVec) :
  (FVec.tensorObj (FVec.tensorObj X Y) Z) ≅ (FVec.tensorObj X (FVec.tensorObj Y Z)) :=
{ hom := (TensorProduct.assoc ℝ X.carrier Y.carrier Z.carrier).toLinearMap,
  inv := (TensorProduct.assoc ℝ X.carrier Y.carrier Z.carrier).symm.toLinearMap,
  hom_inv_id := by {
    sorry
  },
  inv_hom_id := by {
    sorry
  }
}


noncomputable def leftUnitorIso (X : FVec) :
  FVec.tensorObj FVec.unit X ≅ X :=
{ hom := (TensorProduct.lid ℝ X.carrier).toLinearMap,
  inv := (TensorProduct.lid ℝ X.carrier).symm.toLinearMap,
  hom_inv_id := by {
    simp [TensorProduct.lid]
    simp [FVec.unit]
    sorry
  },
  inv_hom_id := by {
    sorry
  }
}

noncomputable def rightUnitorIso (X : FVec) :
  FVec.tensorObj X FVec.unit ≅ X :=
{ hom := (TensorProduct.rid ℝ X.carrier).toLinearMap,
  inv := (TensorProduct.rid ℝ X.carrier).symm.toLinearMap,
  hom_inv_id := by sorry--ext; apply LinearEquiv.left_inv,
  inv_hom_id := by sorry--ext; apply LinearEquiv.right_inv
}



-- simp-lemmas
@[simp]
lemma tensorHom_apply {X₁ Y₁ X₂ Y₂ : FVec} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  FVec.tensorHom f g = TensorProduct.map f g := by
  rfl

@[simp]
lemma whiskerRight_FVec_apply {X Y Z : FVec} (f : X ⟶ Y) :
  whiskerRight_FVec f Z = TensorProduct.map f (LinearMap.id) := by rfl

@[simp]
lemma whiskerLeft_FVec_apply {X Y Z : FVec} (g : Y ⟶ Z) :
  whiskerLeft_FVec X g = TensorProduct.map (LinearMap.id) g := by rfl

@[simp]
lemma tensorHom_id {X Y : FVec} :
  FVec.tensorHom (LinearMap.id : X ⟶ X) (LinearMap.id : Y ⟶ Y) = LinearMap.id := by sorry
  --simp [tensorHom_apply, TensorProduct.map_id]

@[simp]
lemma whiskerRight_id {X Y : FVec} :
  whiskerRight_FVec (LinearMap.id : X ⟶ X) Y = LinearMap.id := by
  simp [whiskerLeft_FVec_apply, TensorProduct.map_id]

@[simp]
lemma whiskerLeft_id {X Y : FVec} :
  whiskerLeft_FVec X (LinearMap.id : Y ⟶ Y) = LinearMap.id := by
  simp [whiskerRight_FVec_apply, TensorProduct.map_id]

@[simp]
lemma tensorHom_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : FVec}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
  FVec.tensorHom (g₁.comp f₁) (g₂.comp f₂) = (FVec.tensorHom g₁ g₂).comp (FVec.tensorHom f₁ f₂) := by
  simp [tensorHom_apply]
  -- TensorProduct.map (g₁.comp f₁) (g₂.comp f₂) = TensorProduct.map g₁ g₂ ≫ TensorProduct.map f₁ f₂
  --exact TensorProduct.map_comp g₁ g₂ f₁ f₂
  sorry

@[simp]
lemma whiskerLeft_comp {X Y₁ Y₂ Z : FVec} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Z) :
  (whiskerLeft_FVec X g).comp (whiskerLeft_FVec X f) = whiskerLeft_FVec X (g.comp f) := by
  simp [whiskerLeft_FVec_apply]
  --exact TensorProduct.map_comp (LinearMap.id) g (LinearMap.id) f
  sorry

@[simp]
lemma whiskerRight_comp {X₁ X₂ Y Z : FVec} (f : X₁ ⟶ X₂) (g : X₂ ⟶ Y) :
  (whiskerRight_FVec g Z).comp (whiskerRight_FVec f Z) = whiskerRight_FVec (g.comp f) Z := by
  simp [whiskerRight_FVec_apply]
  --exact TensorProduct.map_comp (LinearMap.id) g (LinearMap.id) f
  sorry



/-
-- we show, that the tensorproduct makes FVec to a monoidal category
noncomputable instance : MonoidalCategory FVec where
  tensorObj := FVec.tensorObj
  tensorHom := @FVec.tensorHom
  whiskerLeft := @whiskerLeft_FVec
  whiskerRight := @whiskerRight_FVec
  tensorUnit := FVec.unit

  associator X Y Z := associatorIso X Y Z
  leftUnitor X := leftUnitorIso X
  rightUnitor X := rightUnitorIso X

  pentagon := by {
    intro W X Y Z

    sorry
    --aesop_cat
  }
  triangle := by {
    sorry--aesop_cat
  }
-/



/-
-- the dual-functor. V ↦ Lin(V, ℝ)
def starFunctor : FVecᵒᵖ ⥤ FVec := {
  obj := fun V => ModuleCat.of ℝ (Module.Dual ℝ V.unop),

  map := fun f => ModuleCat.ofHom (f.unop).dualMap,

  map_id := by {
    intro X
    rfl
  },

  map_comp := by {
    intros X Y Z f g
    simp
    rfl
  }
}



noncomputable def duality_equiv (A B C : FVec) :
(A ⊗ B ⟶ C) ≃ (A ⟶ starFunctor.obj (op (B ⊗ (starFunctor.obj (op C))))) := by {
  -- Hier müsste man Tensor-Hom-Isos kombinieren + Dualität
  -- Für jetzt axiomatisch:
  classical
  refine
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := by intro; sorry
      right_inv := by intro; sorry
    }
}


theorem starFunctor_is_full : Functor.Full starFunctor := by {
  simp [starFunctor]

}


noncomputable instance : StarAutonomousCategory FVec := {
  toStarAutonomousCategoryStruct := {
    starFunctor := starFunctor,
    duality_equiv := duality_equiv
  }
  full_star := sorry
  faithful_star := sorry
  naturality_a := by intro; sorry
  naturality_b := by intro; sorry
  naturality_c := by intro; sorry
}
-/
