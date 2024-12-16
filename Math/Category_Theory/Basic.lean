import Mathlib.Data.Set.Basic

class Category (Obj : Type u) := -- class (u) of objects
  (Hom : Obj → Obj → Type v) -- for two Objects, there is a class (v) of Morphisms
  (Comp : {A B C : Obj} → (Hom A B) → (Hom B C) → (Hom A C)) -- composition function
  (id : {A : Obj} → Hom A A) -- identity Morphism
  (assoc : {A B C D : Obj} →
    (f : Hom A B) → (g : Hom B C) → (h : Hom C D) →
    Comp (Comp f g) h = Comp f (Comp g h))  -- associativity
  (id_left : {A B : Obj} → (f : Hom A B) → Comp id f = f) -- identity laws
  (id_right : {A B : Obj} → (f : Hom A B) → Comp f id = f)


-- example: The Category of Sets
instance : Category (Type u) := {
  Hom := λ A B => A → B
  Comp := λ {_ _ _} f g => g ∘ f
  id := λ {_} => id
  assoc := λ {_ _ _ _} _ _ _ => rfl
  id_left := λ {_ _} _ => rfl
  id_right := λ {_ _} _ => rfl
}


-- definition of a isomorphism arrow
def IsIsomorphism {Obj : Type u} [Category Obj] {A B : Obj} (f : Category.Hom A B) : Prop :=
  ∃ inv : Category.Hom B A, -- there exists a inverse morphism 'inv'
  Category.Comp inv f = Category.id ∧
  Category.Comp f inv = Category.id


-- definition: two Objects are isomorphic, if there exists an Isomorphism
def AreIsomorphic {Obj : Type u} [Category Obj] {A B : Obj} :=
  ∃ iso : Category.Hom A B, -- the isomorphism
  IsIsomorphism iso


-- example: The isomorphisms in Set are exactly the bijections
theorem set_isomorphism_iff_bijective {A B : Type u} {f : Category.Hom A B} :
Function.Bijective f ↔ IsIsomorphism f := by {
  constructor
  -- bijective => isomorphism
  intro h
  simp [IsIsomorphism]
  rw [Function.bijective_iff_has_inverse] at h
  obtain ⟨g, h⟩ := h
  use g
  simp [Category.Comp, Category.id]
  rw [Function.leftInverse_iff_comp, Function.rightInverse_iff_comp] at h
  simp [h]

  -- isomorphism => bijective
  intro h
  rw [Function.bijective_iff_has_inverse]
  rw [IsIsomorphism] at h
  obtain ⟨inv, h⟩ := h
  use inv
  rw [Function.leftInverse_iff_comp, Function.rightInverse_iff_comp]
  simp [Category.Comp, Category.id] at h
  simp [h]
}


-- definition: dual/opposite Category
