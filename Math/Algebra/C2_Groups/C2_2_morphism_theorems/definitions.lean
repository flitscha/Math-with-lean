import Math.Algebra.C2_Groups.C2_1_Basics.theorems

-- definition of the homomorphism in the homomorphism-theorem
def quotient_homomorphism {G1 : Type u} {G2 : Type v} [MyGroup G1] [MyGroup G2]
(φ : GroupHomomorphism G1 G2) :
GroupHomomorphism (left_coset' G1 (ker_to_normal_subgroup φ)) G2 := {
  f := λ x => by {
    obtain ⟨g, _, _⟩ := x
    exact φ.f g
  }
  mul := by {
    intros a b
    simp
    rw [GroupHomomorphism.f]
    apply φ.mul
  }
}


def quotient_is_injective {G1 : Type u} {G2 : Type v} [MyGroup G1] [MyGroup G2]
{H : normal_subgroup G1} (φ : GroupHomomorphism (left_coset' G1 H) G2) : Prop :=
  ∀ a b : (left_coset' G1 H), a.carrier ≠ b.carrier -> φ.f a ≠ φ.f b


def quotient_is_isomorphism {G1 : Type u} {G2 : Type v} [MyGroup G1] [MyGroup G2]
{H : normal_subgroup G1} (φ : GroupHomomorphism (left_coset' G1 H) G2) : Prop :=
  Function.Surjective φ.f ∧ quotient_is_injective φ


-- isomorphism: G1/H -> G2
structure quotient_isomorphism (G1 : Type u) [MyGroup G1] (H : normal_subgroup G1)
(G2 : Type v) [MyGroup G2] extends GroupHomomorphism (left_coset' G1 H) G2 :=
  injective' : quotient_is_injective toGroupHomomorphism
  surjective : Function.Surjective f

-- G1/H is isomorphic to G2
def quotient_is_isomorphic_to (G1 : Type u) [MyGroup G1] (H : normal_subgroup G1)
(G2 : Type v) [MyGroup G2] : Prop :=
  ∃ φ : quotient_isomorphism G1 H G2, true


def list_prod {G : Type u} [MyGroup G] : List G -> G
| [] => MyGroup.one
| x :: xs => MyGroup.mul x (list_prod xs)


theorem list_prod_of_merged_list {G : Type u} [MyGroup G] (l1 : List G) (l2 : List G) :
list_prod (l1 ++ l2) = MyGroup.mul (list_prod l1) (list_prod l2) := by {
  cases l1
  case nil =>
    simp
    rw [list_prod]
    rw [MyGroup.one_mul]
  case cons x xs =>
    simp [list_prod]
    rw [list_prod_of_merged_list]
    rw [MyGroup.mul_assoc]
}


def list_inv {G : Type u} [MyGroup G] : List G -> List G
| [] => []
| x :: xs => list_inv xs ++ [(MyGroup.inv x)]


theorem list_inv_eq_inv {G : Type u} [MyGroup G] (l : List G) :
list_prod (list_inv l) = MyGroup.inv (list_prod l) := by {
  cases l
  case nil =>
    simp [list_inv, list_prod]
    rw [inv_one_lemma]
  case cons x xs =>
    simp [list_inv, list_prod]
    rw [list_prod_of_merged_list]
    rw [list_inv_eq_inv]
    simp [list_prod]
    rw [mul_inv_lemma]
    rw [MyGroup.mul_one]
}


theorem list_inv_of_merged_list {G : Type u} [MyGroup G] (l1 : List G) (l2 : List G) :
list_inv (l1 ++ l2) = (list_inv l2) ++ (list_inv l1) := by {
  cases l1
  case nil =>
    simp [list_inv]
  case cons x xs =>
    simp [list_inv]
    rw [list_inv_of_merged_list]
    simp
}


theorem list_inv_inv {G : Type u} [MyGroup G] (l : List G) :
list_inv (list_inv l) = l := by {
  cases l
  case nil =>
    simp [list_inv]
  case cons x xs =>
    simp [list_inv]
    rw [list_inv_of_merged_list]
    simp [list_inv]
    constructor
    rw [double_inv_lemma]
    apply list_inv_inv
}


theorem list_inv_mem {G : Type u} [MyGroup G] (l : List G) (g : G) :
g ∈ l -> MyGroup.inv g ∈ (list_inv l) := by {
  intro h
  cases l
  case nil =>
    simp at h
  case cons x xs =>
    simp [list_inv]
    simp at h
    cases h
    case inl h =>
      right
      rw [h]
    case inr h =>
      left
      apply list_inv_mem
      exact h
}


-- generated subgroups
def generated_group (G : Type u) [MyGroup G] (A : Set G) : Subgroup G := {
  carrier := { g | ∃ l : List G, (∀ x ∈ l, x ∈ A ∨ MyGroup.inv x ∈ A) ∧ (list_prod l) = g }
  nonempty := by {
    have : MyGroup.one ∈ {g | ∃ l, (∀ x ∈ l, x ∈ A ∨ MyGroup.inv x ∈ A) ∧ list_prod l = g} := by {
      simp
      use List.nil
      simp
      rw [list_prod]
    }
    contrapose! this
    rw [Set.eq_empty_iff_forall_not_mem] at this
    apply this
  }
  mul_mem := by {
    intros a b h
    obtain ⟨h_a, h_b⟩ := h
    simp at h_a h_b ⊢
    obtain ⟨l_a, h_a1, h_a2⟩ := h_a
    obtain ⟨l_b, h_b1, h_b2⟩ := h_b
    use l_a ++ l_b
    constructor
    intros x h
    simp at h
    cases h
    case inl h =>
      specialize h_a1 x
      simp [h] at h_a1
      exact h_a1
    case inr h =>
      specialize h_b1 x
      simp [h] at h_b1
      exact h_b1
    rw [list_prod_of_merged_list]
    rw [h_a2, h_b2]
  }
  inv_mem := by {
    intros a h
    simp at h ⊢
    obtain ⟨l, h1, h2⟩ := h
    use list_inv l

    constructor
    intro x
    intro h
    have : MyGroup.inv x ∈ l := by {
      apply list_inv_mem at h
      rw [list_inv_inv] at h
      exact h
    }
    specialize h1 (MyGroup.inv x)
    simp [this] at h1
    rw [double_inv_lemma] at h1
    cases h1
    case inl h1 =>
      right
      apply h1
    case inr h1 =>
      left
      apply h1

    rw [list_inv_eq_inv]
    rw [h2]
  }
}


-- cyclic groups: a generated group, where the generator-set has only one element
def cyclic_group (G : Type u) [MyGroup G] (g : G) : Subgroup G :=
  generated_group G {g}
