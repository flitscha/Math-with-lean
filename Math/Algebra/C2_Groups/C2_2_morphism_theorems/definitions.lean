import Math.Algebra.C2_Groups.C2_2_morphism_theorems.lists


-- definition of the homomorphism in the homomorphism-theorem
def quotient_homomorphism {G1 G2 : Type} [MyGroup G1] [MyGroup G2]
(φ : GroupHomomorphism G1 G2) :
GroupHomomorphism (quotient_group G1 (ker_to_normal_subgroup φ)) G2 := {
  f := by {
    apply Quotient.lift (λ g : G1 => φ.f g)
    -- we show, that the definition is welldefined
    intros a b
    intro h
    simp [HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, left_coset_setoid, left_coset_rel] at h
    obtain ⟨k, h_k, h⟩ := h
    rw [h]
    rw [GroupHomomorphism.mul]
    have : (GroupHomomorphism.f k) = MyGroup.one := by {
      simp [ker_to_normal_subgroup] at h_k
      simp [ker] at h_k
      exact h_k
    }
    rw [this]
    rw [MyGroup.mul_one]
  }

  mul := by {
    intros a b
    let g_a : G1 := quotient_to_repr a
    have h_a : ⟦g_a⟧ = a := by {
      simp [g_a]
      apply repr_lemma
    }
    let g_b : G1 := quotient_to_repr b
    have h_b : ⟦g_b⟧ = b := by {
      simp [g_b]
      apply repr_lemma
    }
    rw [← h_a, ← h_b]
    simp
    simp [MyGroup.mul]
    simp [quotient_group_mul]
    rw [GroupHomomorphism.mul]
  }
}


-- generated subgroups
def generated_group (G : Type) [MyGroup G] (A : Set G) : Subgroup G := {
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
def cyclic_group (G : Type) [MyGroup G] (g : G) : Subgroup G :=
  generated_group G {g}


theorem cyclic_group_carrier_lemma (G : Type) [MyGroup G] (g : G) :
(cyclic_group G g).carrier = { x | ∃ z : ℤ, x = group_pow g z } := by {
  ext x
  simp
  constructor
  intro h
  simp [cyclic_group, generated_group] at h
  obtain ⟨l, h1, h2⟩ := h
  rw [← h2]
  clear h2
  induction l
  case nil =>
    simp [list_prod]
    use 0
    simp [group_pow, group_pow_nat]
  case cons y ys h_ys =>
    rw [list_prod]
    simp at h1
    obtain ⟨h1_1, h1_2⟩ := h1
    have : ∃ z : ℤ, list_prod ys = group_pow g z := by {
      apply h_ys
      exact h1_2
    }
    clear h_ys
    obtain ⟨z_ys, h_ys⟩ := this
    cases h1_1
    case inl h =>
      use z_ys+1
      rw [h_ys]
      rw [pow_add_one_lemma]
      rw [h]
      rw [pow_comm_aux]
    case inr h =>
      use z_ys-1
      rw [sub_eq_add_neg]
      rw [pow_sum_lemma]
      rw [h_ys]
      rw [pow_comm_lemma]
      have : (group_pow g (-1)) = y := by {
        have : -1 = Int.negSucc 0 := by simp
        rw [this]
        simp [group_pow, group_pow_nat]
        rw [MyGroup.mul_one]
        rw [← h]
        rw [double_inv_lemma]
      }
      rw [this]

  -- ⊆
  intro h
  obtain ⟨z, h⟩ := h
  rw [cyclic_group, generated_group]
  simp
  cases z
  case ofNat n =>
    use List.replicate n g
    simp
    rw [h]
    clear h
    induction n
    case zero =>
      simp [list_prod]
      simp [group_pow, group_pow_nat]
    case succ n' h_n =>
      simp [list_prod]
      rw [h_n]
      norm_cast
  case negSucc n' =>
    use List.replicate (n'+1) (MyGroup.inv g)
    simp
    constructor
    right
    rw [double_inv_lemma]
    rw [h]
    clear h
    induction n'
    case zero =>
      simp [list_prod]
      rw [MyGroup.mul_one]
      have : (-1) = Int.negSucc 0 := by simp
      rw [this]
      simp [group_pow, group_pow_nat]
      rw [MyGroup.mul_one]
    case succ n'' h_n =>
      rw [List.replicate, list_prod]
      rw [h_n]
      clear h_n

      simp [Int.negSucc_eq]
      nth_rewrite 2 [pow_sum_lemma]

      rw [pow_neg_one_eq_inv]
}
