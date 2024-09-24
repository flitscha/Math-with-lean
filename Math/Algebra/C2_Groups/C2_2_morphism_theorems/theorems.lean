import Math.Algebra.C2_Groups.C2_2_morphism_theorems.definitions

-- Theorem 2.2.1 (Homomorphism theorem)

-- the quotient homomorphism is well-defined:
theorem quotient_homomorphism_welldefined_lemma (G1 G2 : Type)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2)
(a b : left_coset' G1 (ker_to_normal_subgroup φ)) :
a.carrier = b.carrier ->
(quotient_homomorphism φ).f a = (quotient_homomorphism φ).f b := by {
  intro h
  rw [GroupHomomorphism.f]
  rw [quotient_homomorphism]
  simp

  obtain ⟨g_a, a_carrier, h_a_carrier⟩ := a
  obtain ⟨g_b, b_carrier, h_b_carrier⟩ := b
  simp at h
  simp
  rw [h] at h_a_carrier
  rw [h_a_carrier] at h_b_carrier
  clear h h_a_carrier a_carrier

  -- left cosets are equal -> g_a⁻¹ * g_b ∈ Ker φ
  rw [left_coset_eq_lemma] at h_b_carrier
  rw [ker_to_normal_subgroup, normal_sg_to_sg] at h_b_carrier
  simp at h_b_carrier
  rw [ker] at h_b_carrier
  simp at h_b_carrier
  rw [GroupHomomorphism.mul] at h_b_carrier
  symm
  have : MyGroup.one = MyGroup.mul (φ.1 (MyGroup.inv g_a)) (φ.1 g_a) := by {
    rw [homomorphism_inverse_element_lemma]
    rw [MyGroup.inv_mul]
  }
  rw [this] at h_b_carrier
  rw [← group_cancel_rule_left_lemma] at h_b_carrier
  exact h_b_carrier
}


-- the quotient homomorphism is injective:
-- here we can't use the standard definition of injective, because of the
-- definition of left_coset'
theorem quotient_homomorphism_injective_lemma (G1 G2 : Type)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2) :
quotient_is_injective (quotient_homomorphism φ) := by {
  rw [quotient_is_injective]
  intros a b
  intro h
  rw [GroupHomomorphism.f, quotient_homomorphism]
  obtain ⟨g_a, a_carrier, h_a_carrier⟩ := a
  obtain ⟨g_b, b_carrier, h_b_carrier⟩ := b
  simp at h ⊢
  contrapose! h
  rw [h_a_carrier, h_b_carrier]
  rw [left_coset_eq_lemma]
  rw [ker_to_normal_subgroup, normal_sg_to_sg]
  simp
  rw [ker]
  simp
  rw [GroupHomomorphism.mul, homomorphism_inverse_element_lemma, h]
  rw [MyGroup.inv_mul]
}


-- G/ker(φ) is isomorphic to im(φ)
-- also here, the definition of G/H is a problem
theorem quotient_isomorphism_lemma {G1 G2 : Type}
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2) :
quotient_is_isomorphic_to G1 (ker_to_normal_subgroup φ) (image_to_subgroup φ).carrier := by {

  let ψ2 : GroupHomomorphism (left_coset' G1 (ker_to_normal_subgroup φ)) G2 := quotient_homomorphism φ
  have h : im ψ2 = im φ := by {
    simp [ψ2]
    rw [quotient_homomorphism]
    simp [im]
    ext x
    constructor
    simp
    intro c h
    obtain ⟨g_c, _⟩ := c
    use g_c
    simp
    intros g h
    let g_1 : left_coset' G1 (ker_to_normal_subgroup φ) := {
      g := g
      carrier := left_coset G1 (ker_to_normal_subgroup φ) g
      h_carrier := by simp
    }
    use g_1
  }
  let ψ3 : GroupHomomorphism (left_coset' G1 (ker_to_normal_subgroup φ)) (im φ) := {
    f := λ x => by {
      have : ψ2.f x ∈ im φ := by {
        rw [← h]
        rw [im]
        simp
      }
      use ψ2.f x
    }
    mul := by {
      simp
      intros a b
      simp [GroupHomomorphism.f, MyGroup.mul]
      apply GroupHomomorphism.mul
    }
  }
  let ψ4 : quotient_isomorphism G1 (ker_to_normal_subgroup φ) ↑(im φ) := {
    toGroupHomomorphism := ψ3
    injective' := by {
      have : quotient_is_injective (quotient_homomorphism φ) := by {
        apply quotient_homomorphism_injective_lemma
      }
      simp [ψ3, ψ2]
      rw [quotient_is_injective]
      rw [GroupHomomorphism.f]
      simp
      apply this
    }
    surjective := by {
      rw [Function.Surjective]
      simp
      intros a h_a
      rw [GroupHomomorphism.f]
      simp [ψ3]
      rw [GroupHomomorphism.f]
      simp [ψ2, quotient_homomorphism]
      simp [im] at h_a
      obtain ⟨g_a, h_a⟩ := h_a
      let a_1 : left_coset' G1 (ker_to_normal_subgroup φ) := {
        g := g_a
        carrier := left_coset G1 (ker_to_normal_subgroup φ) g_a
        h_carrier := by simp
      }
      use a_1
      rw [h_a]
    }
  }

  rw [quotient_is_isomorphic_to]
  use ψ4
}


theorem cyclic_group_isomorphic_to_Z {G : Type} [MyGroup G] (g : G)
(C : Subgroup G) (h_c : C = cyclic_group G g) :
∃ n : ℤ, quotient_is_isomorphic_to ℤ (nZ n) C.carrier := by {

  let φ : GroupHomomorphism ℤ G := {
    f := λ z => group_pow g z
    mul := by {
      intros a b
      simp [MyGroup.mul]
      rw [pow_sum_lemma]
    }
  }

  -- im(φ) = ⟨g⟩
  have h_im : (image_to_subgroup φ).carrier = C.carrier := by {
    rw [image_to_subgroup]
    simp
    rw [im]
    simp [GroupHomomorphism.f]
    rw [← cyclic_group_carrier_lemma]
    rw [h_c]
  }

  -- ker(φ) = nZ (because every subgroup of Z is nZ)
  have h_ker' : ∃ n : ℤ, ker_to_normal_subgroup φ = normal_sg_to_sg (nZ n) := by {
    apply lemma_2_1_5
  }
  obtain ⟨n, h_ker'⟩ := h_ker'

  have h_ker : (nZ n) = ker_to_normal_subgroup φ := by {
    rw [ker_to_normal_subgroup]
    rw [nZ]
    simp
    simp [normal_sg_to_sg] at h_ker'
    simp [ker_to_normal_subgroup, nZ] at h_ker'
    symm
    apply h_ker'
  }
  clear h_ker'

  use n
  have : quotient_is_isomorphic_to ℤ (ker_to_normal_subgroup φ) (image_to_subgroup φ).carrier := by {
    apply quotient_isomorphism_lemma
  }

  symm at h_im
  rw [← h_ker] at this
  have hhhh : C = image_to_subgroup φ := by {
    obtain ⟨c_carrier, c_nonempty, c_mul_mem, c_inv_mem⟩ := C
    rw [image_to_subgroup]
    simp at h_im ⊢
    rw [image_to_subgroup] at h_im
    simp at h_im
    exact h_im
  }

  rw [← hhhh] at this
  exact this
}


section isomorphism_theorem
variable {G : Type} [MyGroup G] {H : Subgroup G} {N : normal_subgroup G}

-- i)
-- HN := { h*n, h ∈ H, n ∈ N } is a subgroup of G
def HN (H : Subgroup G) (N : normal_subgroup G) : Subgroup G := {
  carrier := { x | ∃ h n : G, h ∈ H.carrier ∧ n ∈ N.carrier ∧ x = MyGroup.mul h n }
  nonempty := by {
    have : MyGroup.one ∈ { x | ∃ h n : G, h ∈ H.carrier ∧ n ∈ N.carrier ∧ x = MyGroup.mul h n } := by {
      simp
      use MyGroup.one
      constructor
      apply subgroup_contains_one_lemma
      use MyGroup.one
      constructor
      apply subgroup_contains_one_lemma
      rw [MyGroup.mul_one]
    }
    contrapose! this
    rw [Set.eq_empty_iff_forall_not_mem] at this
    apply this
  }
  mul_mem := by {
    intros a b h
    obtain ⟨h_a, h_b⟩ := h
    simp at h_a h_b ⊢
    obtain ⟨ha, h_ha, na, h_na, h_a⟩ := h_a
    obtain ⟨hb, h_hb, nb, h_nb, h_b⟩ := h_b

    -- use that N is normal
    have h_normal : MyGroup.mul (MyGroup.mul (MyGroup.inv hb) na) hb ∈ N.carrier := by {
      obtain ⟨N_SG, N_normal⟩ := N
      rw [normal_iff_lemma] at N_normal
      simp at h_na
      specialize N_normal ⟨na, h_na⟩ hb
      exact N_normal
    }

    use MyGroup.mul ha hb
    constructor
    apply Subgroup.mul_mem
    exact ⟨h_ha, h_hb⟩
    use MyGroup.mul (MyGroup.mul (MyGroup.mul (MyGroup.inv hb) na) hb) nb
    constructor
    apply Subgroup.mul_mem
    exact ⟨h_normal, h_nb⟩
    repeat rw [← MyGroup.mul_assoc]
    nth_rewrite 4 [MyGroup.mul_assoc]
    rw [MyGroup.mul_inv]
    rw [MyGroup.mul_one]
    rw [MyGroup.mul_assoc]
    rw [h_a, h_b]
  }
  inv_mem := by {
    intros a h_a
    simp at h_a ⊢
    obtain ⟨ha, h_ha, na, h_na, h_a⟩ := h_a

    -- we use that N is normal again
    have h_normal : MyGroup.mul (MyGroup.mul ha (MyGroup.inv na)) (MyGroup.inv ha) ∈ N.carrier := by {
      have : MyGroup.mul (MyGroup.mul ha (MyGroup.inv na)) (MyGroup.inv ha) =
            MyGroup.inv (MyGroup.mul (MyGroup.mul ha na) (MyGroup.inv ha)) := by {
        repeat rw [mul_inv_lemma]
        rw [double_inv_lemma]
        repeat rw [MyGroup.mul_assoc]
      }
      rw [this]
      apply Subgroup.inv_mem
      obtain ⟨N_SG, N_normal⟩ := N
      simp
      rw [normal_iff_lemma] at N_normal
      specialize N_normal ⟨na, h_na⟩ (MyGroup.inv ha)
      simp at N_normal
      rw [double_inv_lemma] at N_normal
      exact N_normal
    }
    use (MyGroup.inv ha)
    constructor
    apply Subgroup.inv_mem
    exact h_ha
    use MyGroup.mul (MyGroup.mul ha (MyGroup.inv na)) (MyGroup.inv ha)
    constructor
    exact h_normal
    repeat rw [← MyGroup.mul_assoc]
    rw [MyGroup.inv_mul, MyGroup.one_mul]
    rw [h_a]
    rw [mul_inv_lemma]
  }
}


-- ii) N is a normal Subgroup of HN
def N' (H : Subgroup G) (N : normal_subgroup G) : normal_subgroup (HN H N).carrier := {
  carrier := { x : ↑(HN H N).carrier | ∃ g : G, g = x ∧ g ∈ N.carrier }
  nonempty := sorry
  mul_mem := sorry
  inv_mem := sorry
  normal := sorry
}


-- ii) H ∩ N is a normal Subgroup of N
def H_inter_N (H : Subgroup G) (N : normal_subgroup G) : normal_subgroup H.carrier := {
  carrier := { h : H.carrier | ∃ g : G, h = g ∧ g ∈ N.carrier }
  nonempty := sorry
  mul_mem := sorry
  inv_mem := sorry
  normal := sorry
}


-- iii) H/(H ∩ N) ≅ HN/N
theorem isomorphism_theorem_1 :
quotient_is_isomorphic_to H.carrier (H_inter_N H N)
(left_coset' (HN H N).carrier (N' H N)) := by {
  -- we need a better way to use homomorphisms between quotient-groups.
  sorry
}

/-
theorem isomorphism_theorem1_i {G : Type} [MyGroup G] (H : Subgroup G)
(N : normal_subgroup G) :
∃ S : Subgroup G, S.carrier =
{ x | ∃ h n : G, h ∈ H.carrier ∧ n ∈ N.carrier ∧ x = MyGroup.mul h n } := by {
  let HN : Set G := { x | ∃ h n : G, h ∈ H.carrier ∧ n ∈ N.carrier ∧ x = MyGroup.mul h n }

  -- HN is not empty:
  have h_nonempty : HN ≠ ∅ := by {
    simp [HN]
    rw [Set.eq_empty_iff_forall_not_mem]
    simp
    use MyGroup.one, MyGroup.one
    constructor
    apply subgroup_contains_one_lemma
    use MyGroup.one
    constructor
    apply subgroup_contains_one_lemma
    rw [MyGroup.mul_one]
  }

  -- a b ∈ HN -> a*b ∈ HN
  have h_mul_mem : ∀ (a b : G), a ∈ HN ∧ b ∈ HN → MyGroup.mul a b ∈ HN := by {
    intros a b h
    obtain ⟨h_a, h_b⟩ := h
    simp [HN] at h_a h_b ⊢
    obtain ⟨ha, h_ha, na, h_na, h_a⟩ := h_a
    obtain ⟨hb, h_hb, nb, h_nb, h_b⟩ := h_b

    -- use that N is normal
    have h_normal : MyGroup.mul (MyGroup.mul (MyGroup.inv hb) na) hb ∈ N.carrier := by {
      obtain ⟨N_SG, N_normal⟩ := N
      rw [normal_iff_lemma] at N_normal
      simp at h_na
      specialize N_normal ⟨na, h_na⟩ hb
      exact N_normal
    }

    use MyGroup.mul ha hb
    constructor
    apply Subgroup.mul_mem
    exact ⟨h_ha, h_hb⟩
    use MyGroup.mul (MyGroup.mul (MyGroup.mul (MyGroup.inv hb) na) hb) nb
    constructor
    apply Subgroup.mul_mem
    exact ⟨h_normal, h_nb⟩
    repeat rw [← MyGroup.mul_assoc]
    nth_rewrite 4 [MyGroup.mul_assoc]
    rw [MyGroup.mul_inv]
    rw [MyGroup.mul_one]
    rw [MyGroup.mul_assoc]
    rw [h_a, h_b]
  }

  -- a ∈ HN -> a⁻¹ ∈ HN
  have h_inv_mem : ∀ a ∈ HN, MyGroup.inv a ∈ HN := by {
    intros a h_a
    simp [HN] at h_a ⊢
    obtain ⟨ha, h_ha, na, h_na, h_a⟩ := h_a

    -- we use that N is normal again
    have h_normal : MyGroup.mul (MyGroup.mul ha (MyGroup.inv na)) (MyGroup.inv ha) ∈ N.carrier := by {
      have : MyGroup.mul (MyGroup.mul ha (MyGroup.inv na)) (MyGroup.inv ha) =
            MyGroup.inv (MyGroup.mul (MyGroup.mul ha na) (MyGroup.inv ha)) := by {
        repeat rw [mul_inv_lemma]
        rw [double_inv_lemma]
        repeat rw [MyGroup.mul_assoc]
      }
      rw [this]
      apply Subgroup.inv_mem
      obtain ⟨N_SG, N_normal⟩ := N
      simp
      rw [normal_iff_lemma] at N_normal
      specialize N_normal ⟨na, h_na⟩ (MyGroup.inv ha)
      simp at N_normal
      rw [double_inv_lemma] at N_normal
      exact N_normal
    }

    use (MyGroup.inv ha)
    constructor
    apply Subgroup.inv_mem
    exact h_ha
    use MyGroup.mul (MyGroup.mul ha (MyGroup.inv na)) (MyGroup.inv ha)
    constructor
    exact h_normal
    repeat rw [← MyGroup.mul_assoc]
    rw [MyGroup.inv_mul, MyGroup.one_mul]
    rw [h_a]
    rw [mul_inv_lemma]
  }

  let S : Subgroup G := {
    carrier := HN
    nonempty := h_nonempty
    mul_mem := h_mul_mem
    inv_mem := h_inv_mem
  }

  use S
}
-/

/-
theorem isomorphism_theorem1_ii_1 {G : Type u} [MyGroup G] (H : Subgroup G)
(N : normal_subgroup G) :
∃ S : normal_subgroup H.carrier, S.carrier = H.carrier ∩ N.carrier := by {
  sorry
}

theorem isomorphism_theorem1_ii_2 {G : Type u} [MyGroup G] (H : Subgroup G)
(N : normal_subgroup G) :
∃ S : normal_subgroup G, S.carrier =
-/

/-
def normal_subgroup_of_H_inter_N {G : Type} [MyGroup G] (H : Subgroup G) (N : normal_subgroup G) :
SubgroupOfSubgroup H := {
  carrier := { h : G | h ∈ N.carrier ∧ h ∈ H.carrier}

  nonempty := by {
    sorry
  }
  mul_mem := sorry
  inv_mem := sorry
  h_carrier := by simp
}-/

/-
def normal_subgroup_of_H_inter_N {G : Type} [MyGroup G] {H : Subgroup G} {N : normal_subgroup G} :
normal_subgroup H.carrier := {
  carrier := by {
    exact { h : H.carrier | ∃ g : G, g = h ∧ g ∈ N.carrier }
  }
  nonempty := by {
    sorry
  }
  mul_mem := sorry
  inv_mem := sorry
  normal := sorry
}

--def exists_normal_subgroup_in_H {G : Type u} [MyGroup G] (H : Subgroup G) (N : normal_subgroup G) :
--  ∃ H_N : normal_subgroup H.carrier, H_N.carrier = {h ∈ H.carrier | h ∈ N.carrier} :=

theorem isomorphism_theorem1_iii {G : Type} [MyGroup G] (H : Subgroup G)
(N : normal_subgroup G) :

quotient_is_isomorphic_to H.carrier normal_subgroup_of_H_inter_N
(left_coset' HN.carrier N )

-/

end isomorphism_theorem
