import Math.Algebra.C2_Groups.C2_2_morphism_theorems.definitions

-- Theorem 2.2.1 (Homomorphism theorem)

theorem quotient_homomorphism_injective_lemma (G1 G2 : Type)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2) :
Function.Injective (quotient_homomorphism φ).f := by {
  rw [Function.Injective]
  intros a b
  intro h
  -- get representatives of a and b
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

  rw [← h_a, ← h_b] at h ⊢
  rw [GroupHomomorphism.f] at h
  simp [quotient_homomorphism] at h

  apply Quot.eq.mpr
  simp [Setoid.r]
  constructor
  rw [left_coset_rel]
  use MyGroup.mul (MyGroup.inv g_b) g_a
  constructor
  simp [ker_to_normal_subgroup, ker]
  rw [GroupHomomorphism.mul]
  rw [h]
  rw [homomorphism_inverse_element_lemma]
  rw [MyGroup.inv_mul]
  rw [← MyGroup.mul_assoc]
  rw [MyGroup.mul_inv, MyGroup.one_mul]
}



-- G/ker(φ) is isomorphic to im(φ)
theorem homomorphism_theorem {G1 G2 : Type} [MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2) :
groupsAreIsomorphic (quotient_group G1 (ker_to_normal_subgroup φ)) (image_to_subgroup φ).carrier := by {
  rw [groupsAreIsomorphic]

  let ψ1 : GroupHomomorphism (quotient_group G1 (ker_to_normal_subgroup φ)) G2 := quotient_homomorphism φ

  have h : im ψ1 = im φ := by {
    simp [ψ1]
    rw [quotient_homomorphism]
    simp [im]
    ext x
    -- ⊆
    constructor
    simp
    intro c
    let g_c : G1 := quotient_to_repr c
    have h_a : ⟦g_c⟧ = c := by {
      simp [g_c]
      apply repr_lemma
    }
    simp [← h_a]
    intro h
    use g_c

    -- other direction
    simp
    intros c h
    use ⟦c⟧
    simp
    exact h
  }

  let ψ2 : GroupHomomorphism (quotient_group G1 (ker_to_normal_subgroup φ)) (image_to_subgroup φ).carrier := {
    f := λ x => by {
      have : ψ1.f x ∈ im φ := by {
        rw [← h]
        rw [im]
        simp
      }
      use ψ1.f x
      apply this
    }
    mul := by {
      simp
      intros a b
      simp [MyGroup.mul]
      have : (quotient_group_mul (ker_to_normal_subgroup φ) a b) =
            MyGroup.mul a b := by {
        simp [MyGroup.mul]
      }
      rw [this]
      rw [GroupHomomorphism.mul]
    }
  }

  let ψ3 : GroupIsomorphism (quotient_group G1 (ker_to_normal_subgroup φ)) (image_to_subgroup φ).carrier := {
    toGroupHomomorphism := ψ2
    injective := by {
      have : Function.Injective ψ1.f := by {
        apply quotient_homomorphism_injective_lemma
      }
      simp [GroupHomomorphism.f]
      simp [Function.Injective]
      apply this
    }
    surjective := by {
      rw [Function.Surjective]
      simp
      intros a h_a
      rw [GroupHomomorphism.f]
      simp [ψ2]
      rw [GroupHomomorphism.f]
      simp [ψ1]

      simp [image_to_subgroup, im] at h_a
      obtain ⟨g_a, h_a⟩ := h_a
      use ⟦g_a⟧
      simp [quotient_homomorphism]
      rw [h_a]
    }
  }
  use ψ3
}



-- every cyclic group is isomorphic to Z/nZ for a n ∈ ℤ
theorem cyclic_group_isomorphic_to_Z {G : Type} [MyGroup G] (g : G)
(C : Subgroup G) (h_c : C = cyclic_group G g) :
∃ n : ℤ, groupsAreIsomorphic (quotient_group ℤ (nZ n)) C.carrier := by {

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

  have : groupsAreIsomorphic (quotient_group ℤ (ker_to_normal_subgroup φ)) (image_to_subgroup φ).carrier := by {
    apply homomorphism_theorem
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


-- first isomorphic theorem
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
  nonempty := by {
    have : MyGroup.one ∈ { x : ↑(HN H N).carrier | ∃ g : G, g = x ∧ g ∈ N.carrier } := by {
      simp
      apply subgroup_contains_one_lemma
    }
    contrapose! this
    rw [Set.eq_empty_iff_forall_not_mem] at this
    apply this
  }
  mul_mem := by {
    intros a b h
    simp at h ⊢
    apply Subgroup.mul_mem
    exact h
  }
  inv_mem := by {
    intros a h
    simp at h ⊢
    apply Subgroup.inv_mem
    apply h
  }
  normal := by {
    rw [normal_iff_lemma]
    simp
    intros a h_a h_a'
    intros g h_g
    -- we use that N is normal
    obtain ⟨N, N_normal⟩ := N
    rw [normal_iff_lemma] at N_normal
    specialize N_normal ⟨a, h_a'⟩ g
    apply N_normal
  }
}


-- ii) H ∩ N is a normal Subgroup of N
def H_inter_N (H : Subgroup G) (N : normal_subgroup G) : normal_subgroup H.carrier := {
  carrier := { h : H.carrier | ∃ g : G, h = g ∧ g ∈ N.carrier }
  nonempty := by {
    have : MyGroup.one ∈ { h : H.carrier | ∃ g : G, h = g ∧ g ∈ N.carrier } := by {
      simp
      apply subgroup_contains_one_lemma
    }
    contrapose! this
    rw [Set.eq_empty_iff_forall_not_mem] at this
    apply this
  }
  mul_mem := by {
    intros a b
    simp
    intros h_a h_b
    apply Subgroup.mul_mem
    exact ⟨h_a, h_b⟩
  }
  inv_mem := by {
    intro a
    simp
    intro h
    apply Subgroup.inv_mem
    exact h
  }
  normal := by {
    rw [normal_iff_lemma]
    simp
    intros a h_a h_a'
    intros g h_g
    -- we use that N is normal
    obtain ⟨N, N_normal⟩ := N
    rw [normal_iff_lemma] at N_normal
    specialize N_normal ⟨a, h_a'⟩ g
    apply N_normal
  }
}


-- iii) H/(H ∩ N) ≅ HN/N
theorem isomorphism_theorem_1 :
groupsAreIsomorphic (quotient_group H.carrier (H_inter_N H N))
(quotient_group (HN H N).carrier (N' H N)) := by {
  -- we define a homomorphism φ, and then we use the homomorphism-theorem
  let φ : GroupHomomorphism H.carrier (quotient_group (HN H N).carrier (N' H N)) := {
    f := λ h => by {
      have : ↑h ∈ (HN H N).carrier := by {
        simp [HN]
        use h
        simp
        use MyGroup.one
        constructor
        apply subgroup_one_mem_lemma
        rw [MyGroup.mul_one]
      }
      exact ⟦⟨h, this⟩⟧
    }
    mul := by {
      intros a b
      simp
      simp [MyGroup.mul]
      rw [quotient_group_mul]
      simp [MyGroup.mul]
    }
  }

  have h_surj : Function.Surjective φ.f := by {
    rw [Function.Surjective]
    intro a
    let g_a : (↑(HN H N).carrier) := quotient_to_repr a
    have : a = ⟦g_a⟧ := by {
      simp [g_a]
      rw [repr_lemma]
    }
    simp [this]
    simp [GroupHomomorphism.f]

    simp only [HN] at g_a
    obtain ⟨g, h, n, h_h, h_n, h_g⟩ := g_a
    simp [h_g] at this ⊢

    use h
    constructor
    apply Quot.eq.mpr
    simp [Setoid.r]
    constructor
    rw [left_coset_rel]
    simp [MyGroup.mul]

    use MyGroup.inv n
    constructor
    constructor
    simp [N']
    apply Subgroup.inv_mem
    apply h_n
    simp [HN]
    use MyGroup.one
    constructor
    apply subgroup_one_mem_lemma
    use MyGroup.inv n
    constructor
    apply Subgroup.inv_mem
    apply h_n
    rw [MyGroup.one_mul]
    rw [MyGroup.mul_assoc]
    rw [MyGroup.mul_inv, MyGroup.mul_one]
    apply h_h
  }

  have h_ker : ker φ = (H_inter_N H N).carrier := by {
    simp [H_inter_N, ker]
    ext x
    simp
    -- ->
    constructor
    case h.mp =>
      intro h
      simp [GroupHomomorphism.f, MyGroup.one] at h
      rw [quot_eq_lemma] at h
      obtain ⟨h, h_h, h_x⟩ := h
      simp [N'] at h_h
      let h' : N.carrier := ⟨h, h_h⟩
      have : (x : G) = h' := by {
        contrapose! h_x
        simp [MyGroup.mul]
        rw [MyGroup.one_mul]
        apply h_x
      }
      rw [this]
      apply h_h

    case h.mpr =>
      intro h
      simp [GroupHomomorphism.f, MyGroup.one]
      rw [quot_eq_lemma]
      simp [MyGroup.mul, HN, N', MyGroup.one_mul]
      exact h
  }

  have h_im : image_to_subgroup φ = FullSubgroup (quotient_group (↑(HN H N).carrier) (N' H N)) := by {
    simp [image_to_subgroup, FullSubgroup, im]
    rw [Set.univ]
    ext x
    simp
    simp [GroupHomomorphism.f]
    let x' : (↑(HN H N).carrier) := quotient_to_repr x
    have h_x : x = ⟦x'⟧ := by {
      simp [x']
      simp [repr_lemma]
    }
    rw [h_x]
    -- we split the x'
    obtain ⟨g_x, h_g_x⟩ := x'
    simp [HN] at h_g_x
    obtain ⟨h, h_h, n, h_n, h_g_x⟩ := h_g_x

    use h
    use h_h
    rw [quot_eq_lemma]
    simp [N']
    use n
    constructor
    exact h_n
    constructor
    simp [MyGroup.mul]
    exact h_g_x
    simp [HN]
    use MyGroup.one
    constructor
    apply subgroup_contains_one_lemma
    use n
    constructor
    exact h_n
    rw [MyGroup.one_mul]
  }

  have h_isomorphic : groupsAreIsomorphic
      (quotient_group H.carrier (ker_to_normal_subgroup φ))
      (image_to_subgroup φ).carrier := by {
    apply homomorphism_theorem
  }

  have : (ker_to_normal_subgroup φ) = (H_inter_N H N) := by {
    simp [ker_to_normal_subgroup, H_inter_N]
    rw [h_ker]
    simp [H_inter_N]
  }

  rw [this] at h_isomorphic
  rw [h_im] at h_isomorphic

  have h_full_subgroup : groupsAreIsomorphic
      (quotient_group (↑(HN H N).carrier) (N' H N))
      ↑(FullSubgroup (quotient_group (↑(HN H N).carrier) (N' H N))).carrier := by {
    apply full_subgroup_isomorphic_lemma
  }

  apply isomorphic_trans_lemma
    (quotient_group (↑H.carrier) (H_inter_N H N))
    (FullSubgroup (quotient_group (↑(HN H N).carrier) (N' H N))).carrier
    (quotient_group (↑(HN H N).carrier) (N' H N))

  apply h_isomorphic
  apply isomorphic_symm_lemma
  apply h_full_subgroup
}


end isomorphism_theorem
