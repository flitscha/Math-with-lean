import Math.Algebra.C2_Groups.C2_1_Basics.definitions
import Mathlib.Tactic.Ring

----------------------------------------------------------------
-- (ℤ, +) is a group
instance : MyGroup ℤ where
  mul := Int.add
  one := 0
  inv := Int.neg
  mul_assoc := by simp [Int.add_assoc]
  one_mul := by simp [Int.zero_add]
  mul_one := by simp [Int.add_zero]
  inv_mul := by {
    intro a
    have h : (-a) + a = 0 := by simp
    exact h
  }
  mul_inv := by {
    intro a
    have h : a + (-a) = 0 := by simp
    exact h
  }

----------------------------------------------------------------
-- Lemma: the neutral element is unique
-- it is already defined as unique in the group structure
-- but still: here a standard-proof:
theorem neutral_element_unique_lemma [MyGroup G] (e e' : G)
(h_e : e = MyGroup.one) (h_e' : e' = MyGroup.one) : e = e' := by {
  have h1 : MyGroup.mul e e' = e := by {
    rw [h_e']
    apply MyGroup.mul_one
  }
  have h2 : MyGroup.mul e e' = e' := by {
    rw [h_e]
    apply MyGroup.one_mul
  }
  rw [h1] at h2
  exact h2
}


--------------------------------------------------------------
-- in groups, we can do this: a = b ↔ a+x = b+x
theorem group_cancel_rule_right_lemma (G : Type u) [MyGroup G] (a b x : G) :
a = b ↔ MyGroup.mul a x = MyGroup.mul b x := by {
  -- ->
  have h1 : a = b -> MyGroup.mul a x = MyGroup.mul b x := by {
    intro h
    rw [h]
  }
  constructor
  exact h1
  -- <-
  intro h
  -- use the inverse of x
  have h2 : MyGroup.mul (MyGroup.mul a x) (MyGroup.inv x) =
            MyGroup.mul (MyGroup.mul b x) (MyGroup.inv x) := by {
    rw [h]
  }

  repeat rw [MyGroup.mul_assoc] at h2
  repeat rw [MyGroup.mul_inv] at h2
  repeat rw [MyGroup.mul_one] at h2
  exact h2
}

theorem group_cancel_rule_left_lemma (G : Type u) [MyGroup G] (a b x : G) :
a = b ↔ MyGroup.mul x a = MyGroup.mul x b := by {
  -- ->
  have h1 : a = b -> MyGroup.mul x a = MyGroup.mul x b := by {
    intro h
    rw [h]
  }
  constructor
  exact h1
  -- <-
  intro h
  -- use the inverse of x
  have h2 : MyGroup.mul (MyGroup.inv x) (MyGroup.mul x a) =
            MyGroup.mul (MyGroup.inv x) (MyGroup.mul x b) := by {
    rw [h]
  }

  repeat rw [← MyGroup.mul_assoc] at h2
  repeat rw [MyGroup.inv_mul] at h2
  repeat rw [MyGroup.one_mul] at h2
  exact h2
}


----------------------------------------------------------------
-- a * b = 1 -> b = a⁻¹
theorem inv_unique_lemma [MyGroup G] (a b : G) (h : MyGroup.mul a b = MyGroup.one) :
b = MyGroup.inv a := by {
  have : MyGroup.mul (MyGroup.inv a) (MyGroup.mul a b) =
        MyGroup.mul (MyGroup.inv a) MyGroup.one := by {
    rw [← group_cancel_rule_left_lemma]
    exact h
  }
  rw [MyGroup.mul_one] at this
  rw [← MyGroup.mul_assoc] at this
  rw [MyGroup.inv_mul] at this
  rw [MyGroup.one_mul] at this
  exact this
}


----------------------------------------------------------------
-- (a⁻¹)⁻¹ = a
theorem double_inv_lemma [MyGroup G] (a : G) :
MyGroup.inv (MyGroup.inv a) = a := by {
  have h : MyGroup.mul (MyGroup.inv a) (MyGroup.inv (MyGroup.inv a)) = MyGroup.one := by {
    apply MyGroup.mul_inv
  }

  have h2 : a = MyGroup.mul a MyGroup.one := by {
    symm
    apply MyGroup.mul_one
  }

  nth_rewrite 2 [h2]
  rw [← h]
  rw [← MyGroup.mul_assoc]
  rw [MyGroup.mul_inv]
  rw [MyGroup.one_mul]
}


----------------------------------------------------------------
-- (a * b)⁻¹ = b⁻¹ * a⁻¹
theorem mul_inv_lemma [MyGroup G] (a b : G) :
MyGroup.inv (MyGroup.mul a b) = MyGroup.mul (MyGroup.inv b) (MyGroup.inv a) := by {
  have h1 : MyGroup.mul (MyGroup.mul a b) (MyGroup.mul (MyGroup.inv b) (MyGroup.inv a)) = MyGroup.one := by {
    rw [MyGroup.mul_assoc]
    nth_rewrite 2 [← MyGroup.mul_assoc]
    rw [MyGroup.mul_inv, MyGroup.one_mul]
    rw [MyGroup.mul_inv]
  }

  rw [← inv_unique_lemma]
  exact h1
}


--------------------------------------------------------------
-- Lemma: every nonempty subset of ℕ has a minimum
theorem nat_minimum_lemma (S : Set ℕ) (h_nonempty : S ≠ ∅) :
∃ x ∈ S, ∀ m ∈ S, x <= m := by {
  contrapose! h_nonempty
  apply Set.eq_empty_iff_forall_not_mem.mpr
  contrapose! h_nonempty
  obtain ⟨x, h_x⟩ := h_nonempty

  --let s_n := { k : ℕ | k <= n }
  have h_i : (∀ n : ℕ, S ∩ {k | k ≤ n} ≠ ∅ -> ∃ k ∈ S, ∀ m ∈ S, k ≤ m) := by {
    intro n
    induction n
    case zero =>
      simp
      intro h_0
      use 0
      constructor
      exact h_0
      simp

    case succ n' h_n =>
      by_cases h_case : S ∩ {k | k ≤ n'} ≠ ∅
      case pos =>
        intro
        exact h_n h_case
      case neg =>
        intro h
        have h_n1 : n'+1 ∈ S := by {
          simp at h_case
          -- simplifying it with de-morgan
          have h_simp : S ∩ {k | k ≤ n' + 1} = (S ∩ {k | k ≤ n'}) ∪ (S ∩ {n' + 1}) := by {
            -- ->
            ext y
            simp
            constructor
            intro h_y
            obtain ⟨h_y1, h_y2⟩ := h_y
            by_cases h_case2 : y = n'+1
            case pos =>
              right
              constructor
              exact h_y1
              exact h_case2
            case neg =>
              left
              constructor
              exact h_y1
              cases h_y2
              case refl =>
                contrapose! h_case2
                rfl
              case step h_step =>
                exact h_step
            -- <-
            intro h_y
            cases h_y
            case inl h_y =>
              obtain ⟨h_y1, h_y2⟩ := h_y
              constructor
              exact h_y1
              apply Nat.le_add_one_iff.mpr
              left
              exact h_y2
            case inr h_y =>
              obtain ⟨h_y1, h_y2⟩ := h_y
              constructor
              exact h_y1
              rw [h_y2]
          }

          rw [←Set.nonempty_iff_ne_empty] at h
          cases h with
          | intro y hy =>
            rw [h_simp] at hy
            cases hy
            case inl h1 =>
              apply Set.eq_empty_iff_forall_not_mem.mp at h_case
              specialize h_case y
              have : False := by exact h_case h1
              exact False.elim this
            case inr h2 =>
              simp at h2
              obtain ⟨h1, h2⟩ := h2
              rw [← h2]
              exact h1
        }
        use n'+1
        constructor
        exact h_n1
        intro m
        simp at h_case
        apply Set.eq_empty_iff_forall_not_mem.mp at h_case
        contrapose! h_case
        use m
        obtain ⟨h1, h2⟩ := h_case
        simp
        constructor
        exact h1
        rw [add_comm] at h2
        rw [Nat.lt_one_add_iff] at h2
        exact h2
  }
  -- idea: we choose a n, such that x ∈ S∩{n=1} ∪ S∩{n=2} ∪ ...
  -- then we use k as the minimum at h2
  have h_n : ∃ n : ℕ, x ∈ S ∩ {k | k ≤ n } := by {
    use x
    simp
    exact h_x
  }
  obtain ⟨n, h_n⟩ := h_n

  specialize h_i n
  have h : S ∩ {k | k ≤ n} ≠ ∅ := by {
    intro h_empty
    apply Set.eq_empty_iff_forall_not_mem.mp at h_empty
    specialize h_empty x
    simp at h_n
    simp at h_empty
    obtain ⟨h_n1, h_n2⟩ := h_n
    contrapose! h_empty
    constructor
    exact h_n1
    exact h_n2
  }

  exact h_i h
}


--------------------------------------------------------------
-- Lemma 2.1.5:
-- every subgroup of ℤ looks like this for a n ∈ ℤ: {n*z | z ∈ Z}
theorem lemma_2_1_5 (H : Subgroup ℤ) :
∃ n : ℤ, H.carrier = { x : ℤ | ∃ z : ℤ, x = n*z } := by {
  -- first we prove, that 0 ∈ H.carrier
  have h_0 : 0 ∈ H.carrier := by {
    -- H is a subgroup -> H ≠ ∅
    have h_nonempty : H.carrier ≠ ∅ := by {
      apply Subgroup.nonempty
    }
    -- this means, there is an element in H
    have h_a : ∃ a : ℤ, a ∈ H.carrier := by {
      contrapose! h_nonempty
      apply Set.eq_empty_iff_forall_not_mem.mpr
      exact h_nonempty
    }
    obtain ⟨a, h_a⟩ := h_a
    -- -a is also in H
    have a_inv : MyGroup.inv a ∈ H.carrier := by {
      apply Subgroup.inv_mem
      exact h_a
    }
    -- 0 = a + -a
    have h_0 : 0 = a + -a := by simp
    rw [h_0]
    apply Subgroup.mul_mem
    constructor
    exact h_a
    apply a_inv
  }

  by_cases h_case : H.carrier = {0}
  -- trivial case: H = {0}
  case pos =>
    rw [h_case]
    use 0
    simp

  case neg =>
    -- we prove, that there exists a element, with minimal absolute value
    have h_min : ∃ m ∈ H.carrier, m ≠ 0 ∧
                ∀ m' ∈ H.carrier, m' ≠ 0 -> |m| <= |m'| := by {
      -- H has at least 2 elements, because 0 ∈ H, but H ≠ {0}
      have h_nonempty : ∃ x, x ∈ H.carrier ∧ x ≠ 0 := by {
        contrapose! h_case
        ext x
        constructor
        -- ->
        intro h_x
        simp
        specialize h_case x
        exact h_case h_x
        -- <-
        intro h_x
        simp at h_x
        rw [h_x]
        exact h_0
      }

      -- we want the minimal absolute value of H. We do that with this subset of ℕ
      set M := { x : ℕ | ∃ n ∈ H.carrier, n ≠ 0 ∧ x = |n| } with h_M
      have h_M_min : ∃ x ∈ M, ∀ m ∈ M, x <= m := by {
        apply nat_minimum_lemma
        contrapose! h_nonempty
        apply Set.eq_empty_iff_forall_not_mem.mp at h_nonempty
        simp at h_nonempty
        intro x
        intro h_x
        specialize h_nonempty (x.natAbs)
        rw [h_M] at h_nonempty
        simp at h_nonempty
        specialize h_nonempty x
        have h_tmp : (¬x = 0 → ¬|x| = |x|) := by exact h_nonempty h_x
        by_cases h_case1 : x = 0
        case pos =>
          exact h_case1
        case neg =>
          have h1 : ¬|x| = |x| := by exact h_tmp h_case1
          simp at h1
      }

      -- now we can use this minimum
      obtain ⟨x, h_x_M, h_x_min⟩ := h_M_min
      rw [h_M] at h_x_M
      simp at h_x_M
      obtain ⟨n, h_n_H, h_n_0, h_n_x⟩ := h_x_M
      use n
      constructor
      exact h_n_H
      constructor
      apply h_n_0
      intro m'
      intro h_m'
      intro h_m0
      rw [← h_n_x]
      have h_m_M : m'.natAbs ∈ M := by {
        rw [h_M]
        simp
        use m'
      }
      specialize h_x_min m'.natAbs
      have : x ≤ m'.natAbs := by exact h_x_min h_m_M
      have h_mm : |m'| = m'.natAbs := by simp
      rw [h_mm]
      norm_cast
    }

    -- we use the minimum
    obtain ⟨n, h_min⟩ := h_min
    use n
    ext x
    constructor
    -- H ⊆ n*ℤ
    intro h_x
    simp
    have h1 : ∃ a b : ℤ, |b| < |n| ∧ x = n*a + b := by {
      obtain ⟨_, h_tmp2, _⟩ := h_min
      use (x / n : ℤ)
      use x % n
      constructor
      rw [abs_of_nonneg]
      apply Int.emod_lt
      exact h_tmp2
      apply Int.emod_nonneg
      exact h_tmp2
      rw [Int.ediv_add_emod]
    }
    obtain ⟨a, b, h1, h2⟩ := h1

    have h3 : b ∈ H.carrier := by {
      have h_tmp : b = x - n*a := by {
        rw [h2]
        simp
      }
      rw [h_tmp]
      rw [sub_eq_add_neg]
      apply Subgroup.mul_mem
      constructor
      exact h_x
      clear h2
      clear h_tmp
      obtain ⟨h, _⟩ := h_min
      induction a
      case a.right.intro.ofNat a =>
        rw [Int.ofNat_eq_coe]
        induction a
        case zero =>
          simp
          exact h_0
        case succ a' h_a =>
          have : -(n * ↑(a' + 1)) = -(n * ↑a') + -n := by {
            simp
            ring
          }
          rw [this]
          apply Subgroup.mul_mem
          constructor
          exact h_a
          apply Subgroup.inv_mem
          exact h
      case a.right.intro.negSucc a =>
        rw [Int.negSucc_coe]
        induction a
        case zero =>
          simp
          exact h
        case succ a' h_a =>
          have : -(n * -↑(a' + 1 + 1)) = -(n * -↑(a' + 1)) + n := by {
            simp
            ring
          }
          rw [this]
          apply Subgroup.mul_mem
          constructor
          exact h_a
          exact h
    }

    have h4 : b = 0 := by {
      contrapose! h1
      obtain ⟨_, _, h_tmp3⟩ := h_min
      specialize h_tmp3 b
      have h_tmp4 : b ≠ 0 → |n| ≤ |b| := by exact h_tmp3 h3
      exact h_tmp4 h1
    }

    have h5 : x = n*a := by {
      rw [h4] at h2
      simp at h2
      exact h2
    }

    use a

    -- n*ℤ ⊆ H
    intro h_x
    simp at h_x
    obtain ⟨h_nH, _⟩ := h_min
    obtain ⟨z, h_x⟩ := h_x
    induction z
    case ofNat z =>
      simp at h_x
      rw [h_x]
      clear h_x
      induction z
      case zero =>
        simp
        exact h_0
      case succ z' h_z =>
        have h_tmp : n * ↑(z' + 1) = n * ↑z' + n := by {
          nth_rewrite 3 [← Int.mul_one n]
          rw [← Int.mul_add]
          simp
        }
        rw [h_tmp]
        apply Subgroup.mul_mem
        constructor
        exact h_z
        exact h_nH
    case negSucc z =>
      rw [h_x]
      clear h_x
      induction z
      case zero =>
        simp
        apply Subgroup.inv_mem
        exact h_nH
      case succ z' h_z =>
        rw [Int.negSucc_coe] at h_z
        rw [Int.negSucc_coe]
        have h_tmp : n * -↑(z' + 1 + 1) = n * -↑(z' + 1) - n := by {
          simp
          ring
        }
        rw [h_tmp]
        rw [Int.sub_eq_add_neg]
        apply Subgroup.mul_mem
        constructor
        exact h_z
        apply Subgroup.inv_mem
        exact h_nH
}


--------------------------------------------------------------
-- let G be a group, H ⊆ G. H is a subgroup iff H is not empty, and
-- ∀ h1, h2 ∈ H, h1⁻¹*h2 ∈ H
theorem subgroup_iff_lemma (G : Type u) [MyGroup G] (H : Set G) :
(∃ K : Subgroup G, K.carrier = H) ↔ (H ≠ ∅ ∧
∀ a b : G, (a ∈ H ∧ b ∈ H) -> MyGroup.mul (MyGroup.inv a) b ∈ H) := by {
  -- ->
  constructor
  intro h_subgroup
  obtain ⟨K, h_subgroup⟩ := h_subgroup
  rw [← h_subgroup]
  constructor
  apply K.nonempty
  intros a b
  intro h_h
  obtain ⟨h_a, h_b⟩ := h_h
  have h_inv : (MyGroup.inv a ∈ K.carrier) := by {
    apply K.inv_mem
    exact h_a
  }
  apply K.mul_mem
  constructor
  exact h_inv
  exact h_b

  -- <-
  intro h
  obtain ⟨h1, h2⟩ := h
  have h_e : MyGroup.one ∈ H := by {
    have : ∃ a : G, a ∈ H := by {
      contrapose! h1
      rw [Set.eq_empty_iff_forall_not_mem]
      exact h1
    }
    obtain ⟨a, h_a_mem⟩ := this
    specialize h2 a a
    have : MyGroup.mul (MyGroup.inv a) a ∈ H := by {
      apply h2
      simp [h_a_mem]
    }
    rw [MyGroup.inv_mul] at this
    exact this
  }

  have h_inv : (∀ {a : G}, a ∈ H → MyGroup.inv a ∈ H) := by {
    intro a
    intro h_a
    have : MyGroup.mul (MyGroup.inv a) MyGroup.one ∈ H := by {
      specialize h2 a MyGroup.one
      simp [h_a, h_e] at h2
      exact h2
    }
    rw [MyGroup.mul_one] at this
    exact this
  }

  have h_mul : (∀ a b : G, (a ∈ H ∧ b ∈ H) → MyGroup.mul a b ∈ H) := by {
    intros a b
    intro h_mem
    specialize h2 (MyGroup.inv a) b
    simp [h_mem, h_inv] at h2
    rw [double_inv_lemma] at h2
    exact h2
  }

  let K : Subgroup G := {
    carrier := H
    nonempty := h1
    mul_mem := h_mul
    inv_mem := h_inv
  }

  use K
}


--------------------------------------------------------------
-- A Subgroup contains the neutral element
theorem subgroup_one_mem_lemma (G : Type u) [MyGroup G] (H : Subgroup G) :
MyGroup.one ∈ H.carrier := by {
  have h1 : H.carrier ≠ ∅ := by {
    apply Subgroup.nonempty
  }

  have h2 : ∃ x : G, x ∈ H.carrier := by {
    contrapose! h1
    rw [Set.eq_empty_iff_forall_not_mem]
    exact h1
  }
  obtain ⟨x, h2⟩ := h2

  have h3 : MyGroup.inv x ∈ H.carrier := by {
    apply Subgroup.inv_mem
    exact h2
  }

  have h4 : MyGroup.mul (MyGroup.inv x) x ∈ H.carrier := by {
    apply Subgroup.mul_mem
    exact ⟨h3, h2⟩
  }

  rw [MyGroup.inv_mul] at h4
  exact h4
}

---------------------------------------------------------------
-- Lemma: a bijective funktion has a inverse function
theorem bijective_has_inverse_lemma {A : Type u} {B : Type v} (f : A → B)
(h_bij : Function.Bijective f) :
∃ (f_inv : B → A),
(∀ x2 : B, f (f_inv x2) = x2) ∧
(∀ x1 : A, f_inv (f x1) = x1) := by {

  obtain ⟨h_inj, h_surj⟩ := h_bij
  choose f_inv h_f_inv using h_surj
  use f_inv

  constructor
  intro x2
  exact h_f_inv x2

  intro x1
  rw [Function.Injective] at h_inj
  specialize h_f_inv (f x1)
  specialize h_inj h_f_inv
  exact h_inj
}


----------------------------------------------------------------
-- Lemma: if a function has a inverse, then the function is bijective
theorem inverse_is_bijective_lemma {A : Type u} {B : Type v} (f : A -> B)
(h_inv : ∃ (f_inv : B → A),
(∀ x2 : B, f (f_inv x2) = x2) ∧
(∀ x1 : A, f_inv (f x1) = x1)) :
Function.Bijective f := by {

  obtain ⟨f_inv, h_inv⟩ := h_inv
  obtain ⟨h_left_inv, h_right_inv⟩ := h_inv
  constructor
  -- injective
  intros x1 x2 h_eq
  have h1 : f_inv (f x1) = x1 := h_right_inv x1
  have h2 : f_inv (f x2) = x2 := h_right_inv x2
  rw [← h1, ← h2, h_eq]
  -- surjective
  intro x
  use f_inv x
  exact h_left_inv x
}


-----------------------------------------------------------------
-- group-isomorphisms are invertable
theorem isomorphism_is_invertable_lemma (G1 : Type u) (G2 : Type v)
[MyGroup G1] [MyGroup G2] (φ : GroupIsomorphism G1 G2) :
∃ ψ : GroupHomomorphism G2 G1,
(∀ x2 : G2, φ.f (ψ.f x2) = x2) ∧
(∀ x1 : G1, ψ.f (φ.f x1) = x1) := by {

  let φ_f : G1 -> G2 := φ.f

  have h_φ_inj : Function.Injective φ_f := φ.injective
  -- this seems strange. h_inj has the type: Function.Injective GroupHomomorphism.f
  -- but a few details are hidden. The real type is:
  -- Function.Injective (@GroupHomomorphism.f G1 G2 inst✝¹ inst✝ φ.toGroupHomomorphism)
  have h_φ_sur : Function.Surjective φ_f := φ.surjective

  -- define the inverse function
  have h_inv : ∃ (ψ_f : G2 → G1),
  (∀ x2 : G2, φ_f (ψ_f x2) = x2) ∧
  (∀ x1 : G1, ψ_f (φ_f x1) = x1) := by {
    apply bijective_has_inverse_lemma φ_f
    rw [Function.Bijective]
    constructor
    exact h_φ_inj
    exact h_φ_sur
  }
  obtain ⟨ψ_f, h_inv⟩ := h_inv

  -- we show, that the inverse-function is a group-homomorphism
  have ψ_f_is_homomorphism : ∀ x2 y2 : G2, ψ_f (MyGroup.mul x2 y2) = MyGroup.mul (ψ_f x2) (ψ_f y2) := by {
    intros x2 y2

    have h1 : φ_f (ψ_f (MyGroup.mul x2 y2)) =
    MyGroup.mul (φ_f (ψ_f x2)) (φ_f (ψ_f y2)) := by {
      obtain ⟨h_tmp1, _⟩ := h_inv
      repeat rw [h_tmp1]
    }

    have h2 : MyGroup.mul (φ_f (ψ_f x2)) (φ_f (ψ_f y2)) =
    φ_f (MyGroup.mul (ψ_f x2) (ψ_f y2)) := by {
      rw [← φ.mul]
    }

    rw [h2] at h1
    apply h_φ_inj at h1
    exact h1
  }

  -- define the inverse group homomorphism
  let ψ : GroupHomomorphism G2 G1 := {
    f := ψ_f
    mul := ψ_f_is_homomorphism
  }

  use ψ
  apply h_inv
}


------------------------------------------------------------------
-- an invertable group-homomorphism is a group-isomorphisms
theorem invertable_homomorphism_is_isomorphism_lemma (G1 : Type u) (G2 : Type v)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2)
(h_inv : ∃ ψ : GroupHomomorphism G2 G1,
(∀ x2 : G2, φ.f (ψ.f x2) = x2) ∧
(∀ x1 : G1, ψ.f (φ.f x1) = x1)) : Function.Bijective φ.f := by {
  obtain ⟨ψ, h_inv⟩ := h_inv
  apply inverse_is_bijective_lemma
  use ψ.f
}

/-
def G1 : Type u := sorry
def G2 : Type v := sorry
instance : MyGroup G1 := sorry
instance : MyGroup G2 := sorry
def e1 : G1 := sorry
def h_e1 : e1 = MyGroup.one := sorry
def φ : GroupHomomorphism G1 G2 := sorry
#check MyGroup.one
-/

-------------------------------------------------------------------
-- group homomorphisms map the neutral element of G1 to the neutral element of G2
theorem homomorphism_neutral_element_lemma (G1 : Type u) (G2 : Type v)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2) (e1 : G1) (e2 : G2)
(h_e1 : e1 = MyGroup.one) (h_e2 : e2 = MyGroup.one) : φ.f e1 = e2 := by {

  have h : φ.f e1 = MyGroup.mul (φ.f e1) (φ.f e1) := by {
    have h1 : MyGroup.mul e1 e1 = e1 := by {
      rw [h_e1, MyGroup.mul_one]
    }
    nth_rewrite 1 [← h1]
    rw [GroupHomomorphism.mul]
  }

  have h1 : MyGroup.mul (φ.f e1) (MyGroup.inv (φ.f e1)) =
            MyGroup.mul (MyGroup.mul (φ.f e1) (φ.f e1)) (MyGroup.inv (φ.f e1)) := by {
    rw [← group_cancel_rule_right_lemma]
    exact h
  }
  rw [MyGroup.mul_assoc] at h1
  repeat rw [MyGroup.mul_inv] at h1
  rw [MyGroup.mul_one] at h1
  rw [← h1]
  symm
  exact h_e2
}


------------------------------------------------------------------
-- group homomorphisms map the inverse element to the inverse element
theorem homomorphism_inverse_element_lemma (G1 : Type u) (G2 : Type v)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2) :
∀ x1 : G1, φ.f (MyGroup.inv x1) = MyGroup.inv (φ.f x1) := by {
  intro x1
  have h : φ.f (MyGroup.mul (MyGroup.inv x1) x1) = MyGroup.one := by {
    rw [MyGroup.inv_mul]
    apply homomorphism_neutral_element_lemma
    rfl
    rfl
  }
  rw [GroupHomomorphism.mul] at h

  have h2 : MyGroup.mul (MyGroup.mul (φ.f (MyGroup.inv x1)) (φ.f x1)) (MyGroup.inv (φ.f x1)) =
            MyGroup.mul MyGroup.one (MyGroup.inv (φ.f x1)) := by {
    rw [← group_cancel_rule_right_lemma]
    exact h
  }
  rw [MyGroup.mul_assoc] at h2
  rw [MyGroup.mul_inv, MyGroup.one_mul, MyGroup.mul_one] at h2
  rw [h2]
}


--------------------------------------------------------------------
-- g₁H = g₂H ↔ g₁⁻¹*g₂ ∈ H
theorem left_coset_eq_lemma (G : Type u) [MyGroup G] (H : Subgroup G) (g1 g2 : G) :
left_coset G H g1 = left_coset G H g2 ↔
MyGroup.mul (MyGroup.inv g1) g2 ∈ H.carrier := by {
  -- ->
  constructor
  intro h3
  repeat rw [left_coset] at h3
  have h_g2 : g2 ∈ {x | ∃ h : H.carrier, x = MyGroup.mul g2 h} ->
              g2 ∈ {x | ∃ h : H.carrier, x = MyGroup.mul g1 h} := by {
    intro h_h
    rw [h3]
    exact h_h
  }

  have h1 : g2 ∈ {x | ∃ h : H.carrier, x = MyGroup.mul g2 ↑h} := by {
    simp
    use MyGroup.one
    constructor
    apply subgroup_one_mem_lemma
    rw [MyGroup.mul_one]
  }

  have h2 : g2 ∈ {x | ∃ h : H.carrier, x = MyGroup.mul g1 ↑h} := by {
    apply h_g2
    exact h1
  }

  simp at h2
  obtain ⟨a, h_a, h2⟩ := h2

  have h3 : MyGroup.mul (MyGroup.inv g1) g2 =
            MyGroup.mul (MyGroup.inv g1) (MyGroup.mul g1 a) := by {
    rw [← group_cancel_rule_left_lemma]
    exact h2
  }

  rw [← MyGroup.mul_assoc] at h3
  rw [MyGroup.inv_mul] at h3
  rw [MyGroup.one_mul] at h3
  rw [← h3] at h_a
  exact h_a

  -- <-
  intro h
  repeat rw [left_coset]

  ext x
  simp
  constructor
  intro h2
  obtain ⟨a, h2, h3⟩ := h2
  have h_inv : MyGroup.mul (MyGroup.inv g2) g1 ∈ H.carrier := by {
    have : MyGroup.mul (MyGroup.inv g2) g1 =
          MyGroup.inv (MyGroup.mul (MyGroup.inv g1) g2) := by {
      rw [mul_inv_lemma]
      rw [double_inv_lemma]
    }
    rw [this]
    apply Subgroup.inv_mem
    exact h
  }
  use (MyGroup.mul (MyGroup.mul (MyGroup.inv g2) g1) a)
  constructor
  apply Subgroup.mul_mem
  exact ⟨h_inv, h2⟩
  rw [MyGroup.mul_assoc]
  rw [← h3]
  rw [← MyGroup.mul_assoc]
  rw [MyGroup.mul_inv, MyGroup.one_mul]

  intro h2
  obtain ⟨a, h2, h3⟩ := h2
  use MyGroup.mul (MyGroup.mul (MyGroup.inv g1) g2) a
  constructor
  apply Subgroup.mul_mem
  constructor
  exact h
  exact h2
  repeat rw [← MyGroup.mul_assoc]
  rw [MyGroup.mul_inv, MyGroup.one_mul]
  exact h3
}


--------------------------------------------------------------------
-- Hg₁ = Hg₂ ↔ g₁*g₂⁻¹ ∈ H
theorem right_coset_eq_lemma (G : Type u) [MyGroup G] (H : Subgroup G) (g1 g2 : G) :
right_coset G H g1 = right_coset G H g2 ↔
MyGroup.mul g1 (MyGroup.inv g2) ∈ H.carrier := by {
  sorry
}


-------------------------------------------------------------------
-- H is a normal Subgroup ↔ h ∈ H, g ∈ G -> g⁻¹hg ∈ H
theorem normal_subgroup_iff_lemma (G : Type u) [MyGroup G] (K : Set G) :
(∃ H : normal_subgroup G, H.carrier = K) ↔
(∃ H : Subgroup G, H.carrier = K ∧
∀ h : H.carrier, ∀ g : G, MyGroup.mul (MyGroup.mul (MyGroup.inv g) h) g ∈ K) := by {
  sorry
}


--------------------------------------------------------------------
-- in an abelian group, every subgroup is normal
theorem abelian_subgroup_is_normal_lemma (G : Type u) [AbelianGroup G] (K : Set G) :
(∃ H : Subgroup G, H.carrier = K -> ∃ H : normal_subgroup G, H.carrier = K) := by {
  sorry
}


---------------------------------------------------------------------
-- let φ : G -> H. ker(φ) is a normal subgroup of G
theorem kernel_is_normal_subgroup_lemma (G : Type u) (H : Type v)
[MyGroup G] [MyGroup H] (φ : GroupHomomorphism G H) :
∃ N : normal_subgroup G, N.carrier = ker φ := by {
  sorry
}

--------------------------------------------------------------------
-- let φ : G -> H. im(φ) is a subgroup of H
theorem image_is_subgroup_lemma (G : Type u) (H : Type v) [MyGroup G] [MyGroup H]
(φ : GroupHomomorphism G H) : ∃ S : Subgroup H, S.carrier = im φ := by {
  sorry
}


--------------------------------------------------------------------
theorem homomorphism_injective_iff_lemma (G : Type u) (H : Type v) [MyGroup G]
[MyGroup H] (φ : GroupHomomorphism G H) :
Function.Injective φ.f ↔ ker φ = { MyGroup.one } := by {
  sorry
}
