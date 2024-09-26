import Math.Algebra.C2_Groups.C2_1_Basics.definitions
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic


-- subgroup is a group
instance {G : Type} [MyGroup G] (H : Subgroup G) : MyGroup (H.carrier : Type) where
  mul := by {
    intros a b
    have : MyGroup.mul (a : G) b ∈ H.carrier := by {
      apply Subgroup.mul_mem
      simp
    }
    exact ⟨MyGroup.mul a b, this⟩
  }
  one := by {
    have : MyGroup.one ∈ H.carrier := by {
      have h_empty : H.carrier ≠ ∅ := by {
        apply Subgroup.nonempty
      }
      have h_g : ∃ g : G, g ∈ H.carrier := by {
        contrapose! h_empty
        rw [Set.eq_empty_iff_forall_not_mem]
        exact h_empty
      }
      obtain ⟨g, h_g⟩ := h_g
      have h_g_inv : MyGroup.inv g ∈ H.carrier := by {
        apply Subgroup.inv_mem
        exact h_g
      }
      have h_g_g_inv : MyGroup.mul (MyGroup.inv g) g ∈ H.carrier := by {
        apply Subgroup.mul_mem
        exact ⟨h_g_inv, h_g⟩
      }
      rw [MyGroup.inv_mul] at h_g_g_inv
      exact h_g_g_inv
    }
    exact ⟨MyGroup.one, this⟩
  }
  inv := by {
    intro a
    have : MyGroup.inv (a : G) ∈ H.carrier := by {
      apply Subgroup.inv_mem
      simp
    }
    exact ⟨MyGroup.inv a, this⟩
  }
  mul_assoc := by {
    intros a b c
    simp
    apply MyGroup.mul_assoc
  }
  one_mul := by {
    simp
    intros a _
    apply MyGroup.one_mul
  }
  mul_one := by {
    simp
    intros a _
    apply MyGroup.mul_one
  }
  inv_mul := by {
    simp
    intros a _
    apply MyGroup.inv_mul
  }
  mul_inv := by {
    simp
    intros a _
    apply MyGroup.mul_inv
  }

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
-- it is already defined as unique in the group str ucture
-- but still: here a standard-proof:
theorem neutral_element_unique_lemma {G : Type} [MyGroup G] (e e' : G)
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
theorem group_cancel_rule_right_lemma (G : Type) [MyGroup G] (x a b : G) :
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

theorem group_cancel_rule_left_lemma (G : Type) [MyGroup G] (x a b : G) :
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
theorem inv_unique_lemma {G : Type} [MyGroup G] (a b : G) (h : MyGroup.mul a b = MyGroup.one) :
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
theorem double_inv_lemma {G : Type} [MyGroup G] (a : G) :
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
-- 1⁻¹ = 1
theorem inv_one_lemma {G : Type} [MyGroup G] :
(MyGroup.inv MyGroup.one : G) = MyGroup.one := by {
  have : (MyGroup.mul MyGroup.one MyGroup.one : G) =
  MyGroup.mul (MyGroup.inv MyGroup.one) MyGroup.one := by {
    rw [MyGroup.inv_mul, MyGroup.mul_one]
  }
  rw [← group_cancel_rule_right_lemma] at this
  rw [← this]
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


----------------------------------------------------------------
theorem subgroup_contains_one_lemma {G : Type} [MyGroup G] (H : Subgroup G) :
MyGroup.one ∈ H.carrier := by {
  have h_nonempty : H.carrier ≠ ∅ := by apply Subgroup.nonempty
  have h_g : ∃ g : G, g ∈ H.carrier := by {
    contrapose! h_nonempty
    rw [Set.eq_empty_iff_forall_not_mem]
    exact h_nonempty
  }
  obtain ⟨g, h_g⟩ := h_g
  have h_g_inv : MyGroup.inv g ∈ H.carrier := by {
    apply Subgroup.inv_mem
    exact h_g
  }
  have h_product : MyGroup.mul g (MyGroup.inv g) ∈ H.carrier := by {
    apply Subgroup.mul_mem
    exact ⟨h_g, h_g_inv⟩
  }
  rw [MyGroup.mul_inv] at h_product
  exact h_product
}


----------------------------------------------------------------
-- g⁻¹ = MyGroup.inv g
theorem pow_neg_one_eq_inv {G : Type} [MyGroup G] (g : G) :
group_pow g (-1) = MyGroup.inv g := by {
  have : -1 = Int.negSucc 0 := by simp
  rw [this]
  simp [group_pow, group_pow_nat]
  rw [MyGroup.mul_one]
}

-----------------------------------------------------------------
-- g * g^n = g^n * g
theorem pow_comm_aux {G : Type} [MyGroup G] (g : G) (z : ℤ) :
MyGroup.mul g (group_pow g z) = MyGroup.mul (group_pow g z) g := by {
  cases z
  case ofNat n =>
    simp [group_pow]
    induction n
    case zero =>
      simp [group_pow_nat]
      rw [MyGroup.mul_one, MyGroup.one_mul]
    case succ n' h_n =>
      simp [group_pow_nat]
      rw [h_n]
      nth_rewrite 2 [← h_n]
      rw [MyGroup.mul_assoc]
  case negSucc n =>
    simp [group_pow]
    induction n
    case zero =>
      simp [group_pow_nat]
      rw [mul_inv_lemma, MyGroup.mul_assoc, inv_one_lemma]
      rw [MyGroup.one_mul]
      rw [MyGroup.mul_inv, MyGroup.one_mul, MyGroup.inv_mul]
    case succ n' h_n =>
      rw [group_pow_nat]
      rw [mul_inv_lemma]
      rw [← MyGroup.mul_assoc]
      rw [h_n]
      clear h_n
      repeat rw [MyGroup.mul_assoc]
      rw [MyGroup.mul_inv, MyGroup.inv_mul, MyGroup.mul_one]
}


--------------------------------------------------------------
-- gⁿ * gᵐ = gᵐ * gⁿ
theorem pow_comm_lemma {G : Type} [MyGroup G] (g : G) (n m : ℤ) :
MyGroup.mul (group_pow g n) (group_pow g m) =
MyGroup.mul (group_pow g m) (group_pow g n) := by {
  induction n
  case ofNat n =>
    induction n
    case zero =>
      nth_rewrite 1 [group_pow]
      nth_rewrite 3 [group_pow]
      simp
      simp [group_pow_nat]
      rw [MyGroup.one_mul, MyGroup.mul_one]
    case succ n' h_n =>
      rw [group_pow]
      simp
      rw [group_pow_nat]
      rw [group_pow] at h_n
      simp at h_n
      have : group_pow_nat g n' = group_pow g n' := by {
        rw [group_pow]
      }
      rw [this]
      rw [pow_comm_aux]
      rw [group_pow]
      simp
      rw [MyGroup.mul_assoc]
      rw [pow_comm_aux]
      rw [← MyGroup.mul_assoc]
      rw [h_n]
      clear h_n
      rw [MyGroup.mul_assoc]
  case negSucc n =>
    induction n
    case zero =>
      rw [group_pow]
      simp
      repeat rw [group_pow_nat]
      rw [MyGroup.mul_one]
      induction m
      case ofNat m =>
        induction m
        case zero =>
          simp [group_pow, group_pow_nat]
          rw [MyGroup.mul_one, MyGroup.one_mul]
        case succ m' h_m =>
          simp [group_pow]
          simp [group_pow_nat]
          have : group_pow_nat g m' = group_pow g m' := by {
            simp [group_pow]
          }
          rw [this]
          rw [pow_comm_aux]
          rw [← MyGroup.mul_assoc]
          simp at h_m
          rw [h_m]
          clear h_m this
          repeat rw [MyGroup.mul_assoc]
          rw [MyGroup.inv_mul, MyGroup.mul_inv, MyGroup.mul_one]
      case negSucc m' =>
        sorry
    case succ n' h_n =>
      nth_rewrite 1 [group_pow]
      nth_rewrite 3 [group_pow]
      simp
      simp [group_pow_nat]
      rw [group_pow] at h_n
      simp at h_n
      simp [group_pow_nat] at h_n
      have : group_pow_nat g n' = group_pow g n' := by simp [group_pow]
      rw [this]
      rw [pow_comm_aux]
      repeat rw [← MyGroup.mul_assoc]
      rw [pow_comm_aux]
      rw [← this]
      clear this
      rw [MyGroup.mul_assoc]
      sorry
}


--------------------------------------------------------------
-- g^(z+1) = g^z * g
theorem pow_add_one_nat_lemma {G : Type} [MyGroup G] (g : G) (n : ℕ) :
group_pow g (n+1) = MyGroup.mul (group_pow g n) g := by {
  rw [← pow_comm_aux]
  nth_rewrite 2 [group_pow]
  simp
  rw [← group_pow_nat]
  have : (↑n + 1) = Int.ofNat (n+1) := by simp
  rw [this]
  simp [group_pow]
}


theorem pow_add_one_lemma {G : Type} [MyGroup G] (g : G) (z : ℤ) :
group_pow g (z+1) = MyGroup.mul (group_pow g z) g := by {
  cases z
  case ofNat n =>
    have : Int.ofNat n + 1 = Int.ofNat (n+1) := by simp
    rw [this]
    nth_rewrite 1 [group_pow]
    simp
    rw [group_pow_nat]
    rw [← pow_comm_aux]
    simp [group_pow]
  case negSucc n' =>
    nth_rewrite 2 [group_pow]
    simp
    have : group_pow_nat g (n' + 1) = group_pow g (n'+1) := by {
      have : (n' + 1) = Int.ofNat (n'+1) := by simp
      rw [this]
      rw [group_pow]
    }
    rw [this]
    rw [pow_add_one_nat_lemma]
    clear this
    simp [Int.negSucc_eq]
    rw [← pow_comm_aux]
    rw [mul_inv_lemma]
    rw [MyGroup.mul_assoc]
    rw [MyGroup.inv_mul, MyGroup.mul_one]
    nth_rewrite 2 [group_pow]
    simp

    cases n'
    case zero =>
      simp [group_pow, group_pow_nat]
      rw [inv_one_lemma]
    case succ n =>
      have : -↑(n + 1) = Int.negSucc n := by {
        simp [Int.negSucc_eq]
      }
      rw [this]
      simp [group_pow]
}

theorem pow_sub_one_lemma {G : Type} [MyGroup G] (g : G) :
group_pow g (a - 1) = MyGroup.mul (group_pow g a) (MyGroup.inv g) := by {
  sorry
}

--------------------------------------------------------------
-- g^(a+b) = g^a * g^b
theorem pow_sum_lemma {G : Type} [MyGroup G] (g : G) (a b : ℤ) :
group_pow g (a + b) = MyGroup.mul (group_pow g a) (group_pow g b) := by {
  cases a
  case ofNat a =>
    induction a
    case zero =>
      simp
      nth_rewrite 2 [group_pow]
      simp [group_pow_nat]
      rw [MyGroup.one_mul]
    case succ a' h_a =>
      simp
      rw [add_comm, ← add_assoc]
      rw [pow_add_one_lemma]
      have : b + ↑a' = Int.ofNat a' + b := by {
        simp [add_comm]
      }
      rw [this, h_a]
      rw [pow_add_one_lemma]
      repeat rw [MyGroup.mul_assoc]
      rw [← pow_comm_aux]
      rfl
  case negSucc a =>
    induction a
    case zero =>
      simp
      rw [add_comm, ←sub_eq_add_neg]
      rw [pow_sub_one_lemma]
      have : -1 = Int.negSucc 0 := by simp
      rw [this]
      rw [pow_comm_lemma]
      nth_rewrite 3 [group_pow]
      simp [group_pow_nat]
      rw [MyGroup.mul_one]
    case succ a' h_a =>
      have : (Int.negSucc (a' + 1) + b) = Int.negSucc a' + b -1 := by {
        simp [Int.negSucc_eq]
        ring
      }
      rw [this]
      clear this
      rw [pow_sub_one_lemma]
      rw [h_a]
      clear h_a
      have : (Int.negSucc (a' + 1)) = Int.negSucc a' - 1 := by simp
      rw [this]
      rw [pow_sub_one_lemma]
      have : (MyGroup.inv g) = group_pow g (Int.negSucc 0) := by {
        simp [group_pow]
        simp [group_pow_nat]
        rw [MyGroup.mul_one]
      }
      rw [this]
      repeat rw [MyGroup.mul_assoc]
      rw [pow_comm_lemma]
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


----------------------------------------------------------------
-- define nZ as a normal subgroup of Z
def nZ (n : ℤ) : normal_subgroup ℤ := {
  carrier := { x | ∃ z : ℤ, x = n*z }
  nonempty := by {
    have : 0 ∈ {x | ∃ z, x = n * z} := by {
      simp
    }
    contrapose! this
    rw [Set.eq_empty_iff_forall_not_mem] at this
    apply this
  }
  mul_mem := by {
    intros a b
    intro h
    simp [MyGroup.mul]
    simp at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨z1, h1⟩ := h1
    obtain ⟨z2, h2⟩ := h2
    rw [h1, h2]
    use z1+z2
    ring
  }
  inv_mem := by {
    intro a
    simp [MyGroup.inv]
    intro x h
    rw [h]
    use x.neg
    have : -(n*x) = n*(-x) := by simp
    apply this
  }
  normal := by {
    simp [left_coset, right_coset]
    intro g
    simp [MyGroup.mul]
    ext x
    simp
    constructor
    intro h
    obtain ⟨a, h1, h2⟩ := h
    obtain ⟨z, h1⟩ := h1
    use a
    constructor
    use z
    rw [Int.add_comm]
    exact h2
    intro h
    obtain ⟨a, h1, h2⟩ := h
    obtain ⟨z, h1⟩ := h1
    use a
    constructor
    use z
    rw [Int.add_comm]
    rw [h2]
  }
}

--------------------------------------------------------------
-- Lemma 2.1.5:
-- every subgroup of ℤ looks like this for a n ∈ ℤ: {n*z | z ∈ Z}
theorem lemma_2_1_5 (H : Subgroup ℤ) :
∃ n : ℤ, H = nZ n := by {
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
    obtain ⟨carrier, _⟩ := H
    use 0
    simp [normal_sg_to_sg]
    simp at h_case
    rw [h_case]
    rw [nZ]
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
    obtain ⟨carrier, _, mul_mem, inv_mem⟩ := H
    simp at h_0 h_case h_min
    simp [normal_sg_to_sg]
    ext x
    constructor
    -- H ⊆ n*ℤ
    intro h_x
    rw [nZ]
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

    have h3 : b ∈ carrier := by {
      have h_tmp : b = x - n*a := by {
        rw [h2]
        simp
      }
      rw [h_tmp]
      rw [sub_eq_add_neg]
      apply mul_mem
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
          apply mul_mem
          constructor
          exact h_a
          apply inv_mem
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
          apply mul_mem
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
        apply mul_mem
        constructor
        exact h_z
        exact h_nH
    case negSucc z =>
      rw [h_x]
      clear h_x
      induction z
      case zero =>
        simp
        apply inv_mem
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
        apply mul_mem
        constructor
        exact h_z
        apply inv_mem
        exact h_nH
}


--------------------------------------------------------------
-- let G be a group, H ⊆ G. H is a subgroup iff H is not empty, and
-- ∀ h1, h2 ∈ H, h1⁻¹*h2 ∈ H
theorem subgroup_iff_lemma (G : Type) [MyGroup G] (H : Set G) :
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

  have h_inv : (∀ a : G, a ∈ H → MyGroup.inv a ∈ H) := by {
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
theorem subgroup_one_mem_lemma (G : Type) [MyGroup G] (H : Subgroup G) :
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
theorem bijective_has_inverse_lemma {A B : Type} (f : A → B)
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
theorem inverse_is_bijective_lemma {A B : Type} (f : A -> B)
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
theorem isomorphism_is_invertable_lemma (G1 G2 : Type)
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
theorem invertable_homomorphism_is_isomorphism_lemma (G1 G2 : Type)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2)
(h_inv : ∃ ψ : GroupHomomorphism G2 G1,
(∀ x2 : G2, φ.f (ψ.f x2) = x2) ∧
(∀ x1 : G1, ψ.f (φ.f x1) = x1)) : Function.Bijective φ.f := by {
  obtain ⟨ψ, h_inv⟩ := h_inv
  apply inverse_is_bijective_lemma
  use ψ.f
}


-------------------------------------------------------------------
-- group homomorphisms map the neutral element of G1 to the neutral element of G2
theorem homomorphism_neutral_element_lemma (G1 G2 : Type)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2) :
φ.f MyGroup.one = MyGroup.one := by {
  let e1 : G1 := MyGroup.one

  have h : φ.f e1 = MyGroup.mul (φ.f e1) (φ.f e1) := by {
    have h1 : MyGroup.mul e1 e1 = e1 := by {
      rw [MyGroup.mul_one]
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
}


------------------------------------------------------------------
-- group homomorphisms map the inverse element to the inverse element
theorem homomorphism_inverse_element_lemma (G1 G2 : Type)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2) :
∀ x1 : G1, φ.f (MyGroup.inv x1) = MyGroup.inv (φ.f x1) := by {
  intro x1
  have h : φ.f (MyGroup.mul (MyGroup.inv x1) x1) = MyGroup.one := by {
    rw [MyGroup.inv_mul]
    rw [homomorphism_neutral_element_lemma]
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
theorem left_coset_eq_lemma (G : Type) [MyGroup G] (H : Subgroup G) (g1 g2 : G) :
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
theorem right_coset_eq_lemma (G : Type) [MyGroup G] (H : Subgroup G) (g1 g2 : G) :
right_coset G H g1 = right_coset G H g2 ↔
MyGroup.mul g1 (MyGroup.inv g2) ∈ H.carrier := by {
  -- ->
  constructor
  intro h3
  repeat rw [right_coset] at h3
  have h_g2 : g1 ∈ {x | ∃ h : H.carrier, x = MyGroup.mul ↑h g1 } ->
              g1 ∈ {x | ∃ h : H.carrier, x = MyGroup.mul ↑h g2 } := by {
    intro h_h
    rw [← h3]
    exact h_h
  }

  have h1 : g1 ∈ {x | ∃ h : H.carrier, x = MyGroup.mul ↑h g1} := by {
    simp
    use MyGroup.one
    constructor
    apply subgroup_one_mem_lemma
    rw [MyGroup.one_mul]
  }

  have h2 : g1 ∈ {x | ∃ h : H.carrier, x = MyGroup.mul ↑h g2} := by {
    apply h_g2
    exact h1
  }

  simp at h2
  obtain ⟨a, h_a, h2⟩ := h2

  have h3 : MyGroup.mul g1 (MyGroup.inv g2) =
            MyGroup.mul (MyGroup.mul a g2) (MyGroup.inv g2) := by {
    rw [← group_cancel_rule_right_lemma]
    exact h2
  }

  rw [MyGroup.mul_assoc] at h3
  rw [MyGroup.mul_inv] at h3
  rw [MyGroup.mul_one] at h3
  rw [← h3] at h_a
  exact h_a

  -- <-
  intro h
  repeat rw [right_coset]

  ext x
  simp
  constructor
  intro h2
  obtain ⟨a, h2, h3⟩ := h2
  use (MyGroup.mul a (MyGroup.mul g1 (MyGroup.inv g2)))
  constructor
  apply Subgroup.mul_mem
  exact ⟨h2, h⟩
  repeat rw [← MyGroup.mul_assoc]
  rw [← h3]
  rw [MyGroup.mul_assoc]
  rw [MyGroup.inv_mul, MyGroup.mul_one]

  intro h2
  obtain ⟨a, h2, h3⟩ := h2
  use (MyGroup.mul a (MyGroup.mul g2 (MyGroup.inv g1)))
  constructor
  apply Subgroup.mul_mem
  constructor
  exact h2
  rw [← double_inv_lemma g2]
  rw [← mul_inv_lemma]
  apply Subgroup.inv_mem
  exact h
  repeat rw [MyGroup.mul_assoc]
  rw [MyGroup.inv_mul, MyGroup.mul_one]
  exact h3
}


-------------------------------------------------------------------
-- H is a normal Subgroup ↔ ∀ h ∈ H, g ∈ G -> g⁻¹hg ∈ H
theorem normal_iff_lemma {G : Type} [MyGroup G] (H : Subgroup G) :
(∀ g : G, left_coset G H g = right_coset G H g) ↔
(∀ h : H.carrier, ∀ g : G, MyGroup.mul (MyGroup.mul (MyGroup.inv g) h) g ∈ H.carrier) := by {
  -- ->
  constructor
  intro h1
  intros h g
  have h_normal : left_coset G H g = right_coset G H g := by {
    apply h1
  }

  -- h*g ∈ Hg
  have h_hg : MyGroup.mul ↑h g ∈ (right_coset G H g) := by {
    rw [right_coset]
    simp
    use h
    simp
  }

  -- Hg = gH -> h*g ∈ gH
  have h_hg2 : MyGroup.mul ↑h g ∈ (left_coset G H g) := by {
    rw [h_normal]
    exact h_hg
  }

  -- this means, there exists a h', such that h*g = g*h'
  have h_h' : ∃ h' ∈ H.carrier, MyGroup.mul ↑h g = MyGroup.mul g ↑h' := by {
    rw [left_coset] at h_hg2
    simp at h_hg2
    exact h_hg2
  }

  -- h' = g⁻¹*h*g
  obtain ⟨h', h_h', h_hh'⟩ := h_h'
  have h_eq : h' = MyGroup.mul (MyGroup.mul (MyGroup.inv g) ↑h) g := by {
    have h_tmp : MyGroup.mul (MyGroup.inv g) (MyGroup.mul (↑h) g) =
                 MyGroup.mul (MyGroup.inv g) (MyGroup.mul g h') := by {
      rw [← group_cancel_rule_left_lemma]
      exact h_hh'
    }
    repeat rw [← MyGroup.mul_assoc] at h_tmp
    rw [MyGroup.inv_mul] at h_tmp
    rw [MyGroup.one_mul] at h_tmp
    symm
    exact h_tmp
  }
  rw [← h_eq]
  apply h_h'

  -- <-
  intro h
  intro g
  rw [left_coset, right_coset]
  -- ⊆
  ext x
  simp
  constructor
  intro h1
  obtain ⟨a, h_a, h_aa⟩ := h1
  specialize h ⟨a, h_a⟩ (MyGroup.inv g)
  simp at h

  use MyGroup.mul (MyGroup.mul (MyGroup.inv (MyGroup.inv g)) a) (MyGroup.inv g)
  constructor
  --rw [h1]
  apply h
  rw [MyGroup.mul_assoc]
  rw [MyGroup.inv_mul]
  rw [MyGroup.mul_one]
  rw [double_inv_lemma]
  rw [h_aa]

  -- ⊇
  intro h1
  obtain ⟨a, h_a, h_aa⟩ := h1
  specialize h ⟨a, h_a⟩ g
  simp at h

  use MyGroup.mul (MyGroup.mul (MyGroup.inv g) a) g
  constructor
  exact h
  repeat rw [← MyGroup.mul_assoc]
  rw [MyGroup.mul_inv]
  rw [MyGroup.one_mul]
  exact h_aa
}

theorem normal_subgroup_iff_lemma {G : Type} [MyGroup G] (K : Set G) :
(∃ H : normal_subgroup G, H.carrier = K) ↔
(∃ H : Subgroup G, H.carrier = K ∧
∀ h : H.carrier, ∀ g : G, MyGroup.mul (MyGroup.mul (MyGroup.inv g) h) g ∈ K) := by {
  -- ->
  constructor
  intro h1
  obtain ⟨H, h1⟩ := h1
  use H
  constructor
  exact h1
  rw [← h1]
  have : H.carrier = (normal_sg_to_sg H).carrier := by norm_cast
  rw [this]
  rw [← normal_iff_lemma ↑(normal_sg_to_sg H)]
  exact H.normal

  -- <-
  intro h1
  obtain ⟨H, h1, h2⟩ := h1
  rw [← h1] at h2
  rw [← normal_iff_lemma] at h2
  let H' : normal_subgroup G := {
    toSubgroup := H
    normal := h2
  }
  use H'
}

--------------------------------------------------------------------
-- in an abelian group, every subgroup is normal
theorem abelian_subgroup_is_normal_lemma (G : Type) [AbelianGroup G] (K : Set G) :
(∃ H : Subgroup G, H.carrier = K) -> (∃ H : normal_subgroup G, H.carrier = K) := by {
  intro h
  obtain ⟨H, h1⟩ := h

  have : (∀ h : H.carrier, ∀ g : G, MyGroup.mul (MyGroup.mul (MyGroup.inv g) h) g ∈ K) := by {
    intros h g
    rw [AbelianGroup.mul_comm]
    rw [← MyGroup.mul_assoc]
    rw [MyGroup.mul_inv]
    rw [MyGroup.one_mul]
    rw [← h1]
    simp
  }

  let H' : normal_subgroup G := {
    toSubgroup := H
    normal := by {
      rw [normal_iff_lemma]
      rw [← h1] at this
      exact this
    }
  }
  use H'
}


-- Lemma 2.1.11
---------------------------------------------------------------------
-- ker φ is a normal subgroup
def ker_to_normal_subgroup {G1 G2 : Type} [MyGroup G1] [MyGroup G2]
(φ : GroupHomomorphism G1 G2) : normal_subgroup G1 := {
  carrier := ker φ
  nonempty := by {
    have h : MyGroup.one ∈ ker φ := by {
      rw [ker]
      simp
      apply homomorphism_neutral_element_lemma
    }
    contrapose! h
    rw [Set.eq_empty_iff_forall_not_mem] at h
    apply h
  }
  mul_mem := by {
    rw [ker]
    simp
    intros a b
    intros h_a h_b
    rw [GroupHomomorphism.mul]
    rw [h_a, h_b]
    rw [MyGroup.mul_one]
  }
  inv_mem := by {
    rw [ker]
    simp
    intro a
    intro h
    rw [homomorphism_inverse_element_lemma]
    rw [h]
    have h_tmp : (MyGroup.mul (MyGroup.inv MyGroup.one) MyGroup.one : G2) =
                 MyGroup.mul MyGroup.one MyGroup.one := by {
      rw [MyGroup.one_mul]
      rw [MyGroup.inv_mul]
    }
    rw [← group_cancel_rule_right_lemma] at h_tmp
    exact h_tmp
  }
  normal := by {
    rw [normal_iff_lemma]
    simp
    intros h h_ker g
    rw [ker]
    simp
    repeat rw [GroupHomomorphism.mul]
    rw [homomorphism_inverse_element_lemma]
    have h_tmp : ∃ h' : G1, h' = h ∧ h' ∈ ker φ := by {
      use h
    }
    obtain ⟨h', h_h, h_tmp⟩ := h_tmp
    rw [h_h] at h_tmp
    rw [ker] at h_tmp
    simp at h_tmp
    rw [h_tmp]
    rw [MyGroup.mul_one]
    rw [MyGroup.inv_mul]
  }
}


theorem kernel_is_normal_subgroup_lemma (G1 G2 : Type)
[MyGroup G1] [MyGroup G2] (φ : GroupHomomorphism G1 G2) :
∃ N : normal_subgroup G1, N.carrier = ker φ := by {
  use ker_to_normal_subgroup φ
  rw [ker_to_normal_subgroup]
}

--------------------------------------------------------------------
-- im φ is a subgroup
def image_to_subgroup {G1 G2 : Type} [MyGroup G1] [MyGroup G2]
(φ : GroupHomomorphism G1 G2) : Subgroup G2 := {
  carrier := im φ
  nonempty := by {
    have h : MyGroup.one ∈ im φ := by {
      rw [im]
      simp
      use MyGroup.one
      rw [homomorphism_neutral_element_lemma]
    }
    contrapose! h
    rw [Set.eq_empty_iff_forall_not_mem] at h
    apply h
  }
  mul_mem := by {
    rw [im]
    intros a b
    intro ⟨h_a, h_b⟩
    simp at h_a h_b
    simp
    obtain ⟨a', h_a⟩ := h_a
    obtain ⟨b', h_b⟩ := h_b
    use MyGroup.mul a' b'
    rw [GroupHomomorphism.mul]
    rw [h_a, h_b]
  }
  inv_mem := by {
    rw [im]
    intro a
    intro h_a
    simp at h_a
    simp
    obtain ⟨a', h_a⟩ := h_a
    use MyGroup.inv a'
    rw [homomorphism_inverse_element_lemma]
    rw [h_a]
  }
}

theorem image_is_subgroup_lemma (G1 G2 : Type) [MyGroup G1] [MyGroup G2]
(φ : GroupHomomorphism G1 G2) : ∃ H : Subgroup G2, H.carrier = im φ := by {
  use image_to_subgroup φ
  rw [image_to_subgroup]
}

instance image_is_group {G1 G2 : Type} [MyGroup G1] [MyGroup G2]
(φ : GroupHomomorphism G1 G2) : MyGroup (im φ) := {
  mul := λ x y => by {
    rw [im] at x y
    obtain ⟨x, h_x⟩ := x
    obtain ⟨y, h_y⟩ := y
    simp at h_x h_y
    have : MyGroup.mul x y ∈ im φ := by {
      rw [im]
      simp
      obtain ⟨g_x, h_x⟩ := h_x
      obtain ⟨g_y, h_y⟩ := h_y
      use MyGroup.mul g_x g_y
      rw [GroupHomomorphism.mul]
      rw [h_x, h_y]
    }
    exact ⟨MyGroup.mul x y, this⟩
  }
  one := by {
    have : MyGroup.one ∈ im φ := by {
      rw [im]
      simp
      use MyGroup.one
      rw [homomorphism_neutral_element_lemma]
    }
    exact ⟨MyGroup.one, this⟩
  }
  inv := by {
    intro x
    obtain ⟨x, h_x⟩ := x
    have : MyGroup.inv x ∈ im φ := by {
      rw [im]
      simp
      rw [im] at h_x
      simp at h_x
      obtain ⟨g_x, h_x⟩ := h_x
      use MyGroup.inv g_x
      rw [homomorphism_inverse_element_lemma]
      rw [h_x]
    }
    exact ⟨MyGroup.inv x, this⟩
  }
  mul_assoc := by {
    intros x y z
    simp
    apply MyGroup.mul_assoc
  }
  one_mul := by {
    simp
    intros x _
    apply MyGroup.one_mul
  }
  mul_one := by {
    simp
    intros x _
    apply MyGroup.mul_one
  }
  inv_mul := by {
    simp
    intros x _
    apply MyGroup.inv_mul
  }
  mul_inv := by {
    simp
    intros x _
    apply MyGroup.mul_inv
  }
}


--------------------------------------------------------------------
-- φ is injective ↔ ker φ = { one }
theorem homomorphism_injective_iff_lemma (G1 G2 : Type) [MyGroup G1]
[MyGroup G2] (φ : GroupHomomorphism G1 G2) :
Function.Injective φ.f ↔ ker φ = { MyGroup.one } := by {
  -- ->
  constructor
  intro h
  rw [Function.Injective] at h
  rw [ker]
  ext x
  constructor
  simp
  intro h_x
  have h_e : φ.f MyGroup.one = MyGroup.one := by {
    rw [homomorphism_neutral_element_lemma]
  }
  apply h
  rw [h_e]
  exact h_x

  simp
  intro h_x
  rw [h_x]
  rw [homomorphism_neutral_element_lemma]

  -- <-
  intro h
  contrapose! h
  rw [Function.Injective] at h
  simp at h

  obtain ⟨a, b, h_eq, h⟩ := h

  have h_ne_one : MyGroup.mul b (MyGroup.inv a) ≠ MyGroup.one := by {
    contrapose! h
    have h_tmp : MyGroup.mul (MyGroup.mul b (MyGroup.inv a)) a =
                 MyGroup.mul MyGroup.one a := by {
      rw [← group_cancel_rule_right_lemma]
      exact h
    }
    rw [MyGroup.mul_assoc] at h_tmp
    rw [MyGroup.inv_mul] at h_tmp
    rw [MyGroup.mul_one, MyGroup.one_mul] at h_tmp
    symm
    exact h_tmp
  }

  have h_mem : MyGroup.mul b (MyGroup.inv a) ∈ ker φ := by {
    rw [ker]
    simp
    rw [GroupHomomorphism.mul]
    rw [homomorphism_inverse_element_lemma]
    rw [h_eq]
    rw [MyGroup.mul_inv]
  }

  intro h_ker

  have h_eq_one : MyGroup.mul b (MyGroup.inv a) = MyGroup.one := by {
    rw [h_ker] at h_mem
    simp at h_mem
    exact h_mem
  }

  exact h_ne_one h_eq_one
}


-- Proposition 2.1.12
-------------------------------------------------------------------
-- left cosets are disjoint, or equal
theorem left_cosets_disjoint_lemma (G : Type) [MyGroup G]
(H : Subgroup G) (g1 g2 : G) : left_coset G H g1 = left_coset G H g2 ∨
(left_coset G H g1) ∩ (left_coset G H g2) = ∅ := by {
  by_cases h_case : left_coset G H g1 = left_coset G H g2
  case pos =>
    left
    exact h_case

  case neg =>
    right
    contrapose! h_case
    rw [Set.nonempty_iff_ne_empty] at h_case
    have h_a : ∃ x : G, x ∈ left_coset G H g1 ∧ x ∈ left_coset G H g2 := by {
      contrapose! h_case
      rw [Set.eq_empty_iff_forall_not_mem]
      simp
      exact h_case
    }
    obtain ⟨x, h_x1, h_x2⟩ := h_a
    obtain ⟨a1, h_x1⟩ := h_x1
    obtain ⟨a2, h_x2⟩ := h_x2
    clear h_case

    rw [left_coset_eq_lemma]
    have h_a1 : a1 = MyGroup.mul (MyGroup.mul (MyGroup.inv g1) g2) a2 := by {
      rw [MyGroup.mul_assoc]
      rw [← h_x2]
      rw [h_x1]
      rw [← MyGroup.mul_assoc]
      rw [MyGroup.inv_mul, MyGroup.one_mul]
    }

    have h : MyGroup.mul (MyGroup.inv g1) g2 =
             MyGroup.mul (MyGroup.mul (MyGroup.inv g1) g2)
                         (MyGroup.mul a2 (MyGroup.inv a2)) := by {
      rw [MyGroup.mul_inv]
      rw [MyGroup.mul_one]
    }
    rw [h]
    repeat rw [← MyGroup.mul_assoc]
    apply Subgroup.mul_mem
    constructor
    rw [← h_a1]
    simp

    apply Subgroup.inv_mem
    simp
}


---------------------------------------------------------------------
-- cosets have the same cardinality
theorem left_coset_cardianlity_lemma (G : Type) [MyGroup G]
(H : Subgroup G) (g : G) :
same_cardinality H.carrier (left_coset G H g) := by {
  rw [same_cardinality]
  use (λ h => by {
    rw [left_coset]
    use ↑(MyGroup.mul g ↑h)
    simp
    use h
    simp
  })
  rw [Function.Bijective]
  constructor
  rw [Function.Injective]
  simp
  intros _ _ _ _ h
  rw [← group_cancel_rule_left_lemma] at h
  exact h
  rw [Function.Surjective]
  simp
  rw [left_coset]
  intros a h_a
  simp at h_a
  obtain ⟨a_1, h_a, h_aa⟩ := h_a
  use a_1
  constructor
  exact h_a
  symm
  exact h_aa
}

theorem right_coset_cardianlity_lemma (G : Type) [MyGroup G]
(H : Subgroup G) (g : G) :
same_cardinality H.carrier (right_coset G H g) := by {
  rw [same_cardinality]
  use (λ h => by {
    rw [right_coset]
    use ↑(MyGroup.mul ↑h g)
    simp
    use h
    simp
  })
  rw [Function.Bijective]
  constructor
  rw [Function.Injective]
  simp
  intros _ _ _ _ h
  rw [← group_cancel_rule_right_lemma] at h
  exact h
  rw [Function.Surjective]
  simp
  rw [right_coset]
  intros a h_a
  simp at h_a
  obtain ⟨a_1, h_a, h_aa⟩ := h_a
  use a_1
  constructor
  exact h_a
  symm
  exact h_aa
}

-----------------------------------------------------------------
-- G is the union of its cosets
theorem left_coset_union_lemma (G : Type) [MyGroup G] (H : Subgroup G) :
⋃ g : G, (left_coset G H g) = { x | ∃ g : G, x = g } := by {
  ext g
  simp
  use g
  rw [left_coset]
  simp
  use MyGroup.one
  constructor
  apply subgroup_one_mem_lemma
  rw [MyGroup.mul_one]
}

theorem right_coset_union_lemma (G : Type) [MyGroup G] (H : Subgroup G) :
⋃ g : G, (right_coset G H g) = { x | ∃ g : G, x = g } := by {
  ext g
  simp
  use g
  rw [right_coset]
  simp
  use MyGroup.one
  constructor
  apply subgroup_one_mem_lemma
  rw [MyGroup.one_mul]
}


-- theorem 2.1.13 (Lagrange theorem)
-- difficult with cardinality

/-

-- theorem 2.1.16
theorem coset_mul_welldefined_lemma ( G : Type) [MyGroup G] (H : normal_subgroup G)
(a a' b b' : left_coset' G H) :
a.carrier = a'.carrier ∧ b.carrier = b'.carrier ->
(left_coset_mul a b).carrier = (left_coset_mul a' b').carrier := by {
  intro h
  obtain ⟨h1, h2⟩ := h
  repeat rw [left_coset'.h_carrier] at h1 h2 ⊢
  rw [left_coset_eq_lemma] at h1 h2 ⊢

  -- we use, that H is normal
  have h : ∃ h : H.carrier, MyGroup.mul (MyGroup.mul (MyGroup.inv a.g) a'.g) b'.g =
                  MyGroup.mul b'.g h := by {
    have h_K : (∃ H' : normal_subgroup G, H'.carrier = H.carrier) := by {
      use H
    }
    have h_normal : ∀ h : H.carrier, ∀ g : G,
        MyGroup.mul (MyGroup.mul (MyGroup.inv g) h) g ∈ H.carrier := by {
      rw [normal_subgroup_iff_lemma H.carrier] at h_K
      obtain ⟨H', h_eq, h⟩ := h_K
      rw [h_eq] at h
      exact h
    }
    let g : H.carrier := by {
      use (MyGroup.mul (MyGroup.inv a.g) a'.g)
      exact h1
    }
    specialize h_normal g b'.g

    let gg : H.carrier := by {
      use (MyGroup.mul (MyGroup.mul (MyGroup.inv b'.g) ↑g) b'.g)
    }
    use gg
    simp [gg]
    repeat rw [← MyGroup.mul_assoc]
    rw [MyGroup.mul_inv, MyGroup.one_mul]
  }


  obtain ⟨h, h3⟩ := h
  repeat rw [left_coset_mul]
  simp
  rw [mul_inv_lemma]
  repeat rw [MyGroup.mul_assoc]
  nth_rewrite 2 [← MyGroup.mul_assoc]
  rw [h3]
  rw [← MyGroup.mul_assoc]
  apply Subgroup.mul_mem
  constructor
  apply h2
  have : ↑h ∈ H.carrier := by simp
  apply this
}


theorem coset_inv_welldefined_lemma (G : Type) [MyGroup G] (H : normal_subgroup G)
(a a' : left_coset' G H) :
a.carrier = a'.carrier ->
(left_coset_inv a).carrier = (left_coset_inv a').carrier := by {
  intro h
  repeat rw [left_coset_inv]
  simp
  -- the inverse element in a group is always welldefined
  sorry
}


-----------------------------------------------------------------------------
-- the set of all left cosets is a group
instance (G : Type) [MyGroup G] (H : normal_subgroup G) :
MyGroup (left_coset' G H) := {
  mul := left_coset_mul
  one := left_coset_one
  inv := left_coset_inv
  mul_assoc := by {
    intros a b c
    obtain ⟨g_a, _⟩ := a
    obtain ⟨g_b, _⟩ := b
    obtain ⟨g_c, _⟩ := c

    have : MyGroup.mul (MyGroup.mul g_a g_b) g_c = MyGroup.mul g_a (MyGroup.mul g_b g_c) := by {
      apply MyGroup.mul_assoc
    }
    repeat rw [left_coset_mul]
    simp
    constructor
    exact this
    rw [this]
  }
  one_mul := by {
    intro a
    obtain ⟨a, g, h_a, h⟩ := a
    rw [left_coset_mul, left_coset_one]
    simp
    constructor
    apply MyGroup.one_mul
    rw [MyGroup.one_mul]
  }
  mul_one := by {
    intro a
    obtain ⟨a, g, h_a, h⟩ := a
    rw [left_coset_mul, left_coset_one]
    simp
    constructor
    apply MyGroup.mul_one
    rw [MyGroup.mul_one]
  }
  inv_mul := by {
    intro a
    obtain ⟨g_a, _⟩ := a
    rw [left_coset_mul, left_coset_inv, left_coset_one]
    simp
    constructor
    apply MyGroup.inv_mul
    have : (MyGroup.mul (MyGroup.inv g_a) g_a) = MyGroup.one := by {
      apply MyGroup.inv_mul
    }
    rw [this]
  }
  mul_inv := by {
    intro a
    obtain ⟨g_a, _⟩ := a
    rw [left_coset_mul, left_coset_inv, left_coset_one]
    simp
    have : MyGroup.mul g_a (MyGroup.inv g_a) = MyGroup.one := by {
      apply MyGroup.mul_inv
    }
    constructor
    exact this
    rw [this]
  }
}
-/

-- Theorem 2.1.19 (difficult with cardinality)
