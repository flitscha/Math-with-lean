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

def G1 : Type u := sorry
def G2 : Type v := sorry
instance : MyGroup G1 := sorry
instance : MyGroup G2 := sorry
def ψ : GroupHomomorphism G1 G2 := {
  f := id
  mul := sorry
}
def φ : GroupIsomorphism G1 G2 := sorry
def φf : G1 -> G2 := φ.f

def x : G2 := sorry
def h_inj : ∀ ⦃x1 x2 : G1⦄, (φ.f : G1 -> G2) x1 = (φ.f : G1 -> G2) x2 → x1 = x2 := φ.injective
#check φ.f   -- Dies sollte G1 → G2 sein
#check φ.injective   -- Dies sollte Injektivität von φ.f sein
#check h_inj
--def a : idGroupMorphism G1 := sorry
--#check a.f
#check ψ
#check (φ.f : G1 -> G2)
#check φ.injective
#check (φ.f : G1 → G2)
--def a : GroupHomomorphism G2 G2 := idGroupMorphism G2

theorem isomorphism_is_invertable_lemma (G1 : Type u) (G2 : Type v)
[MyGroup G1] [MyGroup G2] (φ : GroupIsomorphism G1 G2) :
∃ ψ : GroupHomomorphism G2 G1,
∀ x2 : G2, φ.f (ψ.f x2) = x2 ∧
∀ x1 : G1, ψ.f (φ.f x1) = x1 := by {

  let φ_f : G1 -> G2 := φ.f

  have h_φ_inj : Function.Injective φ_f := φ.injective
  -- this seems strange. h_inj has the type: Function.Injective GroupHomomorphism.f
  -- but a few details are hidden. The real type is:
  -- Function.Injective (@GroupHomomorphism.f G1 G2 inst✝¹ inst✝ φ.toGroupHomomorphism)
  have h_φ_sur : Function.Surjective φ_f := φ.surjective

  have h_one_to_one : ∀ x2 : G2, ∃! x1 : G1, φ_f x1 = x2 := by {
    intro x2
    obtain ⟨x1, hx1⟩ := h_φ_sur x2
    use x1
    simp
    constructor
    exact hx1
    intro y1
    intro h
    apply h_φ_inj
    rw [h, hx1]
  }

  rw [Function.Injective] at h_φ_inj
  rw [Function.Surjective] at h_φ_sur

  let ψ_f : G2 -> G1 := λ x2 : G2 =>
    Classical.choose (h_one_to_one x2)
    --let ⟨x1, hx1⟩ := h_φ_sur x2 in
    --x1,

  --let ψ_f : G2 → G1 := λ x2 : G2 => by {
  --  have : ∃! x1, φ_f x1 = x2 := by {
  --    apply h_one_to_one
  --  }
  --  exact Classical.choose this
  --}

  have ψ_f_is_homomorphism : ∀ x2 y2 : G2, ψ_f (MyGroup.mul x2 y2) = MyGroup.mul (ψ_f x2) (ψ_f y2) := by {
    intros x2 y2

    let ⟨x1, hx1⟩ := h_φ_sur x2
    let ⟨y1, hy1⟩ := h_φ_sur y2
    have h_mul : φ_f (ψ_f (MyGroup.mul x2 y2)) = MyGroup.mul (φ_f (ψ_f x2)) (φ_f (ψ_f y2)) := by {
      have h_inv : ∀ z2 : G2, φ_f (ψ_f z2) = z2 := by {
        intro z2
        let ⟨z1, hz1⟩ := h_φ_sur z2
        simp [φ_f, ψ_f]


      }
      --rw [MyGroup.mul, φ.mul]
      --exact MyGroup.mul (φ.f (ψ_f x2)) (φ.f (ψ_f y2))
      sorry
    }

    sorry
  }

  let ψ : GroupHomomorphism G2 G1 := {
    f := ψ_f
    mul := ψ_f_is_homomorphism
  }





}




theorem test_lemma (G1 : Type u) (G2 : Type v)
[MyGroup G1] [MyGroup G2] (φ : GroupIsomorphism G1 G2) :
∀ ψ : GroupHomomorphism G1 G2, Function.Injective ψ.f := by {
  have h_inj : Function.Injective (φ.f : G1 → G2) := φ.injective
  intro ψ

  exact h_inj
}

-- Annahmen
variables {G1 G2 : Type} (φ_f : G1 → G2)

-- Beweis, dass φ_f bijektiv ist
theorem bijective_has_inverse (h_one_to_one : ∀ (x2 : G2), ∃! x1, φ_f x1 = x2) :
∃ (φ_f_inv : G2 → G1), (∀ x2 : G2, φ_f (φ_f_inv x2) = x2) ∧ (∀ x1 : G1, φ_f_inv (φ_f x1) = x1) := by {

  let φ_f_inv : G2 → G1 := λ x2 : G2 => Classical.choose (h_one_to_one x2).exists
  use φ_f_inv
  constructor

  intro x2
  have h := Classical.choose_spec (h_one_to_one x2).exists
  simp [φ_f_inv]
  exact h


  intro x1
  have h : ∀ (x1 : G1), ∃! x2 : G2, φ_f_inv x2 = x1 := by {
    sorry
  }
  specialize h x1
  have h2 := Classical.choose_spec (h).exists
  obtain ⟨x2, h⟩ := h
  simp at h
  have h4 := Classical.choose_spec (h_one_to_one x2).exists

  simp [φ_f_inv]
  obtain ⟨hh, _⟩ := h
  rw [← h4] at hh
  rw [← hh]

}
