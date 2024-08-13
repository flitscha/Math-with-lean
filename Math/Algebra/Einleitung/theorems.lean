import Math.Algebra.Einleitung.definitions
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Sqrt

-------------------------------------------------------
-- Theorem: M^(i) ⊆ M^(i+1) for all i
theorem constructable_in_steps_subset (M : Set point) (i : Nat) :
constructable_in_steps M i ⊆ constructable_in_steps M (Nat.succ i) :=
  show constructable_in_steps M i ⊆ constructable_in_steps M (Nat.succ i) by {
  match i with
  | 0 =>
    intro x hx
    rw [constructable_in_steps] at hx
    repeat rw [constructable_in_steps]
    left
    exact hx
  | Nat.succ j =>
    intro x hx
    rw [constructable_in_steps]
    left
    exact hx
}

-----------------------------------------------------
-- Lemma: let z ∈ ℂ, with z.im = 0
-- then: z.re = z
theorem real_as_complex_lemma (z : ℂ) (h : z.im = 0) :
z.re = z := by {
  rw [Complex.ext_iff]
  simp
  symm
  exact h
}

------------------------------------------------------
-- Lemma: let z1, z2 ∈ ℂ, with z1.im = 0 ∧ z2.im = 0
-- then: (z1 * z2).im = 0
theorem product_im_lemma (z1 z2 : ℂ) (h1 : z1.im = 0) (h2 : z2.im = 0) :
(z1 * z2).im = 0 := by {
  simp
  rw [h1, h2]
  simp
}

------------------------------------------------------
-- Lemma: x is the only intersection between 2 lines ↔
-- x is an intersection ∧ (p2 - p1) / (q2 - q1) ∉ ℝ
theorem only_intersection_lemma (p1 p2 q1 q2 x : ℂ) (hp : p1 ≠ p2) (hq : q1 ≠ q2) :
x_is_the_only_intersection_c p1 p2 q1 q2 x ↔
x ∈ line_through_c p1 p2 ∧ x ∈ line_through_c q1 q2 ∧
((p2 - p1) / (q2 - q1)).im ≠ 0 := by {
  -- p1 ≠ p2 ↔ p1 - p2 ≠ 0
  have h_p : p2 - p1 ≠ 0 := by {
    intro h
    apply eq_of_sub_eq_zero at h
    rw [h] at hp
    exact hp rfl
  }

  -- q1 ≠ q2 ↔ q1 - q2 ≠ 0
  have h_q : q2 - q1 ≠ 0 := by {
    intro h
    apply eq_of_sub_eq_zero at h
    rw [h] at hq
    exact hq rfl
  }

  constructor
  -- =>
  intro h
  rw [x_is_the_only_intersection_c] at h
  have ⟨h1, h2, h3⟩ := h
  -- prove the easy thing: x is an intersection
  constructor
  exact h1
  constructor
  exact h2
  -- now we want to show ((p2 - p1) / (q2 - q1)).im ≠ 0
  contrapose! h3
  use x+(p2-p1)*(p2-p1)/(q2-q1)
  --rw [line_through_c]
  --rw [Set.mem_setOf_eq]
  constructor
  constructor

      -- z ∈ line_through_c p1 p2
  rw [line_through_c] at h1 -- we need to know what x looks like
  rw [Set.mem_setOf_eq] at h1
  obtain ⟨r, hr⟩ := h1
  rw [hr] -- now we can rewrite x depending on r
  rw [line_through_c]
  rw [Set.mem_setOf_eq]
  use (r + (p2-p1)/(q2-q1)).re
  rw [real_as_complex_lemma] -- simplifying the equation
  rw [add_assoc]
  simp
  rw [add_mul]
  simp
  repeat rw [div_eq_mul_inv]
  rw [mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc]
          -- we have to show, why we can use real_as_complex_lemma:
          -- r + (p2 - p1) / (q2 - q1) ∈ ℝ
  rw [Complex.add_im]
  rw [h3]
  rw [add_zero]
  exact Complex.ofReal_im r

      -- z ∈ line_through_c q1 q2
  rw [line_through_c] at h2
  rw [Set.mem_setOf_eq] at h2
  obtain ⟨r, hr⟩ := h2
  rw [hr]
  rw [line_through_c]
  rw [Set.mem_setOf_eq]
  use (r + (p2-p1)*(p2-p1) / ((q2-q1)*(q2-q1))).re
  rw [real_as_complex_lemma]
  rw [add_assoc]
  simp
  rw [add_mul]
  simp
  repeat rw [div_eq_mul_inv]
  simp
  repeat rw [mul_assoc]
  simp
  nth_rewrite 2 [mul_comm]
  rw [mul_inv_cancel]
  simp
          -- we need to show q2 - q1 ≠ 0 for mul_inv
  contrapose! hq
  rw [sub_eq_zero] at hq
  rw [hq]
          -- we have to show, why we can use real_as_complex_lemma:
          -- r + (p2-p1)*(p2-p1) / ((q2-q1)*(q2-q1))) ∈ ℝ
  rw [Complex.add_im]
  rw [Complex.ofReal_im r]
  rw [zero_add]
  repeat rw [div_eq_mul_inv]
  rw [mul_inv]
  repeat rw [← mul_assoc]
  nth_rewrite 2 [mul_comm]
  repeat rw [← mul_assoc]
  nth_rewrite 3 [mul_comm]
  rw [mul_assoc]
  rw [product_im_lemma]
  exact h3
  exact h3

      -- z ≠ x#
  intro hx
  rw [add_comm] at hx
  rw [add_left_eq_self] at hx
  rw [div_eq_zero_iff] at hx
  simp at hx
  cases hx with
  | inl hx1 =>
    rw [sub_eq_zero] at hx1
    rw [hx1] at hp
    exact hp rfl
  | inr hx2 =>
    rw [sub_eq_zero] at hx2
    rw [hx2] at hq
    exact hq rfl

  -- <=
  intro h
  rw [x_is_the_only_intersection_c]
  have ⟨h1, h2, h3⟩ := h
      -- x ∈ line_through_c p1 p2
  constructor
  exact h1
      -- x ∈ line_through_c q1 q2
  constructor
  exact h2
  -- ∀ (z : ℂ), z ∈ line_through_c p1 p2 ∧ z ∈ line_through_c q1 q2 → z = x
  intro z
  intro hz
  repeat rw [line_through_c] at hz
  repeat rw [Set.mem_setOf_eq] at hz
  have ⟨hz1, hz2⟩ := hz
  clear hz h
  rw [line_through_c] at h1
  rw [Set.mem_setOf_eq] at h1
  rw [line_through_c] at h2
  rw [Set.mem_setOf_eq] at h2
  contrapose! h3

  obtain ⟨t1, h1'⟩ := h1
  obtain ⟨t2, h2'⟩ := h2
  obtain ⟨t3, hz1'⟩ := hz1
  obtain ⟨t4, hz2'⟩ := hz2

  have h_diff : z - x ≠ 0 := by {
    intro h
    rw [sub_eq_zero] at h
    rw [h] at h3
    exact h3 rfl
  }

  have h_sub1 : z - x = (p2-p1) * (t3-t1) := by {
    rw [h1', hz1']
    simp
    repeat rw [sub_mul]
    repeat rw [mul_sub]
    repeat rw [sub_eq_add_neg]
    rw [mul_comm]
    repeat rw [add_assoc]
    simp
    rw [add_comm]
    rw [add_assoc]
    rw [add_comm]
    rw [mul_comm]
    nth_rewrite 2 [mul_comm]
    rw [add_assoc]
    nth_rewrite 2 [add_comm]
    simp
    rw [mul_comm]
  }

  have h_sub2 : z - x = (q2-q1) * (t4-t2) := by {
    rw [h2', hz2']
    simp
    repeat rw [sub_mul]
    repeat rw [mul_sub]
    repeat rw [sub_eq_add_neg]
    rw [mul_comm]
    repeat rw [add_assoc]
    simp
    rw [add_comm]
    rw [add_assoc]
    rw [add_comm]
    rw [mul_comm]
    nth_rewrite 2 [mul_comm]
    rw [add_assoc]
    nth_rewrite 2 [add_comm]
    simp
    rw [mul_comm]
  }

  have h_eq : (p2 - p1) * (↑t3 - ↑t1) = (q2 - q1) * (↑t4 - ↑t2) := by {
    rw [h_sub1] at h_sub2
    exact h_sub2
  }

  have h_t1 : t3 - t1 ≠ 0 := by {
    rw [h_sub1] at h_diff
    contrapose! h_diff

    have h_tmp : t3 = t1 := by {
      apply eq_of_sub_eq_zero at h_diff
      exact h_diff
    }
    rw [h_tmp]
    simp
  }

  clear h_sub1 h_sub2 h_diff
  -- now we transform h_eq, to get the (p2-p1)/(q2-q1)
  have h : (p2-p1)/(q2-q1) = (t4-t2)/(t3-t1) := by {
    rw [div_eq_div_iff]
    rw [h_eq]
    rw [mul_comm]
    exact h_q
    -- way too complcated
    contrapose! h_t1
    have hh : Complex.ofReal t3 = Complex.ofReal t1 := by {
      apply eq_of_sub_eq_zero at h_t1
      exact h_t1
    }
    simp at hh
    rw [hh]
    simp
  }

  -- we see, that (p2-p1)/(q2-q1) is a real number
  rw [h]
  rw [← Complex.ofReal_sub]
  rw [← Complex.ofReal_sub]
  rw [← Complex.ofReal_div]
  apply Complex.ofReal_im ((t4 - t2) / (t3 - t1))
}

----------------------------------------------------------------
-- Lemma: let M ⊆ ℂ, let x be constructable in i steps
--        let k >= i
--        then: x is constructable in k steps
theorem constructable_in_more_steps_lemma
(M : Set ℂ) (x : ℂ) (i k : ℕ)
(h1 : x ∈ constructable_in_steps_c M i) (h2 : i <= k) :
x ∈ constructable_in_steps_c M k := by {

  induction k
  case zero =>
    have h_i : i = 0 := by {
      rw [Nat.le_zero] at h2
      exact h2
    }
    rw [h_i] at h1
    exact h1

  case succ k' h_k =>

    have h : i <= k' ∨ i = k'+1 := by {
      cases h2
      case refl =>
        right
        simp
      case step h_step =>
        simp at h_step
        left
        exact h_step
    }

    cases h
    case inl h_a =>
      rw [constructable_in_steps_c]
      left
      apply h_k
      exact h_a

    case inr h_b =>
      rw [← h_b]
      exact h1
}

----------------------------------------------------------------
-- Lemma: let 0, 1 ∈ M, then: integers are constructable
theorem int_constructable_lemma (M : Set ℂ) (h_M0 : 0 ∈ M) (h_M1 : 1 ∈ M)
(x : ℂ) (h_x : (∃ n : ℤ, ↑n=x)) : x ∈ Kon_c M := by {
  -- now we show, that every natural number is constructable
  have h_nat : (∀ n : ℕ, ↑n ∈ Kon_c M) := by {
    intro n
    induction n
    case zero =>
      simp
      rw [Kon_c]
      rw [Set.mem_setOf_eq]
      use 0
      rw [constructable_in_steps_c]
      exact h_M0
    case succ k h_k =>
      rw [Kon_c] at h_k
      rw [Set.mem_setOf_eq] at h_k
      obtain ⟨i, h_k⟩ := h_k -- k is constructable in i steps
      simp
      rw [Kon_c]
      rw [Set.mem_setOf_eq]
      use (i+1) -- we claim, that k+1 is constructable in i+1 steps
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      left
      right -- we want to use type-2 construction
      rw [type2_constructable_c]
      rw [Set.mem_setOf_eq]
      rw [point_is_type2_constructable_c]
      -- we use the line between 0 and 1, the circle with center k, and radius 1
      use 0, 1, k, 0, 1

      -- We show, that our points are constructable
      have h_tmp_0 : 0 ∈ constructable_in_steps_c M i := by {
        apply constructable_in_more_steps_lemma M 0 0
        exact h_M0
        simp
      }
      have h_tmp_1 : 1 ∈ constructable_in_steps_c M i := by {
        apply constructable_in_more_steps_lemma M 1 0
        exact h_M1
        simp
      }
      constructor
      exact h_tmp_0
      constructor
      exact h_tmp_1
      constructor
      exact h_k
      constructor
      exact h_tmp_0
      constructor
      exact h_tmp_1
      constructor
      simp
      -- we show: k+1 is on the line
      constructor
      rw [line_through_c]
      simp
      use k+1
      simp
      -- we show: k+1 is on the circle
      rw [circle_c, distance_between_points_c]
      simp
  }

  -- next we show, that every integer is constructable
  obtain ⟨n, h_x⟩ := h_x
  rw [← h_x]

  --intro n
  induction n
  -- first case: positive integer (natural number)
  case ofNat k =>
    simp
    apply h_nat
  case negSucc k' =>
    -- we have to show, that -k-1 is constructable
    -- Idea: circle with radius k+1, and center 0
    rw [Kon_c]
    simp
    -- we need to find a working i
    rw [Kon_c] at h_nat
    simp at h_nat
    obtain ⟨i, hi⟩ := h_nat (k'+1)
    simp at hi
    -- we have extracted the i. Lets use it
    use (i+1)
    rw [constructable_in_steps_c]
    right
    rw [constructable_points_c]
    left
    right -- we do a type2-construction
    rw [type2_constructable_c]
    rw [Set.mem_setOf_eq]
    rw [point_is_type2_constructable_c]

    -- we use the line between 0 and 1, and the circle with center 0 and radius k+1
    use 0, 1, 0, 0, (k'+1)
    have h_tmp_0 : 0 ∈ constructable_in_steps_c M i := by {
      apply constructable_in_more_steps_lemma M 0 0
      exact h_M0
      simp
    }
    have h_tmp_1 : 1 ∈ constructable_in_steps_c M i := by {
      apply constructable_in_more_steps_lemma M 1 0
      exact h_M1
      simp
    }
    constructor
    exact h_tmp_0
    constructor
    exact h_tmp_1
    constructor
    exact h_tmp_0
    constructor
    exact h_tmp_0
    constructor
    exact hi
    constructor
    simp
    constructor
    -- to show: -1 - k' is on the line
    rw [line_through_c]
    simp
    use (-1-k')
    simp
    rfl
    -- to show: -1 - k' is on the circle
    rw [circle_c, distance_between_points_c]
    simp
    rw [Real.sq_sqrt]
    apply pow_two_nonneg
}

----------------------------------------------------------------
-- Lemma: let 0, 1 ∈ M, then n*I is constructable for n ∈ ℤ
theorem int_times_i_constructable_lemma (M : Set ℂ) (h_M0 : 0 ∈ M) (h_M1 : 1 ∈ M)
(z : ℂ) (h_n : (∃ n : ℤ, z = n * Complex.I)) : z ∈ Kon_c M := by {

-- d*I is constructable
--have h_di : d*Complex.I ∈ constructable_in_steps_c M (i_d+3) := by {
  obtain ⟨n, h_n⟩ := h_n

  -- we need the fact, that n is constructable
  have hn : ↑n ∈ Kon_c M := by {
    apply int_constructable_lemma
    exact h_M0
    exact h_M1
    use n
  }
  rw [Kon_c] at hn
  simp at hn
  obtain ⟨i_n, hn⟩ := hn

  -- now we construct n*I
  rw [Kon_c]
  simp
  use i_n+3
  rw [constructable_in_steps_c]
  right
  rw [constructable_points_c]
  left
  right -- type 2 construction
  rw [constructable_in_steps_c]
  rw [type2_constructable_c]
  rw [Set.mem_setOf_eq]
  rw [point_is_type2_constructable_c]
  -- the line: [0 to sqrt(3)*i], circle: [center: 0, radius: n]
  use 0, ((Real.sqrt 3) * Complex.I), 0, 0, n
  -- we show, that we can use this points
  constructor
  left
  rw [constructable_in_steps_c]
  left
  apply constructable_in_more_steps_lemma M 0 0 i_n
  exact h_M0
  apply Nat.zero_le

      -- now the complicated part: sqrt(3)*i
  have h_sqrt3 : (Real.sqrt 3) * Complex.I ∈ constructable_in_steps_c M 2 := by {
    rw [constructable_in_steps_c]
    right
    rw [constructable_in_steps_c]
    rw [constructable_points_c]
    right -- type3-construction
    rw [type3_constructable_c]
    rw [Set.mem_setOf_eq]
    rw [point_is_type3_constructable_c]
    -- we use two circles: [radius=2, center=-1] and [radius=2, center=1]
    use -1, -1, 1, 1, -1, 1
    -- we show, that -1 is constructable in 1 step
    have h_neg1 : -1 ∈ constructable_in_steps_c M 1 := by {
      rw [constructable_in_steps_c]
      right
      rw [constructable_in_steps_c]
      rw [constructable_points_c]
      left
      right -- type2 construction
      rw [type2_constructable_c]
      rw [Set.mem_setOf_eq]
      rw [point_is_type2_constructable_c]
      -- we use the line: [0, 1] and the circle [radius=1, center=0]
      use 0, 1, 0, 0, 1
      constructor
      exact h_M0
      constructor
      exact h_M1
      constructor
      exact h_M0
      constructor
      exact h_M0
      constructor
      exact h_M1
      constructor
      simp
      constructor
      rw [line_through_c]
      simp
      use -1
      simp
      rw [distance_between_points_c]
      simp
      rw [circle_c]
      simp
    }

    constructor
    apply h_neg1
    constructor
    apply h_neg1
    constructor
    left
    exact h_M1
    constructor
    left
    exact h_M1
    constructor
    apply h_neg1
    constructor
    left
    exact h_M1
    constructor
    simp

    have h_tmp : √((-1 - 1) ^ 2) = 2 := by {
      ring_nf
      have h_tmp : (4:ℝ) = 2^2 := by {
        rw [pow_two]
        ring
      }
      rw [h_tmp]
      rw [Real.sqrt_sq]
      simp
    }

    constructor
    rw [distance_between_points_c]
    simp
    -- simplifying
    rw [h_tmp]
    rw [circle_c]
    rw [Set.mem_setOf_eq]
    simp
    ring

    rw [distance_between_points_c]
    simp
    rw [h_tmp]
    rw [circle_c]
    simp
    ring
  }

  constructor
  apply constructable_in_more_steps_lemma M (↑√3 * Complex.I) 2 (i_n+2) at h_sqrt3
  simp at h_sqrt3
  rw [constructable_in_steps_c] at h_sqrt3
  apply h_sqrt3

  constructor
  left
  apply constructable_in_more_steps_lemma M 0 0 (i_n+1)
  exact h_M0
  simp

  constructor
  left
  apply constructable_in_more_steps_lemma M 0 0 (i_n+1)
  exact h_M0
  simp

  constructor
  left
  rw [constructable_in_steps_c]
  left
  exact hn

  constructor
  simp

  -- we show, that the d*I is on the line
  constructor
  rw [line_through_c]
  simp
  use (n/Real.sqrt 3)
  simp
  rw [div_eq_mul_inv]
  rw [mul_assoc]
  nth_rewrite 2 [← mul_assoc]
  simp
  exact h_n

  -- we show, that d*I is on the circle
  rw [distance_between_points_c]
  simp
  rw [circle_c]
  simp
  rw [Real.sq_sqrt]
  rw [h_n]
  simp
  apply pow_two_nonneg
}

----------------------------------------------------------------
-- Lemma: let 0 ∈ M. If z1, z2 ∈ Kon(M), then z1+z2 ∈ Kon(M)
theorem sum_is_constructable_lemma (z1 z2 : ℂ) (M : Set ℂ) (h_M0 : 0 ∈ M)
(h_z1 : z1 ∈ Kon_c M) (h_z2 : z2 ∈ Kon_c M) :
(z1+z2 ∈ Kon_c M) := by {
  by_cases h_case1 : z1 = z2
  case pos =>
    by_cases h_case2 : z1 = 0

    case pos =>
      rw [← h_case1, h_case2]
      simp
      rw [Kon_c]
      simp
      use 0
      apply h_M0

    case neg =>
      rw [← h_case1]
      obtain ⟨i_z1, h_z1⟩ := h_z1
      rw [Kon_c]
      simp
      use i_z1+1
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      left
      right -- type 2 construction
      rw [type2_constructable_c]
      simp
      rw [point_is_type2_constructable_c]
      -- we use the line: [0, z1] and the circle: [center=z1, radius=|z1|]
      use 0, z1, z1, 0, z1
      have h_0_tmp : 0 ∈ constructable_in_steps_c M i_z1 := by {
        apply constructable_in_more_steps_lemma M 0 0
        exact h_M0
        simp
      }
      have h_z1_tmp : z1 ∈ constructable_in_steps_c M i_z1 := by {
        apply constructable_in_more_steps_lemma M z1 i_z1
        exact h_z1
        simp
      }
      constructor
      exact h_0_tmp
      constructor
      exact h_z1_tmp
      constructor
      exact h_z1_tmp
      constructor
      exact h_0_tmp
      constructor
      exact h_z1_tmp
      constructor
      symm
      apply h_case2
      -- z1+z1 is on the line
      constructor
      rw [line_through_c]
      simp
      use 2
      simp
      ring
      -- z1+z1 is on the circle
      rw [distance_between_points_c, circle_c]
      simp
      rw [Real.sq_sqrt]
      have h_tmp1 : 0 <= z1.re^2 := by apply pow_two_nonneg
      have h_tmp2 : 0 <= z1.im^2 := by apply pow_two_nonneg
      linarith

  case neg =>
    obtain ⟨i_z1, h_z1⟩ := h_z1
    obtain ⟨i_z2, h_z2⟩ := h_z2
    rw [Kon_c]
    simp
    use i_z1+i_z2+1
    rw [constructable_in_steps_c]
    right
    rw [constructable_points_c]
    right -- type 3 construction
    rw [type3_constructable_c]
    simp
    rw [point_is_type3_constructable_c]
    -- we use: circle1: [center=z1, radius=|z2|] and circle2: [center=z2, radius=|z1|]
    use z1, 0, z2, z2, 0, z1
    constructor
    apply constructable_in_more_steps_lemma M z1 i_z1
    exact h_z1
    simp

    constructor
    apply constructable_in_more_steps_lemma M 0 0
    apply h_M0
    simp

    constructor
    apply constructable_in_more_steps_lemma M z2 i_z2
    exact h_z2
    simp

    constructor
    apply constructable_in_more_steps_lemma M z2 i_z2
    exact h_z2
    simp

    constructor
    apply constructable_in_more_steps_lemma M 0 0
    apply h_M0
    simp

    constructor
    apply constructable_in_more_steps_lemma M z1 i_z1
    exact h_z1
    simp

    constructor
    apply h_case1

    -- point is on first circle
    constructor
    rw [circle_c, distance_between_points_c]
    simp
    rw [Real.sq_sqrt]
    have h_tmp1 : 0 <= z2.re^2 := by apply pow_two_nonneg
    have h_tmp2 : 0 <= z2.im^2 := by apply pow_two_nonneg
    linarith

    -- point is on second circle
    rw [circle_c, distance_between_points_c]
    simp
    rw [Real.sq_sqrt]
    have h_tmp1 : 0 <= z1.re^2 := by apply pow_two_nonneg
    have h_tmp2 : 0 <= z1.im^2 := by apply pow_two_nonneg
    linarith
}

----------------------------------------------------------------
-- Lemma: let 0,1,z ∈ M. Then: -z ∈ Kon(M)
theorem add_inv_is_constructable_lemma (M : Set ℂ) (h_M0 : 0 ∈ M)
(z : ℂ) (h_z : z ∈ Kon_c M) : -z ∈ Kon_c M := by {
  by_cases h_case : z = 0
  case pos =>
    rw [h_case]
    simp
    rw [Kon_c]
    simp
    use 0
    apply h_M0

  case neg =>
    rw [Kon_c] at h_z
    simp at h_z
    obtain ⟨i_z, h_z⟩ := h_z
    rw [Kon_c]
    simp
    use i_z+1
    rw [constructable_in_steps_c]
    right
    rw [constructable_points_c]
    left
    right -- type 2 construction
    rw [type2_constructable_c]
    simp
    rw [point_is_type2_constructable_c]
    -- we use: line: [z, 0] and circle: [center=0, radius=|z|]
    use z, 0, 0, 0, z
    have h_0 : 0 ∈ constructable_in_steps_c M i_z := by {
      apply constructable_in_more_steps_lemma M 0 0
      exact h_M0
      simp
    }
    constructor
    exact h_z
    constructor
    exact h_0
    constructor
    exact h_0
    constructor
    exact h_0
    constructor
    exact h_z
    constructor
    exact h_case
    -- -z is on the line
    constructor
    rw [line_through_c]
    simp
    use 2
    rw [mul_comm]
    simp
    rw [mul_two]
    simp
    -- -z is on the circle
    rw [distance_between_points_c, circle_c]
    simp
    rw [Real.sq_sqrt]
    have h_re : 0 <= z.re^2 := by apply pow_two_nonneg
    have h_im : 0 <= z.im^2 := by apply pow_two_nonneg
    linarith
}

----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M, with z ∈ Kon(M). Then: z.re ∈ Kon(M)
theorem re_is_constructable_lemma (z : ℂ) (M : Set ℂ) (h_M0 : 0 ∈ M)
(h_M1 : 1 ∈ M) (h_z : z ∈ Kon_c M) : ↑z.re ∈ Kon_c M := by {
  -- PLAN: we move the line [0, i] parallel to z.
  -- the line intersects with z.re
  by_cases h_case : z.re = 0
  case pos =>
    rw [h_case]
    rw [Kon_c]
    simp
    use 0
    apply h_M0

  case neg =>
    have h : ¬√(z.re ^ 2 + z.im ^ 2) = 0 := by {
      contrapose! h_case
      rw [Real.sqrt_eq_zero] at h_case
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      have h_re2 : z.re^2 = 0 := by linarith
      rw [pow_two] at h_re2
      apply eq_zero_or_eq_zero_of_mul_eq_zero at h_re2
      cases h_re2 with
      | inl h =>
        exact h
      | inr h =>
        exact h

      have h_re : 0 <= z.re^2 := by apply pow_two_nonneg
      have h_im : 0 <= z.im^2 := by apply pow_two_nonneg
      linarith
    }

    rw [Kon_c] at h_z
    obtain ⟨i_z, h_z⟩ := h_z

    have h_i : Complex.I ∈ Kon_c M := by {
      apply int_times_i_constructable_lemma
      exact h_M0
      exact h_M1
      use 1
      simp
    }
    obtain ⟨i_i, h_i⟩ := h_i

    have h_p1 : (Complex.I * Real.sqrt (z.re^2+z.im^2)) ∈ Kon_c M := by {
      rw [Kon_c]
      simp
      use i_i+i_z+1
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      left
      right
      rw [type2_constructable_c]
      simp
      rw [point_is_type2_constructable_c]
      -- we use the line: [0, i] and the circle: [center=0, radius=|z|]
      use 0, Complex.I, 0, 0, z
      have h_0 : 0 ∈ constructable_in_steps_c M (i_i+i_z) := by {
        apply constructable_in_more_steps_lemma M 0 0
        exact h_M0
        simp
      }
      constructor
      exact h_0
      constructor
      apply constructable_in_more_steps_lemma M Complex.I i_i
      exact h_i
      simp
      constructor
      exact h_0
      constructor
      exact h_0
      constructor
      apply constructable_in_more_steps_lemma M z i_z
      exact h_z
      simp
      constructor
      simp [Complex.ext_iff]

      constructor
      rw [line_through_c]
      simp
      use Real.sqrt (z.re ^ 2 + z.im ^ 2)
      ring

      rw [distance_between_points_c, circle_c]
      simp
    }
    obtain ⟨i_p1, h_p1⟩ := h_p1

    have h_p2 : z + Complex.I * Real.sqrt (z.re^2+z.im^2) ∈ Kon_c M := by {
      rw [Kon_c]
      simp
      use i_p1+i_z+1
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      right
      rw [type3_constructable_c]
      simp
      rw [point_is_type3_constructable_c]
      -- we use circle1: [center=p1, radius=|z|] and circle2: [center=z, radius=|z|]
      use Complex.I * Real.sqrt (z.re^2+z.im^2)
      use 0, z, z, 0, z
      have h_0 : 0 ∈ constructable_in_steps_c M (i_p1+i_z) := by {
        apply constructable_in_more_steps_lemma M 0 0
        exact h_M0
        simp
      }
      have hz : z ∈ constructable_in_steps_c M (i_p1+i_z) := by {
        apply constructable_in_more_steps_lemma M z i_z
        exact h_z
        simp
      }
      constructor
      apply constructable_in_more_steps_lemma M
            (Complex.I * Real.sqrt (z.re ^ 2 + z.im ^ 2)) i_p1
      exact h_p1
      simp
      constructor
      exact h_0
      constructor
      exact hz
      constructor
      exact hz
      constructor
      exact h_0
      constructor
      exact hz
      constructor
      simp [Complex.ext_iff]
      intro h_re
      intro h_ii
      rw [h_re] at h_case
      exact h_case rfl
      -- circle1
      constructor
      rw [distance_between_points_c, circle_c]
      simp
      rw [Real.sq_sqrt]
      have h_re : 0 <= z.re^2 := by apply pow_two_nonneg
      have h_im : 0 <= z.im^2 := by apply pow_two_nonneg
      linarith
      -- circle2
      rw [distance_between_points_c, circle_c]
      simp
    }
    obtain ⟨i_p2, h_p2⟩ := h_p2

    -- now we can construct z.re
    rw [Kon_c]
    simp
    use i_p2+i_z+1
    rw [constructable_in_steps_c]
    right
    rw [constructable_points_c]
    left
    left
    rw [type1_constructable_c]
    simp
    rw [point_is_type1_constructable_c]
    -- we use: line1: [0, 1] and line2: [z, p2]
    use 0, 1, z, (z + Complex.I * ↑√(z.re ^ 2 + z.im ^ 2))
    constructor
    apply constructable_in_more_steps_lemma M 0 0
    exact h_M0
    simp
    constructor
    apply constructable_in_more_steps_lemma M 1 0
    exact h_M1
    simp
    constructor
    apply constructable_in_more_steps_lemma M z i_z
    exact h_z
    simp
    constructor
    apply constructable_in_more_steps_lemma M
          (z + Complex.I * ↑√(z.re ^ 2 + z.im ^ 2)) i_p2
    exact h_p2
    simp
    constructor
    simp
    constructor
    simp [Complex.ext_iff]
    exact h

    rw [only_intersection_lemma]
    constructor
    rw [line_through_c]
    simp
    constructor
    rw [line_through_c]
    simp
    use -z.im*(Real.sqrt (z.re^2+z.im^2))⁻¹
    rw [← mul_assoc, mul_comm]
    nth_rewrite 3 [mul_comm]
    simp
    repeat rw [← mul_assoc]
    rw [mul_inv_cancel]
    rw [Complex.ext_iff]
    simp
    exact_mod_cast h

    simp
    exact h
    simp
    simp
    exact h
}

-----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M, with z ∈ Kon(M). Then: z/2 ∈ Kon(M)
theorem halve_distance_is_constructable_lemma (z : ℂ) (M : Set ℂ)
(h_M0 : 0 ∈ M) (h_M1 : 1 ∈ M) (h_z : z ∈ Kon_c M) : z/2 ∈ Kon_c M := by {
  -- first we project the distance to the real-axis
  by_cases h_case : z = 0--Real.sqrt (z.re^2+z.im^2) = 0
  case pos =>
    rw [h_case]
    simp
    rw [Kon_c]
    use 0
    exact h_M0

  case neg =>
    have h_case_lemma : ¬√(z.re ^ 2 + z.im ^ 2) = 0 := by {
      contrapose! h_case
      rw [Real.sqrt_eq_zero] at h_case
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      have h1 : z.re^2 = 0 := by linarith
      have h2 : z.im^2 = 0 := by linarith
      have h3 : z.re = 0 := by {
        rw [pow_two] at h1
        apply eq_zero_of_mul_self_eq_zero at h1
        exact h1
      }
      have h4 : z.im = 0 := by {
        rw [pow_two] at h2
        apply eq_zero_of_mul_self_eq_zero at h2
        exact h2
      }
      simp [Complex.ext_iff]
      rw [h3, h4]
      simp
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
    }

    have h_d : ↑(Real.sqrt (z.re^2+z.im^2)) ∈ Kon_c M := by {
      rw [Kon_c] at h_z
      obtain ⟨i_z, h_z⟩ := h_z
      rw [Kon_c]
      simp
      use i_z+1
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      left
      right
      rw [type2_constructable_c]
      simp
      rw [point_is_type2_constructable_c]
      -- we use: line: [0, 1], circle: [center=0, radius=|z|]
      use 0, 1, 0, 0, z
      have h_0 : 0 ∈ constructable_in_steps_c M i_z := by {
        apply constructable_in_more_steps_lemma M 0 0
        exact h_M0
        simp
      }
      constructor
      exact h_0
      constructor
      apply constructable_in_more_steps_lemma M 1 0
      exact h_M1
      simp
      constructor
      exact h_0
      constructor
      exact h_0
      constructor
      exact h_z
      constructor
      simp
      constructor
      rw [line_through_c]
      simp
      rw [circle_c, distance_between_points_c]
      simp
    }
    obtain ⟨i_d, h_d⟩ := h_d

    -- we want to halve this distance. To do that, we need 2 new points: p1 and p2
    let a := Real.sqrt (z.re^2+z.im^2)
    have h_p1 : a/2 + Complex.I*(Real.sqrt (3*a^2))/2 ∈ Kon_c M := by {
      rw [Kon_c]
      simp
      use i_d+1
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      right
      rw [type3_constructable_c]
      simp
      rw [point_is_type3_constructable_c]
      -- we use: circle1: [radius=a, center=0], circle2: [radius=a, center=a]
      use 0, 0, a, a, 0, a
      have h_0 : 0 ∈ constructable_in_steps_c M i_d := by {
        apply constructable_in_more_steps_lemma M 0 0
        exact h_M0
        simp
      }
      constructor
      exact h_0
      constructor
      exact h_0
      constructor
      exact h_d
      constructor
      exact h_d
      constructor
      exact h_0
      constructor
      exact h_d
      constructor
      have h_case_lemma_a : a ≠ 0 := by apply h_case_lemma
      symm
      exact_mod_cast h_case_lemma_a

      -- first circle
      constructor
      rw [circle_c, distance_between_points_c]
      simp
      repeat rw [Real.sq_sqrt]
      rw [mul_pow]
      repeat rw [Real.sq_sqrt]
      ring
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
      simp
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith

      -- second circle
      rw [distance_between_points_c, circle_c]
      simp
      rw [mul_pow]
      repeat rw [Real.sq_sqrt]
      ring_nf
      rw [Real.sq_sqrt]
      ring
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
      apply pow_two_nonneg
      simp
    }
    obtain ⟨i_p1, h_p1⟩ := h_p1

    have h_p2 : a/2 - Complex.I*(Real.sqrt (3*a^2))/2 ∈ Kon_c M := by {
      rw [Kon_c]
      simp
      use i_d+1
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      right
      rw [type3_constructable_c]
      simp
      rw [point_is_type3_constructable_c]
      -- we use: circle1: [radius=a, center=0], circle2: [radius=a, center=a]
      use 0, 0, a, a, 0, a
      have h_0 : 0 ∈ constructable_in_steps_c M i_d := by {
        apply constructable_in_more_steps_lemma M 0 0
        exact h_M0
        simp
      }
      constructor
      exact h_0
      constructor
      exact h_0
      constructor
      exact h_d
      constructor
      exact h_d
      constructor
      exact h_0
      constructor
      exact h_d
      constructor
      symm
      exact_mod_cast h_case_lemma

      -- first circle
      constructor
      rw [circle_c, distance_between_points_c]
      simp
      repeat rw [Real.sq_sqrt]
      rw [mul_pow]
      repeat rw [Real.sq_sqrt]
      ring
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
      simp
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith

      -- second circle
      rw [distance_between_points_c, circle_c]
      simp
      rw [mul_pow]
      repeat rw [Real.sq_sqrt]
      ring_nf
      rw [Real.sq_sqrt]
      ring
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
      apply pow_two_nonneg
      simp
    }
    obtain ⟨i_p2, h_p2⟩ := h_p2

    have h_half_a : ↑(a/2) ∈ Kon_c M := by {
      rw [Kon_c]
      simp
      use i_p1+i_p2+1
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      left
      left
      rw [type1_constructable_c]
      simp
      rw [point_is_type1_constructable_c]
      -- we use: line1: [0, 1] and line2: [p1, p2]
      use 0, 1
      use a/2 + Complex.I * Real.sqrt (3 * a ^ 2) / 2
      use a/2 - Complex.I * Real.sqrt (3 * a ^ 2) / 2
      constructor
      apply constructable_in_more_steps_lemma M 0 0
      exact h_M0
      simp
      constructor
      apply constructable_in_more_steps_lemma M 1 0
      exact h_M1
      simp
      constructor
      apply constructable_in_more_steps_lemma M
            (a/2 + Complex.I * Real.sqrt (3 * a ^ 2) / 2) i_p1
      exact h_p1
      simp
      constructor
      apply constructable_in_more_steps_lemma M
            (a/2 - Complex.I * Real.sqrt (3 * a ^ 2) / 2) i_p2
      exact h_p2
      simp
      constructor
      simp
      constructor
      rw [sub_eq_add_neg]
      simp
      rw [Real.sqrt_eq_zero]
      rw [pow_two]
      contrapose! h_case
      apply eq_zero_of_mul_self_eq_zero at h_case
      contrapose! h_case
      apply h_case_lemma
      apply pow_two_nonneg

      -- only intersection
      rw [only_intersection_lemma]
      constructor
      rw [line_through_c]
      simp
      use a/2
      simp
      constructor
      rw [line_through_c]
      simp
      use 1/2
      repeat rw [add_assoc]
      simp
      ring

      -- im ≠ 0
      simp
      constructor
      rw [Real.sq_sqrt]
      apply h_case_lemma
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith

      ring_nf
      rw [Real.sq_sqrt]
      simp
      apply h_case_lemma
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith

      simp
      rw [sub_eq_add_neg]
      simp
      rw [Real.sq_sqrt]
      apply h_case_lemma
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
    }
    obtain ⟨i_half_a, h_half_a⟩ := h_half_a
    obtain ⟨i_z, h_z⟩ := h_z

    -- now we can project a/2 up to the line [0, z]
    rw [Kon_c]
    simp
    use i_half_a+i_z+1
    rw [constructable_in_steps_c]
    right
    rw [constructable_points_c]
    left
    right
    rw [type2_constructable_c]
    simp
    rw [point_is_type2_constructable_c]
    -- we use: line: [0, z] and circle: [center=0, radius=a/2]
    use 0, z, 0, 0, a/2
    have h_0 : 0 ∈ constructable_in_steps_c M (i_half_a+i_z) := by {
      apply constructable_in_more_steps_lemma M 0 0
      exact h_M0
      simp
    }
    constructor
    exact h_0
    constructor
    apply constructable_in_more_steps_lemma M z i_z
    exact h_z
    simp
    constructor
    exact h_0
    constructor
    exact h_0
    constructor
    apply constructable_in_more_steps_lemma M (a/2) i_half_a
    exact_mod_cast h_half_a
    simp
    constructor
    contrapose! h_case
    symm
    apply h_case

    constructor
    rw [line_through_c]
    simp
    use 1/2
    simp
    ring

    rw [distance_between_points_c, circle_c]
    simp
    rw [Real.sq_sqrt]
    rw [Real.sq_sqrt]
    ring
    have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
    have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
    linarith
    apply pow_two_nonneg
}

-----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M, with z ∈ Kon(M). Then: conj(z) ∈ Kon(M)
theorem conjugation_is_constructable_lemma (M : Set ℂ) (h_M0 : 0 ∈ M)
(h_M1 : 1 ∈ M) (z : ℂ) (h_z : z ∈ Kon_c M) : conj z ∈ Kon_c M := by {
  by_cases h_case1 : z=0
  case pos =>
    rw [h_case1]
    rw [conj]
    simp
    rw [Kon_c]
    simp
    use 0
    apply h_M0

  case neg =>
    rw [Kon_c] at h_z
    simp at h_z
    obtain ⟨i_z, h_z⟩ := h_z

    -- PLAN: we move the line [0, i] parallel to z
    -- then we draw a circle: [radius = |z|, center = 0]
    -- conj z is a intersection

    -- we need the point i
    have h_i : (Complex.I ∈ Kon_c M) := by {
      apply int_times_i_constructable_lemma
      exact h_M0
      exact h_M1
      use 1
      simp
    }
    obtain ⟨i_i, h_i⟩ := h_i

    -- for the parallel line, we first need the point -|z|*i
    have h_p1 : (-Complex.I * Real.sqrt (z.re*z.re+z.im*z.im) ∈ Kon_c M) := by {

      rw [Kon_c]
      simp
      use i_z+i_i+1
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      left
      right -- type2 construction
      rw [type2_constructable_c]
      simp
      rw [point_is_type2_constructable_c]
      -- we use the line: [0, i] and the circle: [center=0, radius=|z|]
      use 0, Complex.I, 0, 0, z
      constructor
      apply constructable_in_more_steps_lemma M 0 0
      exact h_M0
      simp

      constructor
      apply constructable_in_more_steps_lemma M Complex.I i_i
      exact h_i
      simp

      constructor
      apply constructable_in_more_steps_lemma M 0 0
      exact h_M0
      simp

      constructor
      apply constructable_in_more_steps_lemma M 0 0
      exact h_M0
      simp

      constructor
      apply constructable_in_more_steps_lemma M z i_z
      exact h_z
      simp

      constructor
      simp [Complex.ext_iff]

      -- the point is on the line
      constructor
      rw [line_through_c]
      simp
      use -Real.sqrt (z.re * z.re + z.im * z.im)
      simp
      rw [mul_comm]

      -- the point is on the circle
      rw [distance_between_points_c]
      rw [circle_c]
      simp
      repeat rw [Real.sq_sqrt]
      ring
      have h_tmp1 : 0 <= z.re^2 := by apply pow_two_nonneg
      have h_tmp2 : 0 <= z.im^2 := by apply pow_two_nonneg
      linarith

      have h_tmp1 : 0 <= z.re*z.re := by apply mul_self_nonneg
      have h_tmp2 : 0 <= z.im*z.im := by apply mul_self_nonneg
      linarith
    }

    have h_p2 : (z - Complex.I * Real.sqrt (z.re*z.re + z.im*z.im) ∈ Kon_c M) := by {
      rw [sub_eq_add_neg]
      apply sum_is_constructable_lemma
      exact h_M0
      rw [Kon_c]
      simp
      use i_z
      rw [mul_comm]
      rw [neg_mul_eq_mul_neg]
      rw [mul_comm]
      apply h_p1
    }
    obtain ⟨i_p2, h_p2⟩ := h_p2

    -- now we can construct conj z
    rw [Kon_c]
    simp
    use i_p2+i_z+1
    rw [constructable_in_steps_c]
    right
    rw [constructable_points_c]
    left
    right -- type 2 construction
    rw [type2_constructable_c]
    simp
    rw [point_is_type2_constructable_c]
    -- we use: line: [z, p2], circle: [center=0, radius=|z|]
    use (z - Complex.I * Real.sqrt (z.re*z.re + z.im*z.im))
    use z, 0, 0, z
    constructor
    apply constructable_in_more_steps_lemma M
          (z - Complex.I * Real.sqrt (z.re*z.re + z.im*z.im)) i_p2
    exact h_p2
    simp

    constructor
    apply constructable_in_more_steps_lemma M z i_z
    exact h_z
    simp

    constructor
    apply constructable_in_more_steps_lemma M 0 0
    apply h_M0
    simp

    constructor
    apply constructable_in_more_steps_lemma M 0 0
    apply h_M0
    simp

    constructor
    apply constructable_in_more_steps_lemma M z i_z
    exact h_z
    simp

    -- the points are not the same
    constructor
    contrapose! h_case1
    simp at h_case1
    rw [Real.sqrt_eq_zero] at h_case1
    simp [Complex.ext_iff]

    have h_re_zero : z.re * z.re = 0 := by {
      have non_neg_re := mul_self_nonneg z.re
      have non_neg_im := mul_self_nonneg z.im
      linarith [h_case1, non_neg_re, non_neg_im]
    }
    have h_im_zero : z.im * z.im = 0 := by {
      have := le_add_of_nonneg_of_le (mul_self_nonneg z.im) (mul_self_nonneg z.re)
      linarith
    }
    exact ⟨eq_zero_of_mul_self_eq_zero h_re_zero, eq_zero_of_mul_self_eq_zero h_im_zero⟩

    -- we used, that z.re^2+z.im^2 <= 0
    have non_neg_re : 0 ≤ z.re * z.re := by
      exact mul_self_nonneg z.re

    have non_neg_im : 0 ≤ z.im * z.im := by
      exact mul_self_nonneg z.im

    linarith [non_neg_re, non_neg_im]

    -- the point is on the line
    constructor
    rw [line_through_c]
    simp
    rw [conj]
    use (-2*z.im*Real.sqrt (z.re*z.re+z.im*z.im))/(z.re*z.re+z.im*z.im) + 1
    simp
    ring_nf
    have h_tmp : (↑√(z.re ^ 2 + z.im ^ 2) : ℂ) ^ 2 = ↑(√(z.re ^ 2 + z.im ^ 2) ^ 2) := by {
      simp
    }
    rw [h_tmp]
    rw [Real.sq_sqrt]
    nth_rewrite 2 [mul_comm]
    repeat rw [mul_assoc]
    have h_tmp2 : ((↑(z.re ^ 2 + z.im ^ 2) : ℂ) * ((↑z.re:ℂ)^2 + (↑z.im:ℂ)^2)⁻¹) = 1 := by {
      simp
      rw [mul_inv_cancel]
      contrapose! h_case1
      norm_cast at h_case1
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      have h_re1 : ↑z.re^2 = 0 := by linarith
      have h_im1 : z.im^2 = 0 := by linarith
      have h_re2 : z.re = 0 := by {
        rw [pow_two] at h_re1
        apply eq_zero_or_eq_zero_of_mul_eq_zero at h_re1
        cases h_re1 with
        | inl h =>
          exact h
        | inr h =>
          exact h
      }
      have h_im2 : z.im = 0 := by {
        rw [pow_two] at h_im1
        apply eq_zero_or_eq_zero_of_mul_eq_zero at h_im1
        cases h_im1 with
        | inl h =>
          exact h
        | inr h =>
          exact h
      }
      simp [Complex.ext_iff]
      constructor
      exact h_re2
      exact h_im2
    }
    rw [h_tmp2]
    simp
    rw [Complex.ext_iff]
    simp
    rw [two_mul]
    simp
    have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
    have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
    linarith

    -- the point is on the circle
    rw [distance_between_points_c, circle_c]
    simp
    rw [Real.sq_sqrt]
    repeat rw [conj]
    simp
    have h1 : 0 <= z.re^2 := by apply pow_two_nonneg
    have h2 : 0 <= z.im^2 := by apply pow_two_nonneg
    linarith
}

----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M, with z ∈ Kon(M). Then: z.im ∈ Kon(M)
theorem im_is_constructable_lemma (z : ℂ) (M : Set ℂ) (h_M0 : 0 ∈ M)
(h_M1 : 1 ∈ M) (h_z : z ∈ Kon_c M) : ↑z.im ∈ Kon_c M := by {
  --obtain ⟨i_z, h_z⟩ := h_z
  have h_conj : conj z ∈ Kon_c M := by {
    apply conjugation_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z
  }

  have h_conj_inv : -conj z ∈ Kon_c M := by {
    apply add_inv_is_constructable_lemma
    exact h_M0
    exact h_conj
  }

  have h_2im : ↑(2*z.im*Complex.I) ∈ Kon_c M := by {
    have h_tmp : -conj z + z ∈ Kon_c M := by {
      apply sum_is_constructable_lemma (-conj z) z
      exact h_M0
      exact h_conj_inv
      exact h_z
    }
    have h_tmp2 : (2 * z.im * Complex.I) = -conj z + z := by {
      rw [conj]
      rw [Complex.ext_iff]
      simp
      ring
    }
    rw [h_tmp2]
    apply h_tmp
  }

  -- we have to halve the length
  have h_im : ↑(z.im*Complex.I) ∈ Kon_c M := by {
    have h_tmp : 2 * ↑z.im * Complex.I / 2 ∈ Kon_c M := by {
      apply halve_distance_is_constructable_lemma (2 * z.im * Complex.I)
      exact h_M0
      exact h_M1
      exact h_2im
    }

    rw [div_eq_mul_inv] at h_tmp
    rw [mul_comm] at h_tmp
    repeat rw [← mul_assoc] at h_tmp
    nth_rewrite 3 [mul_comm] at h_tmp
    rw [mul_inv_cancel] at h_tmp
    simp at h_tmp
    exact h_tmp
    simp
  }
  obtain ⟨i_im, h_im⟩ := h_im

  -- we move the point z.im*i to z.im
  rw [Kon_c]
  use i_im+1
  rw [constructable_in_steps_c]
  right
  rw [constructable_points_c]
  left
  right
  rw [type2_constructable_c]
  simp
  rw [point_is_type2_constructable_c]
  -- we use the line: [0, 1] and the circle: [center=0, radius=z.im]
  use 0, 1, 0, 0, z.im*Complex.I
  have h_0 : 0 ∈ constructable_in_steps_c M i_im := by {
    apply constructable_in_more_steps_lemma M 0 0
    exact h_M0
    simp
  }
  constructor
  apply h_0
  constructor
  apply constructable_in_more_steps_lemma M 1 0
  exact h_M1
  simp
  constructor
  exact h_0
  constructor
  exact h_0
  constructor
  exact h_im
  constructor
  simp
  constructor
  rw [line_through_c]
  use z.im
  simp
  rw [circle_c, distance_between_points_c]
  simp
  rw [Real.sq_sqrt]
  apply pow_two_nonneg
}

----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M, with z ∈ Kon(M). Then: z*i ∈ Kon(M)
theorem times_i_is_constructable_lemma (M : Set ℂ) (h_M0 : 0 ∈ M) (h_M1 : 1 ∈ M)
(z : ℂ) (h_z : z ∈ Kon_c M) : z*Complex.I ∈ Kon_c M := by {
  -- idea: use z.re and z.im*I
  -- make a circle from -z.im with radius z.re
  -- and another circle from z.re*I with radius z.im

  have h_re : ↑z.re ∈ Kon_c M := by {
    apply re_is_constructable_lemma z
    exact h_M0
    exact h_M1
    exact h_z
  }
  obtain ⟨i_re, h_re⟩ := h_re

  have h_im : ↑z.im ∈ Kon_c M := by {
    apply im_is_constructable_lemma z
    exact h_M0
    exact h_M1
    exact h_z
  }
  obtain ⟨i_im, h_im⟩ := h_im

  -- but we need z.re * i and z.im
  have h_i : Complex.I ∈ Kon_c M := by {
    apply int_times_i_constructable_lemma
    exact h_M0
    exact h_M1
    use 1
    simp
  }
  obtain ⟨i_i, h_i⟩ := h_i

  have h_re_i : z.re * Complex.I ∈ Kon_c M := by {
    rw [Kon_c]
    use i_i+i_re+1
    rw [constructable_in_steps_c]
    right
    rw [constructable_points_c]
    left
    right
    rw [type2_constructable_c]
    simp
    rw [point_is_type2_constructable_c]
    -- we use: line: [0, i] and circle: [center=0, radius=z.re]
    use 0, Complex.I, 0, 0, z.re
    have h_0 : 0 ∈ constructable_in_steps_c M (i_i+i_re) := by {
      apply constructable_in_more_steps_lemma M 0 0
      apply h_M0
      simp
    }
    constructor
    exact h_0
    constructor
    apply constructable_in_more_steps_lemma M Complex.I i_i
    exact h_i
    simp
    constructor
    exact h_0
    constructor
    exact h_0
    constructor
    apply constructable_in_more_steps_lemma M z.re i_re
    exact h_re
    simp
    constructor
    simp [Complex.ext_iff]
    constructor
    rw [line_through_c]
    simp
    rw [circle_c, distance_between_points_c]
    simp
    rw [Real.sq_sqrt]
    apply pow_two_nonneg
  }
  obtain ⟨i_re_i, h_re_i⟩ := h_re_i

  have h_im_neg : -↑z.im ∈ Kon_c M := by {
    apply add_inv_is_constructable_lemma
    exact h_M0
    rw [Kon_c]
    use i_im
  }
  obtain ⟨i_im_neg, h_im_neg⟩ := h_im_neg

  -- the goal is to draw two lines, parallel to the axis. The intersection is z*i
  have h_p1 : z.re*Complex.I + 1 ∈ Kon_c M := by {
    apply sum_is_constructable_lemma (z.re*Complex.I) 1
    exact h_M0
    rw [Kon_c]
    use i_re_i
    rw [Kon_c]
    use 0
    apply h_M1
  }
  obtain ⟨i_p1, h_p1⟩ := h_p1

  have h_p2 : ↑(-z.im + Complex.I) ∈ Kon_c M := by {
    apply sum_is_constructable_lemma (-z.im) Complex.I
    exact h_M0
    rw [Kon_c]
    use i_im_neg
    rw [Kon_c]
    use i_i
  }
  obtain ⟨i_p2, h_p2⟩ := h_p2

  -- now we can draw the lines
  have h_z_i : z*Complex.I ∈ Kon_c M := by {
    rw [Kon_c]
    use i_p1+i_p2+i_re_i+i_im_neg+1
    rw [constructable_in_steps_c]
    right
    rw [constructable_points_c]
    simp
    left
    left
    rw [type1_constructable_c]
    simp
    rw [point_is_type1_constructable_c]
    -- we use: line1: [z.re*i, p1] and line2: [z.im, p2]
    use z.re*Complex.I, z.re*Complex.I + 1
    use (-z.im), ↑(-z.im+Complex.I)
    constructor
    apply constructable_in_more_steps_lemma M (z.re*Complex.I) i_re_i
    exact h_re_i
    nth_rewrite 2 [add_comm]
    rw [add_assoc]
    simp
    constructor
    apply constructable_in_more_steps_lemma M (z.re*Complex.I+1) i_p1
    exact h_p1
    repeat rw [add_assoc]
    simp
    constructor
    apply constructable_in_more_steps_lemma M (-z.im) i_im_neg
    exact h_im_neg
    simp
    constructor
    apply constructable_in_more_steps_lemma M ↑(-z.im+Complex.I) i_p2
    apply h_p2
    nth_rewrite 3 [add_comm]
    repeat rw [add_assoc]
    simp
    constructor
    simp
    constructor
    simp
    rw [only_intersection_lemma]
    -- line 1
    constructor
    rw [line_through_c]
    simp
    use -z.im
    simp [Complex.ext_iff]
    -- line 2
    constructor
    rw [line_through_c]
    simp
    use z.re
    simp [Complex.ext_iff]

    simp
    simp
    simp
  }
  exact h_z_i
}

----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M, with a,b ∈ ℝ constructable. Then: a*b ∈ Kon(M)
theorem mul_real_is_constructable_lemma (M : Set ℂ) (h_M0 : 0 ∈ M) (h_M1 : 1 ∈ M)
(a b : ℝ) (h_a : ↑a ∈ Kon_c M) (h_b : ↑b ∈ Kon_c M) : ↑(a*b) ∈ Kon_c M := by {
  -- idea: we have the point a and the point b*I
  -- we draw the line between 1*I and a
  -- we move the line paralell to b*I
  -- this line intersects with a*b

  by_cases h_case : a = 0 ∨ b = 0
  case pos =>
    cases h_case with
    | inl h_case1 =>
      rw [h_case1]
      simp
      rw [Kon_c]
      use 0
      apply h_M0
    | inr h_case2 =>
      rw [h_case2]
      simp
      rw [Kon_c]
      use 0
      apply h_M0

  case neg =>
    simp at h_case
    obtain ⟨h_case1, _⟩ := h_case

    -- we need the point b*I, (a-i)+b*i
    have h_bi : b*Complex.I ∈ Kon_c M := by {
      apply times_i_is_constructable_lemma
      exact h_M0
      exact h_M1
      exact h_b
    }

    have h_p1 : (a-Complex.I)+b*Complex.I ∈ Kon_c M := by {
      apply sum_is_constructable_lemma
      exact h_M0
      rw [sub_eq_add_neg]
      apply sum_is_constructable_lemma
      exact h_M0
      exact h_a
      apply int_times_i_constructable_lemma
      exact h_M0
      exact h_M1
      use -1
      simp
      exact h_bi
    }
    obtain ⟨i_p1, h_p1⟩ := h_p1
    obtain ⟨i_bi, h_bi⟩ := h_bi

    have h_ab : ↑(a*b) ∈ Kon_c M := by {
      rw [Kon_c]
      use i_p1+i_bi+1
      rw [constructable_in_steps_c]
      right
      rw [constructable_points_c]
      left
      left
      rw [type1_constructable_c]
      simp
      rw [point_is_type1_constructable_c]
      -- we use line1: [b*i, p1] and line2: [0, 1]
      use b*Complex.I, (a-Complex.I)+b*Complex.I, 0, 1
      constructor
      apply constructable_in_more_steps_lemma M (b*Complex.I) i_bi
      exact h_bi
      simp
      constructor
      apply constructable_in_more_steps_lemma M ((a-Complex.I)+b*Complex.I) i_p1
      exact h_p1
      simp
      constructor
      apply constructable_in_more_steps_lemma M 0 0
      exact h_M0
      simp
      constructor
      apply constructable_in_more_steps_lemma M 1 0
      exact h_M1
      simp
      constructor
      simp
      contrapose! h_case1
      rw [sub_eq_zero] at h_case1
      rw [Complex.ext_iff] at h_case1
      simp at h_case1
      constructor
      simp
      rw [only_intersection_lemma]
      constructor
      rw [line_through_c]
      simp
      use b
      ring
      constructor
      rw [line_through_c]
      simp
      use a*b
      simp
      simp
      simp
      simp [Complex.ext_iff]
      simp
    }
    exact h_ab
}

----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M, with z1,z2 ∈ ℂ constructable. Then: z1*z2 ∈ Kon(M)
theorem mul_is_constructable_lemma (M : Set ℂ) (h_M0 : 0 ∈ M) (h_M1 : 1 ∈ M)
(z1 z2 : ℂ) (h_z1 : z1 ∈ Kon_c M) (h_z2 : z2 ∈ Kon_c M) :
z1*z2 ∈ Kon_c M := by {
  -- idea: (a+bi)*(c+di) = ac+adi+bci-bd
  -- we can use, the sum-lemma, multiplication with i, and real multiplication
  have h_z1_re : ↑z1.re ∈ Kon_c M := by {
    apply re_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z1
  }
  have h_z2_re : ↑z2.re ∈ Kon_c M := by {
    apply re_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z2
  }
  have h_z1_im : ↑z1.im ∈ Kon_c M := by {
    apply im_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z1
  }
  have h_z2_im : ↑z2.im ∈ Kon_c M := by {
    apply im_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z2
  }


  have h_ac : ↑(z1.re * z2.re) ∈ Kon_c M := by {
    apply mul_real_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z1_re
    exact h_z2_re
  }

  have h_adi : z1.re * z2.im * Complex.I ∈ Kon_c M := by {
    apply times_i_is_constructable_lemma
    exact h_M0
    exact h_M1
    norm_cast
    apply mul_real_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z1_re
    exact h_z2_im
  }

  have h_bci : z1.im * z2.re * Complex.I ∈ Kon_c M := by {
    apply times_i_is_constructable_lemma
    exact h_M0
    exact h_M1
    norm_cast
    apply mul_real_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z1_im
    exact h_z2_re
  }

  have h_bd : -↑(z1.im*z2.im) ∈ Kon_c M := by {
    apply add_inv_is_constructable_lemma
    exact h_M0
    apply mul_real_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z1_im
    exact h_z2_im
  }

  have h : z1 * z2 = (z1.re*z2.re + z1.re*z2.im*Complex.I +
                      z1.im*z2.re*Complex.I - z1.im*z2.im) := by {
    simp [Complex.ext_iff]
  }

  rw [h]
  rw [sub_eq_add_neg]
  apply sum_is_constructable_lemma
  exact h_M0
  apply sum_is_constructable_lemma
  exact h_M0
  apply sum_is_constructable_lemma
  exact h_M0
  norm_cast
  apply h_adi
  apply h_bci
  simp at h_bd
  apply h_bd
}

----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M, with a ∈ ℝ constructable. Then: 1/a ∈ Kon(M)
theorem mul_real_inv_is_constructable_lemma (M : Set ℂ) (h_M0 : 0 ∈ M)
(h_M1 : 1 ∈ M) (a : ℝ) (h_a : ↑a ∈ Kon_c M) (h_a0 : a ≠ 0) : ↑a⁻¹ ∈ Kon_c M := by {
  -- IDEA: we draw a line from a*i to 1
  -- we move the line parallel to 1*i
  -- this line intersects with a⁻¹
  have h_p1 : 1-a*Complex.I+Complex.I ∈ Kon_c M := by {
    apply sum_is_constructable_lemma
    exact h_M0
    rw [sub_eq_add_neg]
    apply sum_is_constructable_lemma
    exact h_M0
    rw [Kon_c]
    use 0
    exact h_M1
    apply add_inv_is_constructable_lemma
    exact h_M0
    apply times_i_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_a
    apply int_times_i_constructable_lemma
    exact h_M0
    exact h_M1
    use 1
    simp
  }
  obtain ⟨i_p1, h_p1⟩ := h_p1

  have h_i : Complex.I ∈ Kon_c M := by {
    apply int_times_i_constructable_lemma
    exact h_M0
    exact h_M1
    use 1
    simp
  }
  obtain ⟨i_i, h_i⟩ := h_i

  rw [Kon_c]
  use i_i+i_p1+1
  rw [constructable_in_steps_c]
  right
  rw [constructable_points_c]
  left
  left
  rw [type1_constructable_c]
  simp
  rw [point_is_type1_constructable_c]
  -- we use: line1: [i, p1] and line2: [0, 1]
  use Complex.I, 1-a*Complex.I+Complex.I, 0, 1
  constructor
  apply constructable_in_more_steps_lemma M Complex.I i_i
  exact h_i
  simp
  constructor
  apply constructable_in_more_steps_lemma M (1-a*Complex.I+Complex.I) i_p1
  exact h_p1
  simp
  constructor
  apply constructable_in_more_steps_lemma M 0 0
  exact h_M0
  simp
  constructor
  apply constructable_in_more_steps_lemma M 1 0
  exact h_M1
  simp
  constructor
  simp [Complex.ext_iff]
  constructor
  simp
  -- it is the only intersection
  rw [only_intersection_lemma]
  constructor
  -- line1
  rw [line_through_c]
  simp
  use a⁻¹
  simp
  rw [mul_sub]
  simp
  rw [sub_eq_add_neg]
  nth_rewrite 2 [add_comm]
  rw [← add_assoc]
  simp
  ring_nf
  rw [mul_assoc]
  rw [mul_inv_cancel]
  simp
  exact_mod_cast h_a0
  -- line2
  constructor
  rw [line_through_c]
  simp
  use a⁻¹
  simp
  simp
  apply h_a0
  simp [Complex.ext_iff]
  simp
}

----------------------------------------------------------------
-- Lemma: let 0, 1, z ∈ M, with z ≠ 0. Then: 1/z ∈ Kon(M)
theorem mul_inv_is_constructable_lemma (M : Set ℂ) (h_M0 : 0 ∈ M) (h_M1 : 1 ∈ M)
(z : ℂ) (h_z : z ∈ Kon_c M) (h_z_not0 : z ≠ 0) : z⁻¹ ∈ Kon_c M := by {
  -- idea: 1/(a+bi) = a/(a^2+b^2) - i*b/(a^2+b^2)
  have h_re : ↑z.re ∈ Kon_c M := by {
    apply re_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z
  }
  have h_im : ↑z.im ∈ Kon_c M := by {
    apply im_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_z
  }

  have h_1 : ↑(z.re^2+z.im^2) ∈ Kon_c M := by {
    simp
    apply sum_is_constructable_lemma
    exact h_M0
    rw [pow_two]
    apply mul_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_re
    exact h_re
    rw [pow_two]
    apply mul_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_im
    exact h_im
  }

  have h_2 : ↑(z.re^2+z.im^2)⁻¹ ∈ Kon_c M := by {
    apply mul_real_inv_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_1
    have h1 : z.re^2 >= 0 := by apply pow_two_nonneg
    have h2 : z.im^2 >= 0 := by apply pow_two_nonneg
    contrapose! h_z_not0
    have h3 : z.re^2 = 0 := by linarith
    have h4 : z.im^2 = 0 := by linarith
    have h5 : z.re = 0 := by {
      rw [pow_two] at h3
      apply eq_zero_of_mul_self_eq_zero at h3
      exact h3
    }
    have h6 : z.im = 0 := by {
      rw [pow_two] at h4
      apply eq_zero_of_mul_self_eq_zero at h4
      exact h4
    }
    simp [Complex.ext_iff]
    constructor
    exact h5
    exact h6
  }

  have h_3 : ↑(z.re * (z.re^2+z.im^2)⁻¹) ∈ Kon_c M := by {
    simp
    apply mul_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_re
    exact_mod_cast h_2
  }

  have h_4 : ↑(z.im * (z.re^2+z.im^2)⁻¹ * Complex.I) ∈ Kon_c M := by {
    simp
    apply mul_is_constructable_lemma
    exact h_M0
    exact h_M1
    apply mul_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_im
    exact_mod_cast h_2
    apply int_times_i_constructable_lemma
    exact h_M0
    exact h_M1
    use 1
    simp
  }

  have h_5 : ↑(z.re * (z.re^2+z.im^2)⁻¹ -
              z.im * (z.re^2+z.im^2)⁻¹ * Complex.I) ∈ Kon_c M := by {
    rw [sub_eq_add_neg]
    apply sum_is_constructable_lemma
    exact h_M0
    exact_mod_cast h_3
    apply add_inv_is_constructable_lemma
    exact h_M0
    exact h_4
  }

  have h : z⁻¹ = ↑(z.re * (z.re^2+z.im^2)⁻¹ -
                  z.im * (z.re^2+z.im^2)⁻¹ * Complex.I) := by {
    rw [Complex.inv_def]
    have h_conj : (starRingEnd ℂ) z = z.re - z.im*Complex.I := by {
      rw [Complex.ext_iff]
      rw [Complex.conj_re]
      simp
    }
    rw [h_conj]
    rw [Complex.normSq]
    simp
    ring
  }

  rw [h]
  exact h_5
}



/-
----------------------------------------------------------------
Theorem 1.1.2 i)
let M be a set of complex numbers (points), with 0 ∈ M and 1 ∈ M

then: Kon(M) is a subfield of ℂ ∧     (i want to define subfield first)
      ℚ ⊆ Kon(M) ∧
      Kon(M) is closed under complex conjugation
-/
theorem theorem_1_1_2_i (M : Set ℂ) (h_M0 : 0 ∈ M) (h_M1 : 1 ∈ M) :
Q_as_C ⊆ Kon_c M ∧
∀ z ∈ Kon_c M, conj z ∈ Kon_c M := by {
  -- we show: ℚ ⊆ Kon(M)
  constructor
  intro x h_xq
  rw [Q_as_C] at h_xq
  simp at h_xq
  obtain ⟨q, h_q⟩ := h_xq

  -- we need to look, what a rational number looks like
  have h_q' : (∃ n : ℤ, ∃ d : ℕ, q = n/d ∧ d ≠ 0) := by {
    use q.num, q.den
    rw [Rat.num_div_den]
    simp
  }
  obtain ⟨n, d, h_q', h_d_not0⟩ := h_q'

  -- n and d are constructable
  have h_n : ↑n ∈ Kon_c M := by {
    apply int_constructable_lemma
    exact h_M0
    exact h_M1
    use n
  }
  --obtain ⟨i_n, h_n⟩ := h_n

  have h_d : ↑d ∈ Kon_c M := by {
    apply int_constructable_lemma
    exact h_M0
    exact h_M1
    use d
    simp
  }
  --obtain ⟨i_d, h_d⟩ := h_d

  -- 1/d is constructable
  have h_d_inv : (↑d)⁻¹ ∈ Kon_c M := by {
    apply mul_inv_is_constructable_lemma
    exact h_M0
    exact h_M1
    exact h_d
    exact_mod_cast h_d_not0
  }

  -- n/d is constructable
  rw [← h_q]
  rw [h_q']
  simp
  rw [div_eq_mul_inv]
  apply mul_is_constructable_lemma
  exact h_M0
  exact h_M1
  exact h_n
  apply h_d_inv

  -- we show: conj z is constructable
  intro z
  intro h_z
  apply conjugation_is_constructable_lemma
  exact h_M0
  exact h_M1
  exact h_z
}


-----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M. Let a ∈ ℝ with a ∈ Kon(M).
-- Then: √a ∈ Kon(M)
theorem sqrt_real_is_constructable_lemma (a : ℝ) (M : Set ℂ) (h_M0 : 0 ∈ M)
(h_M1 : 1 ∈ M) (h_a : ↑a ∈ Kon_c M) (h_a0 : a >= 0) :
↑(Real.sqrt a) ∈ Kon_c M := by {
  -- plan: we draw a circle with center=(a-1)/2 and radius=(a+1)/2
  -- the intersection with the im-axis is sqrt(a)*i
  have h_p1 : ↑((a-1)/2) ∈ Kon_c M := by {
    rw [div_eq_mul_inv]
    simp
    apply mul_is_constructable_lemma
    exact h_M0
    exact h_M1
    rw [sub_eq_add_neg]
    apply sum_is_constructable_lemma
    exact h_M0
    exact h_a
    apply add_inv_is_constructable_lemma
    exact h_M0
    rw [Kon_c]
    use 0
    exact h_M1
    apply mul_inv_is_constructable_lemma
    exact h_M0
    exact h_M1
    apply int_constructable_lemma
    exact h_M0
    exact h_M1
    use 2
    simp
    simp
  }
  obtain ⟨i_p1, h_p1⟩ := h_p1

  have h_i : Complex.I ∈ Kon_c M := by {
    apply int_times_i_constructable_lemma
    exact h_M0
    exact h_M1
    use 1
    simp
  }
  obtain ⟨i_i, h_i⟩ := h_i
  obtain ⟨i_a, h_a⟩ := h_a

  -- we start with the construction
  have h_sqrt_i : Complex.I * Real.sqrt a ∈ Kon_c M := by {
    rw [Kon_c]
    use i_i+i_p1+i_a+1
    rw [constructable_in_steps_c]
    right
    rw [constructable_points_c]
    left
    right
    rw [type2_constructable_c]
    simp
    rw [point_is_type2_constructable_c]
    -- we use: line: [0, i] and circle: [center=p1, radius=(a+1)/2]
    use 0, Complex.I, (a-1)/2, (a-1)/2, a
    constructor
    apply constructable_in_more_steps_lemma M 0 0
    exact h_M0
    simp
    constructor
    apply constructable_in_more_steps_lemma M Complex.I i_i
    exact h_i
    rw [add_assoc]
    simp
    constructor
    apply constructable_in_more_steps_lemma M ((a-1)/2) i_p1
    exact_mod_cast h_p1
    rw [add_comm, ← add_assoc]
    simp
    constructor
    apply constructable_in_more_steps_lemma M ((a-1)/2) i_p1
    exact_mod_cast h_p1
    rw [add_comm, ← add_assoc]
    simp
    constructor
    apply constructable_in_more_steps_lemma M a i_a
    exact h_a
    simp
    constructor
    simp [Complex.ext_iff]
    constructor
    rw [line_through_c]
    simp
    use √a
    rw [mul_comm]
    rw [circle_c, distance_between_points_c]
    simp
    repeat rw [Real.sq_sqrt]
    ring
    apply pow_two_nonneg
    exact h_a0
  }

  have h : Complex.I * Complex.I * √a ∈ Kon_c M := by {
    rw [mul_assoc]
    apply mul_is_constructable_lemma
    exact h_M0
    exact h_M1
    apply int_times_i_constructable_lemma
    exact h_M0
    exact h_M1
    use 1
    simp
    exact h_sqrt_i
  }

  simp at h

  have h2 : -(-↑√a) ∈ Kon_c M := by {
    apply add_inv_is_constructable_lemma
    exact h_M0
    exact h
  }

  simp at h2
  exact h2
}

-----------------------------------------------------------------
-- Lemma: let 0,1 ∈ M. Let z ∈ ℂ with z ∈ Kon(M).
-- Then: z/|z| ∈ Kon(M)       (the normed number)
theorem normed_is_constructable_lemma (z : ℂ) (M : Set ℂ) (h_M0 : 0 ∈ M)
(h_M1 : 1 ∈ M) (h_z : z ∈ Kon_c M) (h_z0 : z ≠ 0) :
z/(Real.sqrt (z.re^2+z.im^2)) ∈ Kon_c M := by {
  obtain ⟨i_z, h_z⟩ := h_z
  rw [Kon_c]
  use i_z+1
  rw [constructable_in_steps_c]
  right
  rw [constructable_points_c]
  left
  right
  rw [type2_constructable_c]
  simp
  rw [point_is_type2_constructable_c]
  -- we use the line: [0, z] and the circle: [center=0, radius=1]
  use 0, z, 0, 0, 1
  have h_0 : 0 ∈ constructable_in_steps_c M i_z := by {
    apply constructable_in_more_steps_lemma M 0 0
    exact h_M0
    simp
  }
  constructor
  exact h_0
  constructor
  exact h_z
  constructor
  exact h_0
  constructor
  exact h_0
  constructor
  apply constructable_in_more_steps_lemma M 1 0
  exact h_M1
  simp
  constructor
  symm
  exact h_z0
  constructor
  rw [line_through_c]
  simp
  use 1/↑√(z.re ^ 2 + z.im ^ 2)
  rw [mul_comm]
  simp
  rw [div_eq_mul_inv]
  rw [circle_c, distance_between_points_c]
  simp
  rw [Real.sq_sqrt]
  repeat rw [div_eq_mul_inv]
  rw [← add_mul]
  rw [mul_inv_cancel]
  contrapose! h_z0
  have h1 : z.re^2 >= 0 := by apply pow_two_nonneg
  have h2 : z.im^2 >= 0 := by apply pow_two_nonneg
  have h3 : z.re^2 = 0 := by linarith
  have h4 : z.im^2 = 0 := by linarith
  have h5 : z.re = 0 := by {
    rw [pow_two] at h3
    apply eq_zero_of_mul_self_eq_zero at h3
    exact h3
  }
  have h6 : z.im = 0 := by {
    rw [pow_two] at h4
    apply eq_zero_of_mul_self_eq_zero at h4
    exact h4
  }
  simp [Complex.ext_iff]
  rw [h5, h6]
  simp
  have h1 : z.re^2 >= 0 := by apply pow_two_nonneg
  have h2 : z.im^2 >= 0 := by apply pow_two_nonneg
  linarith
}


-----------------------------------------------------------------
-- Theorem 1.1.2 ii)
-- let M ⊆ ℂ, with 0,1 ∈ M. Let z ∈ ℂ with z^2 ∈ Kon(M)
-- then: √z ∈ Kon(M)
theorem theorem_1_1_2_ii (M : Set ℂ) (h_M0 : 0 ∈ M) (h_M1 : 1 ∈ M)
(z : ℂ) (h_z2 : z^2 ∈ Kon_c M) : z ∈ Kon_c M := by {
  by_cases h_case : z = 0
  case pos =>
    rw [h_case]
    rw [Kon_c]
    use 0
    exact h_M0

  case neg =>
    -- we want to project |z| to the real axis
    have h_z_r : ↑(Real.sqrt ((z.re^2-z.im^2)^2 + 4*z.re^2*z.im^2)) ∈ Kon_c M := by {
      have h1 : ↑((z^2).re) ∈ Kon_c M := by {
        apply re_is_constructable_lemma
        exact h_M0
        exact h_M1
        exact h_z2
      }
      have h2 : ↑((z^2).im) ∈ Kon_c M := by {
        apply im_is_constructable_lemma
        exact h_M0
        exact h_M1
        exact h_z2
      }
      rw [pow_two] at h1
      simp at h1
      repeat rw [← pow_two] at h1
      rw [pow_two] at h2
      simp at h2
      rw [mul_comm] at h2
      rw [← two_mul] at h2
      nth_rewrite 2 [mul_comm] at h2
      rw [← mul_assoc] at h2

      have h3 : ↑((z.re ^ 2 - z.im ^ 2) ^ 2) ∈ Kon_c M := by {
        rw [pow_two]
        simp
        apply mul_is_constructable_lemma
        exact h_M0
        exact h_M1
        exact h1
        exact h1
      }

      have h4 : ↑((2*z.re*z.im)*(2*z.re*z.im)) ∈ Kon_c M := by {
        simp
        apply mul_is_constructable_lemma
        exact h_M0
        exact h_M1
        exact h2
        exact h2
      }

      have h5 : ↑((2*z.re*z.im)*(2*z.re*z.im)) = 4 * z.re ^ 2 * z.im ^ 2 := by {
        ring
      }

      rw [h5] at h4

      apply sqrt_real_is_constructable_lemma
      exact h_M0
      exact h_M1
      simp
      apply sum_is_constructable_lemma
      exact h_M0
      exact_mod_cast h3
      exact_mod_cast h4
      simp
      have h6 : (z.re ^ 2 - z.im ^ 2) ^ 2 >= 0 := by apply pow_two_nonneg
      have h7 : 4 * z.re ^ 2 * z.im ^ 2 >= 0 := by {
        apply mul_nonneg
        apply mul_nonneg
        simp
        apply pow_two_nonneg
        apply pow_two_nonneg
      }
      linarith
    }

    -- simplifying
    have h : Real.sqrt ((z.re^2-z.im^2)^2 + 4*z.re^2*z.im^2) = z.re^2+z.im^2 := by {
      ring_nf
      have h1 : z.re^2*z.im^2*2+z.re^4+z.im^4 = (z.re^2+z.im^2)^2 := by {
        ring
      }
      rw [h1]
      rw [Real.sqrt_sq]
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
    }
    rw [h] at h_z_r

    have h_z_sqrt_r : ↑(Real.sqrt (z.re^2+z.im^2)) ∈ Kon_c M := by {
      apply sqrt_real_is_constructable_lemma
      exact h_M0
      exact h_M1
      exact h_z_r
      have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
      have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
      linarith
    }

    -- now we want to halve the angle of z^2
    -- to do that, we construct a new point:
    -- we draw two more circles: center=z^2 and center=|z^2|
    -- the line from 0 to the intersection of the two circles is halve the angle of z^2
    obtain ⟨i_z_r, h_z_r⟩ := h_z_r
    obtain ⟨i_z2, h_z2⟩ := h_z2
    have h_p1 : 2*z.re^2+2*z.re*z.im*Complex.I ∈ Kon_c M := by {
      by_cases h_case2 : z.im = 0
      case pos =>
        rw [h_case2]
        simp
        rw [h_case2] at h_z_r
        simp at h_z_r
        apply mul_is_constructable_lemma
        exact h_M0
        exact h_M1
        apply int_constructable_lemma
        exact h_M0
        exact h_M1
        use 2
        simp
        rw [Kon_c]
        use i_z_r

      case neg =>
        rw [Kon_c]
        use i_z_r+i_z2+1
        rw [constructable_in_steps_c]
        right
        rw [constructable_points_c]
        right
        rw [type3_constructable_c]
        simp
        rw [point_is_type3_constructable_c]
        -- we use: circle1: [center=z^2, radius=|z^2|] and circle2: [center=|z^2|, radius=|z^2|]
        use z^2, 0, z.re^2+z.im^2, z.re^2+z.im^2, 0, z.re^2+z.im^2
        have h_re : ↑(z.re^2+z.im^2) ∈ constructable_in_steps_c M (i_z_r+i_z2) := by {
          apply constructable_in_more_steps_lemma M ↑(z.re^2+z.im^2) i_z_r
          exact h_z_r
          simp
        }
        constructor
        apply constructable_in_more_steps_lemma M (z^2) i_z2
        exact h_z2
        simp
        constructor
        apply constructable_in_more_steps_lemma M 0 0
        exact h_M0
        simp
        constructor
        exact_mod_cast h_re
        constructor
        exact_mod_cast h_re
        constructor
        apply constructable_in_more_steps_lemma M 0 0
        exact h_M0
        simp
        constructor
        exact_mod_cast h_re
        constructor
        simp [pow_two, Complex.ext_iff]
        rw [sub_eq_add_neg]
        simp
        contrapose! h_case2
        obtain ⟨h_case2, _⟩ := h_case2
        exact h_case2

        -- circle1
        constructor
        rw [distance_between_points_c]
        have h_tmp : (Complex.im 0 - ((↑z.re^2 + ↑z.im^2):ℂ).im)^2 = 0 := by {
          simp [Complex.ext_iff]
          repeat rw [pow_two]
          simp
        }
        have h_tmp2 : (Complex.re 0 - ((↑z.re^2+↑z.im^2):ℂ).re) ^ 2 = (↑z.re^2+↑z.im^2)^2 := by {
          simp
          repeat rw [pow_two]
          simp
          ring
        }

        rw [h_tmp, h_tmp2]
        simp
        rw [Real.sqrt_sq]

        rw [circle_c]
        simp
        repeat rw [pow_two]
        simp
        ring
        have h_1 : z.re^2 >= 0 := by apply pow_two_nonneg
        have h_2 : z.im^2 >= 0 := by apply pow_two_nonneg
        linarith

        -- circle2
        rw [distance_between_points_c]
        have h_tmp : (Complex.im 0 - ((↑z.re^2 + ↑z.im^2):ℂ).im)^2 = 0 := by {
          simp [Complex.ext_iff]
          repeat rw [pow_two]
          simp
        }
        have h_tmp2 : (Complex.re 0 - ((↑z.re^2+↑z.im^2):ℂ).re) ^ 2 = (↑z.re^2+↑z.im^2)^2 := by {
          simp
          repeat rw [pow_two]
          simp
          ring
        }

        rw [h_tmp, h_tmp2]
        simp
        rw [Real.sqrt_sq]

        rw [circle_c]
        simp
        repeat rw [pow_two]
        simp
        ring
        have h_1 : z.re^2 >= 0 := by apply pow_two_nonneg
        have h_2 : z.im^2 >= 0 := by apply pow_two_nonneg
        linarith
    }
    obtain ⟨i_p1, h_p1⟩ := h_p1
    obtain ⟨i_z_sqrt_r, h_z_sqrt_r⟩ := h_z_sqrt_r

    have h_z : z.re + z.im*Complex.I ∈ Kon_c M := by {
      by_cases h_case2 : 0 = 2 * ↑z.re ^ 2 + 2 * ↑z.re * ↑z.im * Complex.I
      case pos =>
        have h1 : z.re^2 >= 0 := by apply pow_two_nonneg
        simp [Complex.ext_iff] at h_case2
        obtain ⟨h_case2_1, h_case2_2⟩ := h_case2
        simp [pow_two] at h_case2_1
        rw [h_case2_1]
        rw [h_case2_1] at h_z_sqrt_r
        simp at h_z_sqrt_r
        rw [Real.sqrt_sq_eq_abs] at h_z_sqrt_r

        by_cases h_case3 : z.im >= 0
        case pos =>
          rw [abs_of_nonneg h_case3] at h_z_sqrt_r
          simp
          apply times_i_is_constructable_lemma
          exact h_M0
          exact h_M1
          rw [Kon_c]
          use i_z_sqrt_r

        case neg =>
          simp at h_case3
          rw [abs_of_neg h_case3] at h_z_sqrt_r
          simp
          apply times_i_is_constructable_lemma
          exact h_M0
          exact h_M1
          have hh : z.im = -(-(z.im:ℂ)) := by simp
          rw [hh]
          apply add_inv_is_constructable_lemma
          exact h_M0
          use i_z_sqrt_r
          exact_mod_cast h_z_sqrt_r

      case neg =>
        use i_p1+i_z_sqrt_r+1
        rw [constructable_in_steps_c]
        right
        rw [constructable_points_c]
        left
        right
        rw [type2_constructable_c]
        simp
        rw [point_is_type2_constructable_c]
        -- we use the line [0, p1] and the circle: [center=0, radius=|z|]
        use 0
        use 2 * ↑z.re ^ 2 + 2 * ↑z.re * ↑z.im * Complex.I
        use 0, 0, Real.sqrt (z.re^2+z.im^2)
        have h_0 : 0 ∈ constructable_in_steps_c M (i_p1+i_z_sqrt_r) := by {
          apply constructable_in_more_steps_lemma M 0 0
          exact h_M0
          simp
        }
        constructor
        exact h_0
        constructor
        apply constructable_in_more_steps_lemma M
              (2 * ↑z.re ^ 2 + 2 * ↑z.re * ↑z.im * Complex.I) i_p1
        exact h_p1
        simp
        constructor
        exact h_0
        constructor
        exact h_0
        constructor
        apply constructable_in_more_steps_lemma M (Real.sqrt (z.re^2+z.im^2)) i_z_sqrt_r
        exact h_z_sqrt_r
        simp
        constructor
        apply h_case2
        constructor
        -- line
        rw [line_through_c]
        simp
        use 1/(2*z.re)
        simp [Complex.ext_iff, pow_two]
        constructor
        ring_nf
        rw [pow_two, mul_assoc]
        rw [mul_inv_cancel]
        simp
        contrapose! h_case2
        rw [h_case2]
        simp
        ring_nf
        rw [mul_inv_cancel]
        simp
        contrapose! h_case2
        rw [h_case2]
        simp
        -- circle
        rw [distance_between_points_c]
        have h_tmp : (Complex.im 0 - (↑√(z.re ^ 2 + z.im ^ 2):ℂ).im) ^ 2 = 0 := by {
          simp [Complex.ext_iff]
        }
        have h_tmp2 : (Complex.re 0 - (↑√(z.re^2+z.im^2):ℂ).re) ^ 2 = z.re^2+z.im^2 := by {
          simp
          rw [Real.sq_sqrt]
          have h_re : z.re^2 >= 0 := by apply pow_two_nonneg
          have h_im : z.im^2 >= 0 := by apply pow_two_nonneg
          linarith
        }

        rw [h_tmp, h_tmp2]
        simp
        rw [circle_c]
        simp
        rw [Real.sq_sqrt]
        have h_1 : z.re^2 >= 0 := by apply pow_two_nonneg
        have h_2 : z.im^2 >= 0 := by apply pow_two_nonneg
        linarith
    }

    have h_zz : z = z.re + z.im * Complex.I := by {
      simp [Complex.ext_iff]
    }
    rw [h_zz]
    apply h_z
}
