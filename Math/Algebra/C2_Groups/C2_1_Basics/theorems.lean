import Math.Algebra.C2_Groups.C2_1_Basics.definitions

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
theorem nat_minimum_lemma2 (S : Set ℕ) (h_nonempty : S ≠ ∅) :
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
theorem lemma_2_1_5 (H : Subgroup ℤ) :
∃ n : ℤ, H.carrier = { x : ℤ | ∃ z : ℤ, x = n*z } := by {
  -- first we prove, that 0 ∈ H.carrier
  have h_0 : 0 ∈ H.carrier := by {
    sorry
    --apply MyGroup.one
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
      have h_nonempty : ∃ x, x ∈ H.carrier ∧ x ≠ 0 := by sorry
      obtain ⟨x, hm, hm_nz⟩ := h_nonempty
      let S := {x : ℕ | ∃ k ∈ H.carrier, x = |k| ∧ k ≠ 0}
      have hS_nonempty : S ≠ ∅ := by sorry
      obtain ⟨n, ⟨k, hk, hk_eq, hk_ne⟩, h_smallest⟩ :=


      contrapose! h_case
      ext x
      constructor
      simp
      contrapose! h_case






      use 0
      constructor
      apply h_0
      contrapose! h_case
      ext x
      constructor
      intro h_x
      simp

      specialize h_case x
      have h : ∃ m' ∈ H.carrier, x ≠ m' ∧ |m'| ≤ |x| := by {
        apply h_case
        exact h_x
      }
      clear h_case
      obtain ⟨m', h1, h2, h3⟩ := h




      --obtain ⟨m, h_case⟩ := h_case
      have h_pos : ∃ m ∈ H.carrier, m > 0 := by sorry
      obtain ⟨m, hmH, hm_pos⟩ := h_pos
      have hm_min : ∀ m' ∈ H.carrier, 0 < m' → m ≤ m' := by sorry

      use m
      constructor
      exact hmH
      intros m' hm'H hm_neq
      have : |m| ≤ |m'| := by sorry
      apply lt_of_le_of_ne
      exact this

      rw [abs_of_nonneg]
    }

    case neg =>
      sorry
}
