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
-- Lemma 2.1.5:
theorem lemma_2_1_5 (H : Subgroup ℤ) :
∃ n : ℤ, H.carrier = { x : ℤ | ∃ z : ℤ, x = n*z } := by {
  by_cases h_case : H.carrier = {0}
  -- trivial case: H = {0}
  case pos =>
    rw [h_case]
    use 0
    simp

  case neg =>
    sorry
}
