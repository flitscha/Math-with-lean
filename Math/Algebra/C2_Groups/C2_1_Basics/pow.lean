import Math.Algebra.C2_Groups.C2_1_Basics.quotient_group

-- definitions

-- g^n, where n ∈ ℕ
def group_pow_nat {G : Type} [MyGroup G] (g : G) : ℕ → G
| 0       => MyGroup.one
| (n + 1) => MyGroup.mul g (group_pow_nat g n)


-- g^n, where n ∈ ℤ
def group_pow {G : Type} [MyGroup G] (g : G) : ℤ → G
| Int.ofNat n => group_pow_nat g n
| Int.negSucc n' => MyGroup.inv (group_pow_nat g (n' + 1))

-----------------------------------------------------------
-- theorems

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
