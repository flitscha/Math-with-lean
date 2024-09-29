import Math.Algebra.C2_Groups.C2_1_Basics.theorems


-- Definition der Äquivalenzrelation für linke Nebenklassen
def left_coset_rel {G : Type} [MyGroup G] (H : normal_subgroup G) : G → G → Prop :=
  λ g1 g2 => ∃ h ∈ H.carrier, g1 = MyGroup.mul g2 h

-- Zeige, dass es sich um eine Äquivalenzrelation handelt Setoid = äquivalenzrelation + Beweis
instance left_coset_setoid (G : Type) [MyGroup G] (H : normal_subgroup G) : Setoid G := {
  r := left_coset_rel H,
  iseqv := by {
    constructor
    -- reflexivity
    case refl =>
      intro g
      rw [left_coset_rel]
      use MyGroup.one
      constructor
      apply subgroup_one_mem_lemma
      rw [MyGroup.mul_one]

    -- symmetry
    case symm =>
      intros x y h
      rw [left_coset_rel] at h ⊢
      obtain ⟨g, h_g, h_x⟩ := h
      use MyGroup.inv g
      constructor
      apply Subgroup.inv_mem
      apply h_g
      rw [h_x]
      rw [MyGroup.mul_assoc]
      rw [MyGroup.mul_inv]
      rw [MyGroup.mul_one]

    -- transitivity
    case trans =>
      intros x y z h1 h2
      rw [left_coset_rel] at h1 h2 ⊢
      obtain ⟨g1, h_g1, h_x⟩ := h1
      obtain ⟨g2, h_g2, h_y⟩ := h2
      use MyGroup.mul g2 g1
      rw [h_x, h_y]
      constructor
      apply Subgroup.mul_mem
      exact ⟨h_g2, h_g1⟩
      rw [MyGroup.mul_assoc]
  }
}


def quotient_group (G : Type) [MyGroup G] (H : normal_subgroup G) : Type :=
  Quotient (left_coset_setoid G H)

/-
theorem quotient_group_eq_lemma (G : Type) [MyGroup G] (H : normal_subgroup G) :
  quotient_group G H = { x : G // ∀ g : G, MyGroup.mul x (MyGroup.inv g) ∈ H.carrier } := by {

  rw [quotient_group]
  simp [Quotient, Setoid.r]

}-/

--theorem quotient_group_eq_lemma (G : Type) [MyGroup G] (H : normal_subgroup G) :
--quotient_group G H = { ⟦x⟧ ∈  left_coset_setoid G H | x ∈ G }
/-
noncomputable def quotient_to_repr {G : Type} [MyGroup G] {H : normal_subgroup G} :
  quotient_group G H → G × Setoid G :=
  λ x =>
    let g : G := Quot.out x
    (g, left_coset_setoid G H)
-/

noncomputable def quotient_to_repr {G : Type} [MyGroup G] {H : normal_subgroup G} :
quotient_group G H -> G := by {
  intro x
  exact Quot.out x
}


theorem repr_lemma {G : Type} [MyGroup G] {H : normal_subgroup G}
(a : quotient_group G H) : ⟦quotient_to_repr a⟧ = a := by {
  let g := quotient_to_repr a
  apply Quotient.inductionOn
  intro x
  sorry
}

/-
theorem repr_lemma {G : Type} [MyGroup G] {H : normal_subgroup G}
(a : quotient_group G H) : ⟦quotient_to_repr a⟧ = a := by {
  sorry
}-/


def quotient_group_mul {G : Type} [MyGroup G] (H : normal_subgroup G) :
quotient_group G H -> quotient_group G H -> quotient_group G H := by {
  intros x y
  apply Quotient.liftOn₂ x y (λ g₁ g₂ => ⟦MyGroup.mul g₁ g₂⟧)

  -- we show, that this definition is welldefined
  intros a1 b1 a2 b2
  intros h_a h_b
  simp [HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, left_coset_setoid, left_coset_rel] at h_a h_b ⊢
  obtain ⟨ha, h_ha, h_a⟩ := h_a
  obtain ⟨hb, h_hb, h_b⟩ := h_b

  -- we use that H is normal
  have h_normal : ∀ h : H.carrier, ∀ g : G,
      MyGroup.mul (MyGroup.mul (MyGroup.inv g) h) g ∈ H.carrier := by {
    have h_tmp : ∀ (g : G), left_coset G H g = right_coset G H g := by {
      obtain ⟨H, normal⟩ := H
      exact normal
    }
    rw [normal_iff_lemma] at h_tmp
    apply h_tmp
  }

  use MyGroup.mul (MyGroup.mul (MyGroup.mul (MyGroup.inv b2) ha) b2) hb
  constructor
  apply Subgroup.mul_mem
  constructor
  specialize h_normal ⟨ha, h_ha⟩ b2
  apply h_normal
  exact h_hb

  rw [h_a, h_b]
  repeat rw [← MyGroup.mul_assoc]
  nth_rewrite 6 [MyGroup.mul_assoc]
  rw [MyGroup.mul_inv, MyGroup.mul_one]
}


def quotient_group_inv {G : Type} [MyGroup G] {H : normal_subgroup G} :
quotient_group G H -> quotient_group G H := by {
  intro x
  apply Quotient.liftOn x (λ g₁ => ⟦MyGroup.inv g₁⟧)

  -- we show, that this definition is welldefined
  intros a1 a2
  intro h
  simp [HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r, left_coset_setoid, left_coset_rel] at h ⊢
  obtain ⟨ha, h_ha, h⟩ := h

  -- we use that H is normal
  have h_normal : ∀ h : H.carrier, ∀ g : G,
      MyGroup.mul (MyGroup.mul (MyGroup.inv g) h) g ∈ H.carrier := by {
    have h_tmp : ∀ (g : G), left_coset G H g = right_coset G H g := by {
      obtain ⟨H, normal⟩ := H
      exact normal
    }
    rw [normal_iff_lemma] at h_tmp
    apply h_tmp
  }

  use MyGroup.mul (MyGroup.mul a2 (MyGroup.inv ha)) (MyGroup.inv a2)
  constructor

  have : MyGroup.inv ha ∈ H.carrier := by {
    apply Subgroup.inv_mem
    apply h_ha
  }
  specialize h_normal ⟨MyGroup.inv ha, this⟩ (MyGroup.inv a2)
  simp [double_inv_lemma] at h_normal
  apply h_normal

  rw [h]
  rw [mul_inv_lemma]
  repeat rw [← MyGroup.mul_assoc]
  rw [MyGroup.inv_mul, MyGroup.one_mul]
}


-- Instanz der Gruppe auf der Quotientengruppe
instance quotient_group_group (G : Type) [MyGroup G] (H : normal_subgroup G) :
MyGroup (quotient_group G H) := {
  mul := quotient_group_mul H
  one := ⟦MyGroup.one⟧
  inv :=  quotient_group_inv

  one_mul := by {
    intro a
    let g : G := quotient_to_repr a
    have : ⟦g⟧ = a := by {
      simp [g]
      apply repr_lemma
    }
    rw [← this]
    simp [quotient_group_mul, MyGroup.one_mul]
  }

  mul_one := by {
    intro a
    let g : G := quotient_to_repr a
    have : ⟦g⟧ = a := by {
      simp [g]
      apply repr_lemma
    }
    rw [← this]
    simp [quotient_group_mul, MyGroup.mul_one]
  }

  mul_assoc := by {
    intros a b c
    let g_a : G := quotient_to_repr a
    let g_b : G := quotient_to_repr b
    let g_c : G := quotient_to_repr c
    have h_a : ⟦g_a⟧ = a := by {
      simp [g_a]
      apply repr_lemma
    }
    have h_b : ⟦g_b⟧ = b := by {
      simp [g_b]
      apply repr_lemma
    }
    have h_c : ⟦g_c⟧ = c := by {
      simp [g_c]
      apply repr_lemma
    }
    rw [← h_a, ← h_b, ← h_c]
    simp [quotient_group_mul, MyGroup.mul_assoc]
  }

  inv_mul := by {
    intro a
    let g : G := quotient_to_repr a
    have : ⟦g⟧ = a := by {
      simp [g]
      apply repr_lemma
    }
    rw [← this]
    simp [quotient_group_inv, quotient_group_mul, MyGroup.inv_mul]
  }

  mul_inv := by {
    intro a
    let g : G := quotient_to_repr a
    have : ⟦g⟧ = a := by {
      simp [g]
      apply repr_lemma
    }
    rw [← this]
    simp [quotient_group_inv, quotient_group_mul, MyGroup.mul_inv]
  }
}
