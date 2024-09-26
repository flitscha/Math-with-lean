import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic


class MyGroup (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul : ∀ a : G, mul (inv a) a = one
  mul_inv : ∀ a : G, mul a (inv a) = one


class AbelianGroup (G : Type) extends MyGroup G where
  mul_comm : ∀ a b : G, mul a b = mul b a


def group_pow_nat {G : Type} [MyGroup G] (g : G) : ℕ → G
| 0       => MyGroup.one
| (n + 1) => MyGroup.mul g (group_pow_nat g n)


def group_pow {G : Type} [MyGroup G] (g : G) : ℤ → G
| Int.ofNat n => group_pow_nat g n
| Int.negSucc n' => MyGroup.inv (group_pow_nat g (n' + 1))


structure Subgroup (G : Type) [MyGroup G] where
  carrier : Set G -- this is a subset of G. (the subgroup)
  nonempty : carrier ≠ ∅
  mul_mem : ∀ a b : G, (a ∈ carrier ∧ b ∈ carrier) → MyGroup.mul a b ∈ carrier
  inv_mem : ∀ a : G, a ∈ carrier → MyGroup.inv a ∈ carrier

def Subgroup.toType [MyGroup G] (H : Subgroup G) : Type :=
  { x // x ∈ H.carrier }
/-
structure SubgroupOfSubgroup {G : Type} [MyGroup G] (H : Subgroup G) extends Subgroup G where
  h_carrier : carrier ⊆ H.carrier

def SoS_to_S {G : Type} [MyGroup G] (H : Subgroup G) :
SubgroupOfSubgroup H -> Subgroup G := by {
  intro h
  exact h.toSubgroup
}-/

--instance {G : Type} [MyGroup G] : Coe (Subgroup G) (Set G) := {
--  coe := λ h => h.carrier
--}

def SubgroupToGroup {G : Type} [MyGroup G] (H : Subgroup G) : MyGroup H.carrier := {
  mul := by {
    intros a b
    have h : ↑(MyGroup.mul ↑a ↑b) ∈ ↑H.carrier := by {
      apply H.mul_mem
      simp
    }
    exact ⟨MyGroup.mul ↑a ↑b, h⟩
  }
  one := by {
    have h : MyGroup.one ∈ ↑H.carrier := by {
      have h1 : H.carrier ≠ ∅ := by exact H.nonempty
      have h2 : ∃ a : G, a ∈ H.carrier := by {
        contrapose! h1
        apply Set.eq_empty_iff_forall_not_mem.mpr
        exact h1
      }
      obtain ⟨a, h2⟩ := h2
      have h3 : MyGroup.inv a ∈ H.carrier := by {
        apply H.inv_mem
        exact h2
      }
      have h4 : MyGroup.mul a (MyGroup.inv a) ∈ H.carrier := by {
        apply H.mul_mem
        constructor
        exact h2
        exact h3
      }
      have h5 : MyGroup.mul a (MyGroup.inv a) = MyGroup.one := by {
        apply MyGroup.mul_inv
      }
      rw [← h5]
      exact h4
    }
    exact ⟨MyGroup.one, h⟩
  }
  inv := by {
    intro a
    have h : MyGroup.inv ↑a ∈ H.carrier := by {
      apply H.inv_mem
      simp
    }
    exact ⟨MyGroup.inv a, h⟩
  }
  mul_assoc := by {
    intros a b c
    simp
    have h : ∀ a b c : G, MyGroup.mul (MyGroup.mul a b) c =
                          MyGroup.mul a (MyGroup.mul b c) := by {
      exact MyGroup.mul_assoc
    }
    apply h
  }
  one_mul := by {
    simp
    have h : ∀ a : G, MyGroup.mul MyGroup.one a = a := by exact MyGroup.one_mul
    intro a
    intro
    apply h
  }
  mul_one := by {
    simp
    have h : ∀ a : G, MyGroup.mul a MyGroup.one = a := by exact MyGroup.mul_one
    intro a
    intro
    apply h
  }
  inv_mul := by {
    simp
    have h : ∀ a : G, MyGroup.mul (MyGroup.inv a) a = MyGroup.one := by exact MyGroup.inv_mul
    intro a
    intro
    apply h
  }
  mul_inv := by {
    simp
    have h : ∀ a : G, MyGroup.mul a (MyGroup.inv a) = MyGroup.one := by exact MyGroup.mul_inv
    intro a
    intro
    apply h
  }
}

structure AbelianSubgroup (G : Type) [MyGroup G] extends Subgroup G where
  mul_comm : ∀ a b : carrier, MyGroup.mul (a : G) b = MyGroup.mul (b : G) a

class GroupHomomorphism (G1 : Type) (G2 : Type) [MyGroup G1] [MyGroup G2] :=
  f : G1 -> G2
  mul : ∀ a b : G1, f (MyGroup.mul a b) = MyGroup.mul (f a) (f b)

structure GroupIsomorphism (G1 : Type) (G2 : Type) [MyGroup G1]
[MyGroup G2] extends GroupHomomorphism G1 G2 :=
  (injective : Function.Injective f)
  (surjective : Function.Surjective f)

-- proof, that a group isomorphism is a group homomorphism
def isomorphismToHomomorphism {G1 : Type} {G2 : Type}
[MyGroup G1] [MyGroup G2] (ψ : GroupIsomorphism G1 G2) : GroupHomomorphism G1 G2 := {
  f := ψ.f
  mul := ψ.mul
}

instance coeIsomorphismToHomomorphism {G1 : Type} {G2 : Type}
[MyGroup G1] [MyGroup G2] :
Coe (GroupIsomorphism G1 G2) (GroupHomomorphism G1 G2) := {
  coe := isomorphismToHomomorphism
}


-- two groups are called isomorphic, iff there exists a group-isomorphism between the two groups
def groupsAreIsomorphic (G1 : Type) (G2 : Type) [MyGroup G1] [MyGroup G2] : Prop :=
  ∃ _ : GroupIsomorphism G1 G2, true


-- left coset = linke Nebenklasse
def left_coset (G : Type) [MyGroup G] (H : Subgroup G) (g : G) : Set G :=
  { x | ∃ h : H.carrier, x = MyGroup.mul g ↑h }

-- right coset = rechte Nebenklasse
def right_coset (G : Type) [MyGroup G] (H : Subgroup G) (g : G) : Set G :=
  { x | ∃ h : H.carrier, x = MyGroup.mul ↑h g }

-- Set of all cosets
def all_left_cosets (G : Type) [MyGroup G] (H : Subgroup G) : Set (Set G) :=
  { x | ∃ g : G, x = left_coset G H g }

def all_right_cosets (G : Type) [MyGroup G] (H : Subgroup G) : Set (Set G) :=
  { x | ∃ g : G, x = right_coset G H g }

-- normal subgroup: gH = Hg   ∀ g ∈ G
structure normal_subgroup (G : Type) [MyGroup G] extends Subgroup G where
  normal : ∀ g : G, left_coset G toSubgroup g = right_coset G toSubgroup g

-- normal subgroup is a subgroup
def normal_sg_to_sg {G : Type} [MyGroup G] (H : normal_subgroup G) :
Subgroup G := {
  carrier := H.carrier
  nonempty := H.nonempty
  mul_mem := H.mul_mem
  inv_mem := H.inv_mem
}

instance coe_normal_subgroup_to_subgroup {G : Type} [MyGroup G] :
Coe (normal_subgroup G) (Subgroup G) := {
  coe := normal_sg_to_sg
}

-- kernel of homomorphism
def ker {G : Type} {H : Type} [MyGroup G] [MyGroup H]
(φ : GroupHomomorphism G H) : Set G := { g | φ.f g = MyGroup.one }

-- image of homomorphism
def im {G H: Type} [MyGroup G] [MyGroup H]
(φ : GroupHomomorphism G H) : Set H := { h | ∃ g : G, h = φ.f g }


-- two sets have the same cardinality iff there exists a bijection
def same_cardinality {m1 : Type} {m2 : Type}
(M1 : Set m1) (M2 : Set m2) : Prop :=
  ∃ φ : M1 -> M2, Function.Bijective φ


-- Definition 2.1.15 (difficult with cardinality)



-- we want to show, that the set of all left cosets is a group.
-- We define this structs, to make is easier

/-
structure left_coset' (G : Type) [MyGroup G] (H : Subgroup G) :=
  g : G
  carrier : Set G
  h_carrier : carrier = left_coset G H g

def left_coset_mul {G : Type} [MyGroup G] {H : normal_subgroup G}
(A B : left_coset' G H) : left_coset' G H := by {
  obtain ⟨g_a, _⟩ := A
  obtain ⟨g_b, _⟩ := B
  exact {
    g := MyGroup.mul g_a g_b,
    carrier := left_coset G H (MyGroup.mul g_a g_b),
    h_carrier := by simp
  }
}

def left_coset_one {G : Type} [MyGroup G] {H : normal_subgroup G} :
left_coset' G H := by {
  exact {
    g := MyGroup.one
    carrier := left_coset G H MyGroup.one
    h_carrier := by simp
  }
}

def left_coset_inv {G : Type} [MyGroup G] {H : normal_subgroup G}
(A : left_coset' G H) : left_coset' G H := by {
  obtain ⟨g_a, _⟩ := A
  exact {
    g := MyGroup.inv g_a
    carrier := left_coset G H (MyGroup.inv g_a)
    h_carrier := by simp
  }
}

-/



-- Definiere die Quotientengruppe als Typ
/-
def quotient_group (G : Type) [group G] (H : subgroup G) : Type :=
quotient (left_coset_setoid G H)

-- Instanz der Gruppe auf der Quotientengruppe
instance quotient_group_group (G : Type) [group G] (H : normal_subgroup G) : group (quotient_group G H) :=
{ mul := λ x y, quotient.lift_on₂' x y (λ a b, ⟦a * b⟧)
    (begin
      -- Wohldefiniertheit der Multiplikation zeigen
      intros a₁ a₂ b₁ b₂ ha hb,
      obtain ⟨h₁, h₁H, ha_eq⟩ := ha,
      obtain ⟨h₂, h₂H, hb_eq⟩ := hb,
      apply quotient.sound,
      use h₁ * h₂,
      split,
      { exact H.mul_mem h₁H h₂H },
      { rw [ha_eq, hb_eq, mul_assoc, mul_assoc, ← mul_assoc b₁, mul_assoc b₁, mul_assoc b₁, mul_assoc, mul_assoc (b₁ * h₁), ← mul_assoc] }
    end),
  one := ⟦1⟧,
  mul_assoc := begin
    intros x y z,
    apply quotient.induction_on₃' x y z,
    intros a b c,
    apply quotient.sound,
    use 1,
    split,
    { exact H.one_mem },
    { simp }
  end,
  one_mul := begin
    intro x,
    apply quotient.induction_on' x,
    intro a,
    apply quotient.sound,
    use 1,
    split,
    { exact H.one_mem },
    { simp }
  end,
  mul_one := begin
    intro x,
    apply quotient.induction_on' x,
    intro a,
    apply quotient.sound,
    use 1,
    split,
    { exact H.one_mem },
    { simp }
  end,
  inv := λ x, quotient.lift_on' x (λ a, ⟦a⁻¹⟧)
    (begin
      -- Wohldefiniertheit des Inversen zeigen
      intros a b h,
      obtain ⟨h', h'H, ha_eq⟩ := h,
      apply quotient.sound,
      use h'⁻¹,
      split,
      { exact H.inv_mem h'H },
      { rw [ha_eq, mul_inv_eq_iff_eq_mul] }
    end),
  mul_left_inv := begin
    intro x,
    apply quotient.induction_on' x,
    intro a,
    apply quotient.sound,
    use a⁻¹,
    split,
    { exact H.inv_mem H.one_mem },
    { simp }
  end }
-/
