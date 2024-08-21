import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

class MyGroup (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul : ∀ a : G, mul (inv a) a = one
  mul_inv : ∀ a : G, mul a (inv a) = one


class AbelianGroup (G : Type u) extends MyGroup G where
  comm : ∀ a b : G, mul a b = mul b a


structure Subgroup (G : Type u) [MyGroup G] where
  carrier : Set G -- this is a subset of G. (the subgroup)
  nonempty : carrier ≠ ∅
  mul_mem : ∀ a b : G, (a ∈ carrier ∧ b ∈ carrier) → MyGroup.mul a b ∈ carrier
  inv_mem : ∀ {a : G}, a ∈ carrier → MyGroup.inv a ∈ carrier


-- proof, that a Subgroup is a group
def SubgroupToGroup {G : Type u} [MyGroup G] (H : Subgroup G) : MyGroup H.carrier := {
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

class GroupHomomorphism (G1 : Type u) (G2 : Type v) [MyGroup G1] [MyGroup G2] :=
  f : G1 -> G2
  mul : ∀ a b : G1, f (MyGroup.mul a b) = MyGroup.mul (f a) (f b)

structure GroupIsomorphism (G1 : Type u) (G2 : Type v) [MyGroup G1]
[MyGroup G2] extends GroupHomomorphism G1 G2 :=
  (injective : Function.Injective f)
  (surjective : Function.Surjective f)

-- proof, that a group isomorphism is a group homomorphism
def isomorphismToHomomorphism {G1 : Type u} {G2 : Type v}
[MyGroup G1] [MyGroup G2] (ψ : GroupIsomorphism G1 G2) : GroupHomomorphism G1 G2 := {
  f := ψ.f
  mul := ψ.mul
}

instance coeIsomorphismToHomomorphism {G1 : Type u} {G2 : Type v}
[MyGroup G1] [MyGroup G2] :
Coe (GroupIsomorphism G1 G2) (GroupHomomorphism G1 G2) := {
  coe := isomorphismToHomomorphism
}


/-
--def idGroupMorphism (G : Type u) [MyGroup G] : G → G := id

structure idGroupMorphism (G : Type u) [MyGroup G] extends GroupHomomorphism G G :=
  identity : f = id

def idToHomomorphism (G : Type u) [MyGroup G] : GroupHomomorphism G G := {
  f := id
  mul := by {
    intros a b
    have h : id (MyGroup.mul a b) = MyGroup.mul (id a) (id b) := by {
      simp
    }
    apply h
  }
}

/-
-- proof, that the identity morphism is a homomorphism
def idToHomomorphism {G : Type u} [MyGroup G]
(ψ : idGroupMorphism G) : GroupHomomorphism G G := {
  f := ψ.f
  mul := by {
    intros a b
    have h : ψ.f (MyGroup.mul a b) = MyGroup.mul (ψ.f a) (ψ.f b) := by {
      repeat rw [ψ.identity]
    }
    apply h
  }
}-/

instance coeIdToHomomorphism {G : Type u} [MyGroup G] :
Coe (idGroupMorphism G) (GroupHomomorphism G G) := {
  coe := by {
    intro
    exact idToHomomorphism G
  }
}
-/

-- two groups are called isomorphic, iff there exists a group-isomorphism between the two groups
def groupsAreIsomorphic (G1 : Type u) (G2 : Type v) [MyGroup G1] [MyGroup G2] : Prop :=
  ∃ _ : GroupIsomorphism G1 G2, true


-- left coset = linke Nebenklasse
def left_coset (G : Type u) [MyGroup G] (H : Subgroup G) (g : G) : Set G :=
  { x | ∃ h : H.carrier, x = MyGroup.mul g ↑h }

-- right coset = rechte Nebenklasse
def right_coset (G : Type u) [MyGroup G] (H : Subgroup G) (g : G) : Set G :=
  { x | ∃ h : H.carrier, x = MyGroup.mul ↑h g }

-- Set of all cosets
def all_left_cosets (G : Type u) [MyGroup G] (H : Subgroup G) : Set (Set G) :=
  { x | ∃ g : G, x = left_coset G H g }

def all_right_cosets (G : Type u) [MyGroup G] (H : Subgroup G) : Set (Set G) :=
  { x | ∃ g : G, x = right_coset G H g }

-- normal subgroup: gH = Hg   ∀ g ∈ G
structure normal_subgroup (G : Type u) [MyGroup G] extends Subgroup G where
  normal : ∀ g : G, left_coset G to_Subgroup g = right_coset G to_Subgorup g


-- kernel of homomorphism
def ker {G : Type u} {H : Type v} [MyGroup G] [MyGroup H]
(φ : GroupHomomorphism G H) : Set G := { g | φ.f g = MyGroup.one }

-- image of homomorphism
def im {G : Type u} {H : Type v} [MyGroup G] [MyGroup H]
(φ : GroupHomomorphism G H) : Set H := { h | ∃ g : G, h = φ.f g }
