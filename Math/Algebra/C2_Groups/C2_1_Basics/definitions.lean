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


structure AbelianGroup (G : Type u) extends MyGroup G where
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
  φ : G1 -> G2
  mul : ∀ a b : G1, φ (MyGroup.mul a b) = MyGroup.mul (φ a) (φ b)

structure GroupIsomorphism (G1 : Type u) (G2 : Type v) [MyGroup G1]
[MyGroup G2] extends GroupHomomorphism G1 G2 :=
  injective : Function.Injective φ
  surjective : Function.Surjective φ

structure idGroupMorphism (G : Type u) [MyGroup G] where
  φ : G -> G
  identity : ∀ a : G, φ a = a

-- proof, that the identity morphism is a homomorphism
def idMorphismToHomomorphism (G : Type u) [MyGroup G]
(ψ : idGroupMorphism G) : GroupHomomorphism G G := {
  φ := ψ.φ
  mul := by {
    intros a b
    have h : ψ.φ (MyGroup.mul a b) = MyGroup.mul (ψ.φ a) (ψ.φ b) := by {
      repeat rw [ψ.identity]
    }
    apply h
  }
}

-- proof, that a group isomorphism is a group homomorphism
def isomorphismToHomomorphism (G1 : Type u) (G2 : Type v)
[MyGroup G1] [MyGroup G2] (ψ : GroupIsomorphism G1 G2) : GroupHomomorphism G1 G2 := {
  φ := ψ.φ
  mul := ψ.mul
}

structure InverseGroupHomomorphism (G1 G2 : Type u) [MyGroup G1] [MyGroup G2] where
  φ : G1 → G2
  ψ : G2 → G1
  -- φ ist ein Gruppenhomomorphismus
  homomorphism : ∀ a b : G1, φ (MyGroup.mul a b) = MyGroup.mul (φ a) (φ b)
  -- ψ ist ein Gruppenhomomorphismus
  inverseHomomorphism : ∀ a b : G2, ψ (MyGroup.mul a b) = MyGroup.mul (ψ a) (ψ b)
  -- φ und ψ sind Umkehrabbildungen zueinander
  φψ : ∀ a : G1, ψ (φ a) = a
  ψφ : ∀ b : G2, φ (ψ b) = b
