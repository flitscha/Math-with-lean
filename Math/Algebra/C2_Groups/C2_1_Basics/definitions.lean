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


#check { a : ℤ | a = 3 }

def n : ℕ := 5  -- Beispielwert für n, du kannst ihn anpassen

def nZ : Set ℤ := { x | ∃ z : ℤ, x = n*z }
-- Definiere die Menge der Vielfachen von n
