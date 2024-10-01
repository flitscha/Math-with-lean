import Math.Algebra.C2_Groups.C2_1_Basics.quotient_group

-- to define the generated subgroups, we use lists of Members of G
-- such a list, is representing the product of all elements in the list

-- a list is actually the product of all elements in the list
def list_prod {G : Type} [MyGroup G] : List G -> G
| [] => MyGroup.one
| x :: xs => MyGroup.mul x (list_prod xs)


-- product of merged list
theorem list_prod_of_merged_list {G : Type} [MyGroup G] (l1 : List G) (l2 : List G) :
list_prod (l1 ++ l2) = MyGroup.mul (list_prod l1) (list_prod l2) := by {
  cases l1
  case nil =>
    simp
    rw [list_prod]
    rw [MyGroup.one_mul]
  case cons x xs =>
    simp [list_prod]
    rw [list_prod_of_merged_list]
    rw [MyGroup.mul_assoc]
}


-- inverting a list: reverse order, and inverse elements
def list_inv {G : Type} [MyGroup G] : List G -> List G
| [] => []
| x :: xs => list_inv xs ++ [(MyGroup.inv x)]


theorem list_inv_eq_inv {G : Type} [MyGroup G] (l : List G) :
list_prod (list_inv l) = MyGroup.inv (list_prod l) := by {
  cases l
  case nil =>
    simp [list_inv, list_prod]
    rw [inv_one_lemma]
  case cons x xs =>
    simp [list_inv, list_prod]
    rw [list_prod_of_merged_list]
    rw [list_inv_eq_inv]
    simp [list_prod]
    rw [mul_inv_lemma]
    rw [MyGroup.mul_one]
}


theorem list_inv_of_merged_list {G : Type} [MyGroup G] (l1 : List G) (l2 : List G) :
list_inv (l1 ++ l2) = (list_inv l2) ++ (list_inv l1) := by {
  cases l1
  case nil =>
    simp [list_inv]
  case cons x xs =>
    simp [list_inv]
    rw [list_inv_of_merged_list]
    simp
}


theorem list_inv_inv {G : Type} [MyGroup G] (l : List G) :
list_inv (list_inv l) = l := by {
  cases l
  case nil =>
    simp [list_inv]
  case cons x xs =>
    simp [list_inv]
    rw [list_inv_of_merged_list]
    simp [list_inv]
    constructor
    rw [double_inv_lemma]
    apply list_inv_inv
}


-- if g is in the list l, then g⁻¹ is in the list l⁻¹
theorem list_inv_mem {G : Type} [MyGroup G] (l : List G) (g : G) :
g ∈ l -> MyGroup.inv g ∈ (list_inv l) := by {
  intro h
  cases l
  case nil =>
    simp at h
  case cons x xs =>
    simp [list_inv]
    simp at h
    cases h
    case inl h =>
      right
      rw [h]
    case inr h =>
      left
      apply list_inv_mem
      exact h
}
