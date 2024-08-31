import Math.Algebra.C2_Groups.C2_1_Basics.theorems

-- definition of the homomorphism in the homomorphism-theorem
def quotient_homomorphism (G : Type u) (H : Type v) [MyGroup G] [MyGroup H]
(φ : GroupHomomorphism G H) :
GroupHomomorphism (left_coset' G (ker_to_normal_subgroup φ)) H := {
  f := λ x => by {
    obtain ⟨g, _, _⟩ := x
    exact φ.f g
  }
  mul := by {
    intros a b
    simp
    rw [GroupHomomorphism.f]
    apply φ.mul
  }
}
