import Math.Algebra.C2_Groups.C2_1_Basics.theorems

-- Theorem 2.2.1 (Homomorphism theorem)
def quotient_homomorphism (G : Type u) (H : Type v) [MyGroup G] [MyGroup H]
(φ : GroupHomomorphism G H) : GroupHomomorphism (left_coset' G (ker φ)) H
