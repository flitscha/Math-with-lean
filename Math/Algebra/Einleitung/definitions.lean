import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- definition: point in ℝ²
structure point := (x : ℝ) (y : ℝ)

-- definition: distance between 2 points
noncomputable def distance_between_points (p1 p2 : point) : ℝ :=
  Real.sqrt ((p1.x - p2.x)^2 + (p1.y - p2.y)^2)

-- definition of line through 2 points
def line_through (p1 p2 : point) : Set point :=
  { p | ∃ t : ℝ, p.x = p1.x + t * (p2.x - p1.x) ∧ p.y = p1.y + t * (p2.y - p1.y) }

-- definition: circle with center and radius
def circle (center : point) (radius : ℝ) : Set point :=
  { p | (p.x - center.x)^2 + (p.y - center.y)^2 = radius^2 }

-- definition: x is the only intersection of the two lines
def x_is_the_only_intersection (p1 p2 q1 q2 x : point) : Prop :=
  x ∈ (line_through p1 p2) ∧ x ∈ (line_through q1 q2) ∧
  ∀ p : point, (p ∈ line_through p1 p2 ∧ p ∈ line_through q1 q2) → p = x

-- definition: point is type1-construcable with points in the set M
def point_is_type1_constructable (M : Set point) (x : point) : Prop :=
  ∃ (p1 p2 q1 q2 : point),
  p1 ∈ M ∧ p2 ∈ M ∧ q1 ∈ M ∧ q2 ∈ M ∧
  p1 ≠ p2 ∧ q1 ≠ q2 ∧
  x_is_the_only_intersection p1 p2 q1 q2 x

-- definition: point is type2-constructable
def point_is_type2_constructable (M : Set point) (x : point) : Prop :=
  ∃ (p1 p2 q q1 q2 : point),
  p1 ∈ M ∧ p2 ∈ M ∧ q ∈ M ∧ q1 ∈ M ∧ q2 ∈ M ∧
  p1 ≠ p2 ∧
  x ∈ (line_through p1 p2) ∧ x ∈ (circle q (distance_between_points q1 q2))

-- definition: point is type3-constructable
def point_is_type3_constructable (M : Set point) (x : point) : Prop :=
  ∃ (p p1 p2 q q1 q2 : point),
  p ∈ M ∧ p1 ∈ M ∧ p2 ∈ M ∧ q ∈ M ∧ q1 ∈ M ∧ q2 ∈ M ∧
  p ≠ q ∧
  x ∈ (circle p (distance_between_points p1 p2)) ∧
  x ∈ (circle q (distance_between_points q1 q2))

-- definition: set of all points, that are type_i-constructable
def type1_constructable (M : Set point) : Set point :=
  { x | point_is_type1_constructable M x}

def type2_constructable (M : Set point) : Set point :=
  { x | point_is_type2_constructable M x}

def type3_constructable (M : Set point) : Set point :=
  { x | point_is_type3_constructable M x}

-- definition: set of all points, that are constructable in one step (all 3 types)
def constructable_points (M : Set point) : Set point :=
  (type1_constructable M) ∪ (type2_constructable M) ∪ (type3_constructable M)

-- definition: M^(i) the set of the points, that are constructable in i steps
def constructable_in_steps (M : Set point) (i : Nat) : Set point :=
  match i with
  | 0 => M
  | Nat.succ j =>
    (constructable_in_steps M j) ∪ constructable_points (constructable_in_steps M j)
--def constructable_in_steps (M : Set point) : Nat → Set point
--| 0 => M
--| Nat.succ i => constructable_points ((constructable_in_steps M) i)

-- definition: Kon(M) are all the points, that are constructable in finite many staps
def Kon (M : Set point) : Set point :=
  { p | ∃ i : Nat, p ∈ constructable_in_steps M i }


----------------------------------------------------------
---------------- Complex definitions ---------------------
----------------------------------------------------------
--def point_c := ℂ

-- definition: ℚ to ℂ
def Q_as_C : Set ℂ := {z : ℂ | ∃ q : ℚ, ↑q = z }

-- definition: complex conjugation
def conj (z : ℂ) : ℂ :=
  z.re - z.im * Complex.I

-- definition: distance between 2 points
noncomputable def distance_between_points_c (p1 p2 : ℂ) : ℝ :=
  Real.sqrt ((p1.re - p2.re)^2 + (p1.im - p2.im)^2)

-- definition of line through 2 points
def line_through_c (p1 p2 : ℂ) : Set ℂ :=
  { z : ℂ | ∃ t : ℝ, z = p1 + t * (p2 - p1) }

-- definition: circle with center and radius
def circle_c (center : ℂ) (radius : ℝ) : Set ℂ :=
  { p | (p.re - center.re)^2 + (p.im - center.im)^2 = radius^2 }

-- definition: x is the only intersection of the two lines
def x_is_the_only_intersection_c (p1 p2 q1 q2 x : ℂ) : Prop :=
  x ∈ (line_through_c p1 p2) ∧ x ∈ (line_through_c q1 q2) ∧
  ∀ z : ℂ, (z ∈ line_through_c p1 p2 ∧ z ∈ line_through_c q1 q2) → z = x

-- definition: point is type1-construcable with points in the set M
def point_is_type1_constructable_c (M : Set ℂ) (x : ℂ) : Prop :=
  ∃ (p1 p2 q1 q2 : ℂ),
  p1 ∈ M ∧ p2 ∈ M ∧ q1 ∈ M ∧ q2 ∈ M ∧
  p1 ≠ p2 ∧ q1 ≠ q2 ∧
  x_is_the_only_intersection_c p1 p2 q1 q2 x

-- definition: point is type2-constructable
def point_is_type2_constructable_c (M : Set ℂ) (x : ℂ) : Prop :=
  ∃ (p1 p2 q q1 q2 : ℂ),
  p1 ∈ M ∧ p2 ∈ M ∧ q ∈ M ∧ q1 ∈ M ∧ q2 ∈ M ∧
  p1 ≠ p2 ∧
  x ∈ (line_through_c p1 p2) ∧ x ∈ (circle_c q (distance_between_points_c q1 q2))

-- definition: point is type3-constructable
def point_is_type3_constructable_c (M : Set ℂ) (x : ℂ) : Prop :=
  ∃ (p p1 p2 q q1 q2 : ℂ),
  p ∈ M ∧ p1 ∈ M ∧ p2 ∈ M ∧ q ∈ M ∧ q1 ∈ M ∧ q2 ∈ M ∧
  p ≠ q ∧
  x ∈ (circle_c p (distance_between_points_c p1 p2)) ∧
  x ∈ (circle_c q (distance_between_points_c q1 q2))

-- definition: set of all points, that are type_i-constructable
def type1_constructable_c (M : Set ℂ) : Set ℂ :=
  { x | point_is_type1_constructable_c M x}

def type2_constructable_c (M : Set ℂ) : Set ℂ :=
  { x | point_is_type2_constructable_c M x}

def type3_constructable_c (M : Set ℂ) : Set ℂ :=
  { x | point_is_type3_constructable_c M x}

-- definition: set of all points, that are constructable in one step (all 3 types)
def constructable_points_c (M : Set ℂ) : Set ℂ :=
  (type1_constructable_c M) ∪ (type2_constructable_c M) ∪ (type3_constructable_c M)

-- definition: M^(i) the set of the points, that are constructable in i steps
def constructable_in_steps_c (M : Set ℂ) (i : Nat) : Set ℂ :=
  match i with
  | 0 => M
  | Nat.succ j =>
    (constructable_in_steps_c M j) ∪ constructable_points_c (constructable_in_steps_c M j)

-- definition: Kon(M) are all the points, that are constructable in finite many staps
def Kon_c (M : Set ℂ) : Set ℂ :=
  { p | ∃ i : Nat, p ∈ constructable_in_steps_c M i }
