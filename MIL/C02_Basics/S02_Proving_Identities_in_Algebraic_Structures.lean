import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]

-- Prove these:
-- (With enough planning, you can do each of them with three rewrites.)
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

-- If the hypothesis h is true (ie a + b = c + b), then b = c is true.
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  -- The hypothesis h in add_left_cancel expects three parameters: a, b and c.
  -- They correspond to (a * 0), (a * 0) and 0 respectively in the hypothesis h defined at and
  -- passed from the current theorem via implicit arguments.
  -- Note the use of implicit arguments is enabled via the use of
  -- curly brackets {a b c : R} in add_left_cancel.
  -- Contrast this with add_left_cancel_x and mul_zero_x below
  rw [add_left_cancel h]

#check add_left_cancel

-- Illustrate what it's like without the use of implicit arguments via curly brackets.
-- Note the use of (a b c : R) instead of {a b c : R}
theorem add_left_cancel_x (a b c : R) (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem mul_zero_x (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  -- Note the verbosity of the parameters we have to explicitly specified
  -- when implicit arguments are not enabled via curly brackets.
  rw [add_left_cancel_x (a * 0) (a * 0) 0 h]

#check add_left_cancel_x

-- multiplication is not assumed to be commutative, so the following theorem also requires some work.
theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    rw [← add_mul, zero_add, zero_add]
  exact add_right_cancel h

-- By now, you should also be able replace each sorry in the next exercise with a proof,
-- still using only facts about rings that we have established in this section.
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
    rw [← neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← add_neg_cancel_right a b, h, zero_add]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [add_comm, add_right_neg]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

-- In Lean, subtraction in a ring is provably equal to addition of the additive inverse.
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

-- On the real numbers, it is defined that way:
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

-- The above is an instance of what is known as a definitional equality in Lean’s underlying logic.
-- This means that not only can one rewrite with sub_eq_add_neg to replace a - b = a + -b,
-- but in some contexts, when dealing with the real numbers,
-- you can use the two sides of the equationinterchangeably.
namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_right_neg]

-- The above can be proven using rw, but if you replace the arbitrary ring R by the real numbers,
-- you can also prove it using either apply or exact.  How?

-- Lean knows that 1 + 1 = 2 holds in any ring. With a bit of effort,
-- you can use that to prove the theorem two_mul from the last section:
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing

-- We close this section by noting that some of the facts about addition and negation
-- that we established above do not need the full strength of the ring axioms,
-- or even commutativity of addition.
section
variable (A : Type*) [AddGroup A]

-- The weaker notion of a group can be axiomatized as follows:
#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)

end

-- It is conventional to use additive notation when the group operation is commutative,
-- and multiplicative notation otherwise. So Lean defines a multiplicative version as well as
-- the additive version (and also their abelian variants, AddCommGroup and CommGroup).
section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

-- If you are feeling cocky, try proving the following facts about groups, using only these axioms.
-- You will need to prove a number of helper lemmas along the way.
-- The proofs we have carried out in this section provide some hints.
namespace MyGroup

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

end MyGroup

end
