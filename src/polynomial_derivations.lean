/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import tactic
       data.polynomial
       data.real.basic

-- set_option profiler true
/-!

# Polynomial derivations

We prove the structure theorem for polynomial derivations.

# Main definitions

* `polynomial_derivation (R : Type) [comm_ring R]` : the type of `R`-derivations on `R[X]`.

# Main statements

We prove the structure theorem, that every polynomial derivation is equal to
an R[X]-linear multiple of polynomial differentiation.

Proof that there
is an equivalence between polynomials and polynomial derivations, sending
a polynomial h to the derivation mapping f to h*derivative(f).
proof that differentiation is a derivation.

# Further work


-/

-- start of file

/-- A polynomial derivation on a ring R is a function d : R[X] → R[X] satisfying
three axioms:

map_add   : ∀ {f g : polynomial R}      , d (f + g)   = d f + d g
map_C_mul : ∀ (k : R) (f : polynomial R), d (C k * f) = C k * d f
map_mul   : ∀ (f g : polynomial R)      , d (f * g)   = f * d g + g * d f
-/
structure polynomial_derivation (R : Type) [comm_ring R] :=
(to_fun : polynomial R → polynomial R) -- Delta
(map_add' : ∀ (f g : polynomial R), to_fun (f + g) = to_fun f + to_fun g)
(map_C_mul' : ∀ (k : R) (f : polynomial R), to_fun (polynomial.C k * f) = polynomial.C k * to_fun f)
(map_mul' : ∀ (f g : polynomial R), to_fun (f * g) = f * to_fun g + g * to_fun f)

open polynomial

namespace polynomial_derivation

variables {R : Type} [comm_ring R]

/-- think of a polynomial derivation as a function from R[X] to R[X] -/
instance : has_coe_to_fun (polynomial_derivation R) :=
{ F := λ _, polynomial R → polynomial R,
  coe := to_fun
}

@[simp]
theorem map_add (d : polynomial_derivation R) : ∀ {f g : polynomial R}, d (f + g) = d f + d g := d.map_add'

@[simp]
theorem map_mul (d : polynomial_derivation R): ∀ (f g : polynomial R), d (f * g) = f * d g + g * d f := d.map_mul'

@[simp]
theorem map_C_mul (d : polynomial_derivation R): ∀ (k : R) (f : polynomial R), d (C k * f) = C k * d f := d.map_C_mul'


@[simp]
lemma map_one (d : polynomial_derivation R) : d 1 = 0 :=
begin
  have hd : d 1 + d 1 = d 1 := begin
    conv begin
      to_rhs, rw (show (1 : polynomial R) = 1 * 1, by simp),
    end,
    rw map_mul, ring,
  end,
  rwa add_left_eq_self at hd,
end

@[simp]
lemma map_C (d : polynomial_derivation R) (a : R) : d (C a) = 0 :=
by rw [(show C a = C a * (1 : polynomial R), from (mul_one _).symm),
      map_C_mul, map_one, mul_zero]


lemma map_pow_succ_aux (n : ℕ)
  (d : polynomial_derivation R) :
  X * ((↑n + 1) * X ^ n * d X) + X * X ^ n * d X =
    (↑n + 1 + 1) * (X * X ^ n) * d X := by ring

-- Leibniz rule
lemma map_pow_succ (d : polynomial_derivation R) (n : ℕ) : d (X ^ (n + 1)) = (n + 1)*X^n * d(X) :=
begin
  induction n with n IH,
  {simp},
  rw pow_succ, rw map_mul,
  rw IH,
  simp only [pow_succ, nat.succ_eq_add_one],
  push_cast,
  exact map_pow_succ_aux n d,
end

lemma structure_theorem_aux' (a : R) (n : ℕ) (d : polynomial_derivation R) : C a * X ^ n * d X + X * (d X * derivative (C a * X ^ n)) =
    d X * (derivative (C a * X ^ n) * X + C a * X ^ n * 1) := by ring

/-- structure theorem for polynomial derivations -/
theorem structure_theorem (d : polynomial_derivation R) (f : polynomial R): d f = d X * polynomial.derivative f :=
begin
  apply f.induction_on,
  {intro a, simp [map_C]},
  { intros _ _ hp hq,
    rw [map_add, hp, hq, derivative_add, mul_add],},
  intros n a h,
  rw [pow_succ, mul_comm X, ←mul_assoc, map_mul, derivative_mul, h, derivative_X], 
  exact structure_theorem_aux' a n d,
end

@[ext] theorem ext : ∀ {d₁ d₂ : polynomial_derivation R} (H : ∀ f, d₁ f = d₂ f), d₁ = d₂
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ H := by congr; exact funext H

lemma structure_classification_aux1
  (j : polynomial R)
  (k : R)
  (f : polynomial R) :
  j * (0 * f + C k * derivative f) = C k * (j * derivative f) := by ring

lemma structure_classification_aux2
  (j f g : polynomial R) :
  j * (derivative f * g + f * derivative g) =
    f * (j * derivative g) + g * (j * derivative f) := by ring


noncomputable definition structure_classification (R : Type) [comm_ring R] :
  polynomial_derivation R ≃ polynomial R :=
{ to_fun := λ d, d X,
  inv_fun := λ j, 
    { to_fun := λ f, j * f.derivative,
      map_add' := λ _ _, by rw [derivative_add, mul_add],
      map_C_mul' := begin
        intros,
        rw [derivative_mul, derivative_C],
        exact structure_classification_aux1 j k f,
      end,
      map_mul' := begin
        intros,
        rw derivative_mul,
        exact structure_classification_aux2 j f g,
      end },
  left_inv := begin
    intro d,
    ext1 f,
    rw structure_theorem d f,
    refl,
  end,
  right_inv := begin
    intro p,
    change p * derivative X = p,
    simp only [mul_one, polynomial.derivative_X],
  end }

end polynomial_derivation