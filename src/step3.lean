/-
2006 STEP 3 Question 8
-/

import data.polynomial
       data.real.basic
       tactic

open polynomial

/-
Δ is a function takes takes polynomials in x to polynomials in x; that is, given
any polynomial h(x), there is a polynomial called Δh(x) which is obtained from
h(x) using the rules that define Δ.
-/

variable Δ : polynomial ℝ → polynomial ℝ
include Δ

/-
These rules are as follows
-/

variable Δ1 : Δ X = C 1
variable Δ2 : ∀ (f g : polynomial ℝ), Δ(f + g) = Δ f + Δ g
variable Δ3 : ∀ (k : ℝ) (f : polynomial ℝ), Δ(C k * f) = C k * Δ f
variable Δ4 : ∀ (f g : polynomial ℝ), Δ(f * g) = f * Δ g + g * Δ f
include Δ1 Δ2 Δ3 Δ4

/-
Using these rules show that, if f(x) is a polynomial of degree zero (that is, a
constant), then Δ f(x) = 0.
-/

-- First, show that Δ 1 is 0
lemma Δ_one : Δ (C 1) = 0 := begin
-- If we can prove that Δ 1 + Δ 1 = Δ 1, then Δ 1 = 0 follows
-- Therefore we have a proof of Δ 1 = 0 if we have a proof of Δ 1 + Δ 1 = Δ 1
 suffices H : Δ 1 + Δ 1 = Δ 1,
    rwa add_left_eq_self at H,
-- Δ 1 + Δ 1 = Δ (1 * 1)
  conv begin to_rhs,
    rw (show (1 : polynomial ℝ) = 1 * 1, by ring),
  end,
-- By rule 4, this expands
  rw Δ4,
-- This then simplifies down to our desired result
  ring,
end

-- Having shown that Δ 1 is 0, Δ c (for c ∈ ℝ), is also 0
lemma Δ_const (a : ℝ) : Δ (C a) = 0 := begin
-- Δ c = Δ (c * 1)
  rw (show (C a) = (C a) * (C 1), by rw [<-C_mul,mul_one]),
-- By rule 3 we can expand this
  rw Δ3,
-- We know from above that Δ 1 is 0
  rw Δ_one Δ, simp,
-- Therefore Δ c must be 0
  repeat {assumption}
end

/-
Calculate Δx^2 and Δx^3
-/

lemma ΔXsquared : Δ (X^2) = 2*X := begin
-- Δ (x^2) = Δ (x*x)
  rw pow_two,
-- By rule 4, this is the same as X * Δ X + X * Δ X
  rw Δ4,
-- By rule 1, this is just X * 1 + X * 1
  rw Δ1,
-- Which is 2*X
  rw mul_comm,
  rw <-add_mul,
  norm_num,
end

lemma ΔXcubed : Δ (X^3) = 3*X^2 := begin
-- Δ (x^3) = Δ (x * x^2)
  rw (show (X:polynomial ℝ)^3 = X * X^2, by ring),
-- Use rule 4 to expand this
  rw Δ4,
-- Then use the result for Δx^2
  rw ΔXsquared Δ, rw <-mul_assoc, rw Δ1, rw mul_comm, rw <-mul_assoc,
  rw <-pow_two, rw <-mul_add, rw mul_comm, refl,

  repeat {assumption},
end

/-
Prove that Δh(x) ≡ dh(x)/dx for any polynomial h(x). You should make it clear
whenever you use one of the above rules in your proof.
-/

lemma ΔXn (n : ℕ) : Δ (X^(n+1)) = C (n+1)*X^n := begin
    induction n with d hd,
  { -- base case
    rw [pow_one, Δ1, nat.cast_zero],
    simp,
  },
  rw [nat.succ_eq_add_one, pow_succ, Δ4, Δ1, hd, pow_succ,
    nat.cast_add, nat.cast_one],
  rw (show C (1:ℝ) = 1, by simp),
  simp,
  ring,
end

lemma Δ_is_derivative (p : polynomial ℝ) : Δ p = derivative p :=
begin
  apply p.induction_on,
  { intro a, rw Δ_const Δ, simp, repeat {assumption}},
  { intros p q hp hq, rw Δ2, rw hp, rw hq, simp,},
  intros a n IH,
  rw [Δ4, Δ_const Δ, ΔXn Δ, mul_zero, add_zero, derivative_monomial, <-mul_assoc],
  simp,
  repeat {assumption},
end