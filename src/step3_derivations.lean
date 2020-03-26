import data.polynomial
       data.real.basic
       polynomial_derivations

-- set_option profiler true

section step

open polynomial

parameters Δ : polynomial ℝ → polynomial ℝ

parameter Δ1 : Δ X = C 1
parameter Δ2 : ∀ (f g : polynomial ℝ), Δ(f + g) = Δ f + Δ g
parameter Δ3 : ∀ (k : ℝ) (f : polynomial ℝ), Δ(C k * f) = C k * Δ f
parameter Δ4 : ∀ (f g : polynomial ℝ), Δ(f * g) = f * Δ g + g * Δ f
include Δ1 Δ2 Δ3 Δ4

definition d : polynomial_derivation ℝ :=
{ to_fun := Δ,
  map_add' := Δ2,
  map_C_mul' := Δ3,
  map_mul' := Δ4 }

theorem Δ_is_derivative (p : polynomial ℝ) : Δ p = derivative p := begin
  show d p = derivative p,
  apply p.induction_on,
  { intro a, simp only [polynomial_derivation.map_C, polynomial.derivative_C]},
  { intros p q hp hq, rw [derivative_add, d.map_add, hp, hq] },
  intros n a IH,
  rw [pow_succ, mul_comm X, <-mul_assoc, d.map_mul, derivative_mul,
  derivative_X, IH], unfold_coes, rw [(show d.to_fun = Δ, by refl),
  Δ1, mul_one, (show C a * X ^ n * C 1 = C a * X ^ n, by simp only [mul_one, polynomial.C_1])],
  ring,
end

end step