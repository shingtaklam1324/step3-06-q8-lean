import tactic
       data.mv_polynomial
       data.polynomial

structure mv_polynomial_derivation (R : Type) (S : Type) [comm_ring R] :=
(to_fun : mv_polynomial S R → mv_polynomial S R) -- Delta
(map_add' : ∀ (f g : mv_polynomial S R), to_fun (f + g) = to_fun f + to_fun g)
(map_C_mul' : ∀ (k : R) (f : mv_polynomial S R), to_fun (mv_polynomial.C k * f) = mv_polynomial.C k * to_fun f)
(map_mul' : ∀ (f g : mv_polynomial S R), to_fun (f * g) = f * to_fun g + g * to_fun f)

open mv_polynomial

namespace mv_polynomial_derivation

variables {R : Type} [comm_ring R]
variables {S : Type}

instance : has_coe_to_fun (mv_polynomial_derivation R S) :=
{ F := λ _, mv_polynomial S R → mv_polynomial S R,
  coe := to_fun }

@[simp]
theorem map_add (d : mv_polynomial_derivation R S) : ∀ {f g : mv_polynomial S R}, d (f + g) = d f + d g := d.map_add'

@[simp]
theorem map_C_mul (d : mv_polynomial_derivation R S) : ∀ (k : R) (f : mv_polynomial S R), d (mv_polynomial.C k * f) = mv_polynomial.C k * d f := d.map_C_mul'

@[simp]
theorem map_mul (d : mv_polynomial_derivation R S) : ∀ (f g : mv_polynomial S R), d (f * g) = f * d g + g * d f := d.map_mul'

@[simp]
lemma map_one (d : mv_polynomial_derivation R S) : d 1 = 0 :=
begin
  have hd : d 1 + d 1 = d 1 := begin
    conv begin
      to_rhs, rw (show (1 : mv_polynomial S R) = 1 * 1, by simp)
    end,
    rw map_mul, ring,
  end,
  rwa add_left_eq_self at hd,
end

@[simp]
lemma map_C (d : mv_polynomial_derivation R S) (a : R) : d (C a) = 0 :=
by rw [(show C a = C a * (1 : mv_polynomial S R), from (mul_one _).symm),
      map_C_mul, map_one, mul_zero]

end mv_polynomial_derivation