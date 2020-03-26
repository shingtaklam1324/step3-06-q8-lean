import tactic
       data.mv_polynomial

structure mv_polynomial_derivation (R : Type) (S : Type) [comm_ring R] :=
(to_fun : mv_polynomial S R → mv_polynomial S R) -- Delta
(map_add' : ∀ (f g : mv_polynomial S R), to_fun (f + g) = to_fun f + to_fun g)
(map_C_mul' : ∀ (k : R) (f : mv_polynomial S R), to_fun (mv_polynomial.C k * f) = mv_polynomial.C k * to_fun f)
(map_mul' : ∀ (f g : mv_polynomial S R), to_fun (f * g) = f * to_fun g + g * to_fun f)

namespace mv_polynomial_derivation

variables {R : Type} [comm_ring R]
variable {S : Type}

instance : has_coe_to_fun (mv_polynomial_derivation R S) :=
{ F := λ _, mv_polynomial S R → mv_polynomial S R,
  coe := to_fun }



end mv_polynomial_derivation