import Mathlib

namespace Millennium.BSD.DescentKuriharaHeegnerSqueeze

theorem exact_rank_selmer_of_matching_certificates
    {R rank selmerCorank support : ℕ}
    (hpoints : R ≤ rank)
    (hkummer : rank ≤ selmerCorank)
    (hupper : selmerCorank ≤ support)
    (hsupport : support = R) :
    rank = R ∧ selmerCorank = R := by
  omega

theorem support_below_descent_is_impossible
    {R rank selmerCorank support : ℕ}
    (hpoints : R ≤ rank)
    (hkummer : rank ≤ selmerCorank)
    (hupper : selmerCorank ≤ support)
    (hbelow : support < R) :
    False := by
  omega

theorem heegner_one_fewer_exactification
    {R rank selmerPlus ord support : ℕ}
    (hpoints : R ≤ rank)
    (hkummer : rank ≤ selmerPlus)
    (hcorA : selmerPlus = ord + 1)
    (hwitness : ord ≤ support)
    (hsupport : support + 1 = R) :
    rank = R ∧ selmerPlus = R := by
  omega

theorem depth_step_nonincreasing
    {d dNext e : ℕ}
    (hdepth : d = dNext + 2 * e) :
    dNext ≤ d := by
  omega

theorem depth_step_drop
    {d dNext e : ℕ}
    (hdepth : d = dNext + 2 * e) :
    d - dNext = 2 * e := by
  omega

theorem two_depth_steps_telescope
    {d0 d1 d2 e0 e1 : ℕ}
    (h0 : d0 = d1 + 2 * e0)
    (h1 : d1 = d2 + 2 * e1) :
    d0 = d2 + 2 * (e0 + e1) := by
  omega

#print axioms exact_rank_selmer_of_matching_certificates
#print axioms support_below_descent_is_impossible
#print axioms heegner_one_fewer_exactification
#print axioms depth_step_nonincreasing
#print axioms depth_step_drop
#print axioms two_depth_steps_telescope

end Millennium.BSD.DescentKuriharaHeegnerSqueeze
