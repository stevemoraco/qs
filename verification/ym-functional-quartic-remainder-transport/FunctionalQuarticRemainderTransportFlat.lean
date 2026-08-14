import Mathlib

namespace Millennium.YangMills

theorem quartic_remainder_transport_pointwise
    (h hinv F ph pinv pf : ℝ → ℝ)
    (u target H I R Lh Lf X4 Y4 Q : ℝ)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hLh : 0 ≤ Lh) (hLf : 0 ≤ Lf)
    (hinv_rem : |hinv u - pinv u| ≤ I * |u|^4)
    (hx4 : |hinv u|^4 ≤ X4 * |u|^4)
    (hF_rem : |F (hinv u) - pf (hinv u)| ≤ R * |hinv u|^4)
    (hpf_lip :
      |pf (hinv u) - pf (pinv u)| ≤ Lf * |hinv u - pinv u|)
    (hy4 : |F (hinv u)|^4 ≤ Y4 * |u|^4)
    (hh_rem :
      |h (F (hinv u)) - ph (F (hinv u))| ≤ H * |F (hinv u)|^4)
    (hph_lip :
      |ph (F (hinv u)) - ph (pf (pinv u))|
        ≤ Lh * |F (hinv u) - pf (pinv u)|)
    (hpoly : |ph (pf (pinv u)) - target| ≤ Q * |u|^4) :
    |h (F (hinv u)) - target|
      ≤ (H * Y4 + Lh * (R * X4 + Lf * I) + Q) * |u|^4 := by
  have hsplitF :
      F (hinv u) - pf (pinv u) =
        (F (hinv u) - pf (hinv u)) +
          (pf (hinv u) - pf (pinv u)) := by
    ring
  have hRmul :
      R * |hinv u|^4 ≤ R * (X4 * |u|^4) :=
    mul_le_mul_of_nonneg_left hx4 hR
  have hLfmul :
      Lf * |hinv u - pinv u| ≤ Lf * (I * |u|^4) :=
    mul_le_mul_of_nonneg_left hinv_rem hLf
  have hFpoly :
      |F (hinv u) - pf (pinv u)|
        ≤ (R * X4 + Lf * I) * |u|^4 := by
    rw [hsplitF]
    calc
      |(F (hinv u) - pf (hinv u)) +
          (pf (hinv u) - pf (pinv u))|
          ≤ |F (hinv u) - pf (hinv u)| +
              |pf (hinv u) - pf (pinv u)| := abs_add_le _ _
      _ ≤ R * |hinv u|^4 + Lf * |hinv u - pinv u| :=
        add_le_add hF_rem hpf_lip
      _ ≤ R * (X4 * |u|^4) + Lf * (I * |u|^4) :=
        add_le_add hRmul hLfmul
      _ = (R * X4 + Lf * I) * |u|^4 := by ring
  have hsplitH :
      h (F (hinv u)) - ph (pf (pinv u)) =
        (h (F (hinv u)) - ph (F (hinv u))) +
          (ph (F (hinv u)) - ph (pf (pinv u))) := by
    ring
  have hHmul :
      H * |F (hinv u)|^4 ≤ H * (Y4 * |u|^4) :=
    mul_le_mul_of_nonneg_left hy4 hH
  have hLhmul :
      Lh * |F (hinv u) - pf (pinv u)|
        ≤ Lh * ((R * X4 + Lf * I) * |u|^4) :=
    mul_le_mul_of_nonneg_left hFpoly hLh
  have hcomposite :
      |h (F (hinv u)) - ph (pf (pinv u))|
        ≤ (H * Y4 + Lh * (R * X4 + Lf * I)) * |u|^4 := by
    rw [hsplitH]
    calc
      |(h (F (hinv u)) - ph (F (hinv u))) +
          (ph (F (hinv u)) - ph (pf (pinv u)))|
          ≤ |h (F (hinv u)) - ph (F (hinv u))| +
              |ph (F (hinv u)) - ph (pf (pinv u))| := abs_add_le _ _
      _ ≤ H * |F (hinv u)|^4 +
            Lh * |F (hinv u) - pf (pinv u)| :=
        add_le_add hh_rem hph_lip
      _ ≤ H * (Y4 * |u|^4) +
            Lh * ((R * X4 + Lf * I) * |u|^4) :=
        add_le_add hHmul hLhmul
      _ = (H * Y4 + Lh * (R * X4 + Lf * I)) * |u|^4 := by ring
  have hsplitTarget :
      h (F (hinv u)) - target =
        (h (F (hinv u)) - ph (pf (pinv u))) +
          (ph (pf (pinv u)) - target) := by
    ring
  rw [hsplitTarget]
  calc
    |(h (F (hinv u)) - ph (pf (pinv u))) +
        (ph (pf (pinv u)) - target)|
        ≤ |h (F (hinv u)) - ph (pf (pinv u))| +
            |ph (pf (pinv u)) - target| := abs_add_le _ _
    _ ≤ (H * Y4 + Lh * (R * X4 + Lf * I)) * |u|^4 +
          Q * |u|^4 := add_le_add hcomposite hpoly
    _ = (H * Y4 + Lh * (R * X4 + Lf * I) + Q) * |u|^4 := by ring

#print axioms quartic_remainder_transport_pointwise

end Millennium.YangMills
