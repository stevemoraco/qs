import Mathlib

namespace Millennium.YangMills

noncomputable def hiddenSpectrumFineTransfer (x : ℝ) : ℝ := x / 4

noncomputable def hiddenSpectrumCoarseTransfer (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 / 4, x.2 / 2)

def hiddenSpectrumEmbedding (x : ℝ) : ℝ × ℝ := (x, 0)

theorem hidden_spectrum_exact_intertwining (x : ℝ) :
    hiddenSpectrumCoarseTransfer (hiddenSpectrumEmbedding x) =
      hiddenSpectrumEmbedding (hiddenSpectrumFineTransfer x) := by
  simp [hiddenSpectrumCoarseTransfer, hiddenSpectrumEmbedding,
    hiddenSpectrumFineTransfer]

theorem hidden_coarse_mode :
    hiddenSpectrumCoarseTransfer (0, 1) = ((0 : ℝ), (1 / 2 : ℝ)) := by
  norm_num [hiddenSpectrumCoarseTransfer]

theorem hidden_coarse_factor_exceeds_fine :
    (1 / 4 : ℝ) < (1 / 2 : ℝ) := by
  norm_num

theorem hidden_mode_not_in_embedding_range :
    ¬ ∃ x : ℝ, hiddenSpectrumEmbedding x = (0, 1) := by
  rintro ⟨x, hx⟩
  have hsecond := congrArg Prod.snd hx
  norm_num [hiddenSpectrumEmbedding] at hsecond

#print axioms hidden_spectrum_exact_intertwining
#print axioms hidden_coarse_mode
#print axioms hidden_coarse_factor_exceeds_fine
#print axioms hidden_mode_not_in_embedding_range

end Millennium.YangMills
