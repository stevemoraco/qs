# YM cubic RG clock firewall provenance

Exact source mirror of:

- repository: `stevemoraco/RH-Lean`
- branch: `agent/ym-cubic-rg-clock-firewall-20260813-gpt56`
- repaired source commit: `b66393e50a8e24dfcc224bdab2c8ca38e90a806d`
- source path: `Millennium/YangMills/CubicRecurrenceSubleadingFirewall.lean`
- repaired source blob: `85e5ee8f8713d30d741d69b05dd1070736a74323`

The first replayed source commit `586b4825a623d59c3bf0cea9a2db158784c77aa0`
failed cleanly: division-valued `reciprocalClockProgress` needed to be
`noncomputable`, and one tactic sequence contained a redundant post-step.
Those failed declarations are preserved as failed-first evidence and are not
verification evidence.

The mirror is for independent kernel replay of the repaired finite scalar
theorem only. It does not verify Yang--Mills, RG hitting-time asymptotics,
dimensional transmutation, OS reconstruction, or the Clay theorem.
