# Critic review: batch-POLISH-Sec3 (9cf8c00)

Verdict: **REJECTED; resubmit**.

Passed: all 242 `Prop` bodies unchanged; no code outside comments changed in Sec3.lean / Sec3Proofs.lean;
88/88 `\label` citations lie inside their cited ranges.

Blocking finding (fabricated source quote):
- `Formalization/Statements/Sec3.lean:633` quotes Remark 3.5 as `"along with the continuity of D"`, and the
  new `docs/SOURCE-ISSUES.md` entry `ISSUE-3.5-OU` gives as "Printed text (verbatim, L1018-1019)":
  *"These three properties along with the continuity of $D$ uniquely determine the Ornstein-Uhlenbeck process
  which is reversible with stationary distribution equal to standard normal."*
- The source says (SteinIntro_utf8.tex:1018-1019): "These three properties determine the O-U diffusion
  process, and this process is reversible with the standard normal distribution as its stationary
  distribution." The published PDF (Probability Surveys 8 (2011), p. 228) has the same wording. Neither
  version contains "continuity of D".

Required fix: quote the printed text exactly (copy it with `sed -n '1018,1019p'`), remove every reference to a
"continuity of D" hypothesis as printed text, and keep the reading note's mathematical content (the
regularity assumption is the project's reading of "diffusion process", not a printed hypothesis).

## Resubmission batch-POLISH-Sec3b (63f4181): **ACCEPTED**

- The fabricated phrase is removed from Sec3.lean and SOURCE-ISSUES.md (`grep "continuity of D"` finds none).
- `ISSUE-3.5-OU` now quotes `SteinIntro.tex:1018-1019` verbatim (checked mechanically against the source).
- Cumulative Sec3 polish (9cf8c00 + 63f4181): all 243 `Prop` bodies unchanged, no code outside comments
  changed, 88/88 `\label` citations inside their cited ranges, no other added quotation missing from the source.
- `lake build` success (3569 jobs); axiom audit passed for 7011 declarations.
