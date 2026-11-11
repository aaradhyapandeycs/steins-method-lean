# Pinned Mathematical Source (`arXiv:1109.1880v1`)

All source inventory entries (`docs/source-inventory.md`), definitions (`docs/DEFINITIONS.md`), source-issue records (`docs/SOURCE-ISSUES.md`), and Lean declarations in `Formalization/` are pinned to the following mathematical source:

* **Title**: *Fundamentals of Stein's method*
* **Author**: Nathan Ross
* **Journal Version**: *Probability Surveys*, Vol. 8 (2011), pp. 210–293, DOI `10.1214/11-PS182` (IMS *Probability Surveys* works are licensed under CC BY 4.0; see [`docs/AUTHOR_RULINGS.md`](AUTHOR_RULINGS.md) `R1`)
* **arXiv Identifier**: `arXiv:1109.1880v1 [math.PR]` (`https://arxiv.org/abs/1109.1880v1`, submitted 2011-09-09; `v1` is the sole arXiv version, under arXiv's perpetual non-exclusive distribution license 1.0)

Neither the raw TeX nor the normalized UTF-8 copy is tracked in git; both are fetched and SHA-256 verified locally by [`scripts/fetch_source.py`](../scripts/fetch_source.py) against [`source/provenance.json`](../source/provenance.json).

## Cryptographic File Digests

| Artifact | Origin / Local Git-Ignored Path | Lines | Bytes | SHA-256 |
| --- | --- | ---: | ---: | --- |
| arXiv source tarball | `https://arxiv.org/e-print/1109.1880v1` → `source/upstream/1109.1880v1.tar.gz` | — | 67,729 | `e22da0defd90826bfa2aecb2ddc5cff99ad67fe138f507bee74573bf4533bf55` |
| arXiv PDF | `https://arxiv.org/pdf/1109.1880v1` → `source/upstream/1109.1880v1.pdf` | — | 745,400 | `78cb3b0b439fea213c638d69d80b629123298b5e673683d2338d4b8da394115b` |
| Raw LaTeX source (ISO-8859-1, CRLF) | `source/upstream/tex/SteinIntro.tex` | 4,359 | 221,647 | `02041ab1408158cebf82f2ec67fed7722ed7594b78728ca00d644a92d67d8d95` |
| Normalized UTF-8 LF LaTeX source | `docs/source/SteinIntro_utf8.tex` | 4,359 | 217,289 | `2cb6fcad2e479c23bbd7a607f815003d33f5a07c030047088c1a582fe6a3bf4e` |
| Bibliography (`.bbl`) | `source/upstream/tex/SteinIntro.bbl` | 320 | 11,704 | `5b87ac4e7a24845fd19fa9265a45225e3e6e5d671196dcd0b118a36df72d7de2` |

Line numbers are identical between `source/upstream/tex/SteinIntro.tex` and `docs/source/SteinIntro_utf8.tex` (`4,359` lines). Citations in Lean docstrings and documentation write `SteinIntro.tex:start-end`.

## Source Line Ranges by Section

* **Preamble, Frontmatter, Abstract & Table of Contents**: `SteinIntro.tex:1-346`
* **Section 1 — Introduction (`SteinIntro.tex:347-557`)**: Berry–Esseen (`\label{thm1}`), Background and Notation, Probability Metrics (`\label{probmet}`: $d_{\mathcal{H}}$, $d_{\mathrm{K}}$, $d_{\mathrm{W}}$, $d_{\mathrm{TV}}$, Proposition 1.2 `\label{prop22}`)
* **Section 2 — Normal Approximation (`SteinIntro.tex:558-699`, `\label{stnorm}`)**: Stein's Lemma (`\label{lem1}`), CDF Stein Equation (`\label{lem2}`), Corollary 2.3 (`\label{cor1}`), General Setup (`\label{prop31}`), Solution Regularity (`\label{lem31}`)
* **Section 3 — Bounding the Error (`SteinIntro.tex:700-1815`, `\label{norm}`)**: Wasserstein Bound (`\label{thm31}`), Sums of Independent Random Variables (`\label{thm32}`, `\label{lem33}`, `\label{lem33aa}`), Dependency Neighborhoods (`\label{thm41}`), Exchangeable Pairs & $a$-Stein Pairs (`\label{prop51}`, `\label{thm51}`, `\label{lem51}`, `\label{thm52}`), Size-Bias Coupling (`\label{sbc}`), Zero-Bias Coupling (`\label{thm81}`, `\label{thm82}`, `\label{thm83}`), Kolmogorov Metric Bounds (`\label{thm91}`, `\label{lem91}`, `\label{cor91}`, `\label{thm92}`, `\label{lem92}`)
* **Section 4 — Poisson Approximation (`SteinIntro.tex:1816-2711`, `\label{poi}`)**: Chen–Stein Characterization (`\label{lem101}`, `\label{lem102}`, `\label{cor101}`, `\label{lem103}`, `\label{thm101}`), Law of Small Numbers (`\label{thm102}`), Dependency Neighborhoods (`\label{thm103}`), Size-Bias Coupling, Exchangeable Pairs
* **Section 5 — Exponential Approximation (`SteinIntro.tex:2712-3189`, `\label{exp}`)**: Stein Operator, Equilibrium Coupling, Geometric Sums, Critical Branching Processes
* **Section 6 — Geometric Approximation (`SteinIntro.tex:3190-3388`, `\label{geo}`)**: Discrete Stein Operator, Discrete Equilibrium Coupling, Uniform Attachment
* **Section 7 — Concentration Inequalities (`SteinIntro.tex:3389-3887`, `\label{con}`)**: Exchangeable-Pair Concentration (`\label{thm211a}`, Hoeffding CLT, Curie–Weiss `\label{thm211b}`), Size-Bias Concentration (`\label{thm211c}`)
* **Commented-Out Draft Region (`SteinIntro.tex:3888-4347`)**: Commented out with `%` in Ross's e-print (`% \section{Local Limit Theorems}`); contains zero active TeX lines.
* **Acknowledgments & End of Document (`SteinIntro.tex:4348-4359`)**: Active `\subsubsection*{Acknowledgments}`, `\bibliographystyle{plain}`, `\bibliography{SteinIntro}`, and `\end{document}`.
