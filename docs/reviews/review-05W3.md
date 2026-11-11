# Critic review 05W3: W2-1 and W2-2 fixes, `f395dee`

- **Critic:** Claude, 2026-11-11.

**ACCEPTED.** The site is release-ready, pending the owner's go-ahead (ruling R3).

| Check | Result |
|---|---|
| `python3 site/build.py --rev HEAD` | exit 0 |
| `python3 site/check_fidelity.py` | `FIDELITY OK` |
| `python3 scripts/export_public.py --preview <scratch>` | 0 lint findings |
| Independent export scan (private paths, product names, tokens, UUIDs) | clean |
| **W2-1:** headline | "65 of 122 numbered results formalized (47 proved, 5 defined, 9 corrected, 4 restricted; 11 with a machine-checked refutation); 57 open". This matches COVERAGE (65/122). |
| **W2-1:** definitions | Definitions 3.1, 3.2, 3.7, 3.10 and 6.1 show **defined**. Definition 3.10 keeps an *also corrected* marker. Definitions 4.9, 5.1 and 5.2 are open (their tracks have not landed). |
| **W2-2:** README | now reads "depends on no axioms other than …" |
