# Literature and priority check

- **Date of the search:** 2026-11-27. It has **not** yet been repeated for release.
- **Question:** has anyone answered Ozawa's question (5)(i) of Oberwolfach Report 22/2018, in either direction, or claimed or started work on it?
- **Verdict:** no published answer, no claim and no active work was found in any source checked. Some sources could not be completed (listed at the end). Only special cases are settled, by published inequalities, and no source states even these as answers to the question.

## The primary source

- Oberwolfach Report 22/2018, *Interactions between Operator Space Theory and Quantum Probability with Applications to Quantum Information*, workshop 6–12 May 2018, organisers U. Franz, M. Junge, G. Pisier, Q. Xu. Oberwolfach Rep. 15 (2018), no. 2, pp. 1293–1379. Section "Open Problems", pp. 1372–1374, reporter Xumin Wang; item (5), p. 1373. [doi:10.4171/OWR/2018/22](https://doi.org/10.4171/OWR/2018/22), [EMS PDF](https://ems.press/content/serial-article-files/46743).
- The PDF was downloaded and its full text extracted. The Greek letters and symbols of item (5) were checked one by one by their Unicode names. The verbatim statement is in [`PROOF.md`](PROOF.md) §1.
- There is one printed version; the TIB repository copy is the same file.
- The report gives no motivation for item (5). The list gathers items from Blecher, Collins, Gerhold, Labuschagne, Ozawa, Skalski, Winter and Skeide. Ozawa's own talk at the workshop (with Kaluba and Nowak, "Aut(F5) has property (T)") is unrelated.
- The source does not fix the logarithm base. Changing it only rescales $\delta$ and does not rescue the literal statement ([`PROOF.md`](PROOF.md) Remark 2.2 and Theorem 6.1).

## Sources searched (2026-11-27)

| Source | What was searched | Finding |
| --- | --- | --- |
| Primary source | Full text of OWR 22/2018; all 56 arXiv papers of N. Ozawa listed through the arXiv API; [arXiv:2009.00837](https://arxiv.org/abs/2009.00837) v1 and v2 read in full | Ozawa's only entropy paper is arXiv:2009.00837, which is commutative. No Ozawa paper treats the noncommutative inequality. |
| [1337isnot1337/solved-conjectures](https://github.com/1337isnot1337/solved-conjectures) | Issue and pull-request search (Ozawa, entropy variation, Jensen–Shannon, von Neumann entropy, 401593, Oberwolfach, trace distance, Holevo, CPTP, density matrix); the `research` and `audit` branch trees; `CONTENTS.md`; code search | No issue, file or result on this problem. Entropy hits concern unrelated problems. |
| [PerAlexandersson/RealRooted](https://github.com/PerAlexandersson/RealRooted) and [SymCat](https://www.symmetricfunctions.com/realRootedOpenProblems.htm) | Issue and code search; the open-problems page | Nothing relevant; the problem is outside real-rootedness. |
| [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing) | Issue, pull-request and code search (Ozawa, OWR/2018/22, 401593, entropy variation, Jensen–Shannon, quantum Jensen, Holevo, Pinsker, and more) | Nothing on Ozawa's question. **Adjacent active area:** inequalities between quantum Jensen–Shannon divergence and trace-distance quantities (pull requests #15993, #16113, #33491/#33634, #18219; last activity 2026-11-23). None is this statement. Its mdbook problem pages were covered only by code search. |
| arXiv | `abs:Ozawa AND abs:entropy`; `abs:"Jensen-Shannon" AND abs:"trace distance"`; `abs:"Jensen-Shannon" AND abs:"von Neumann algebra"`; `abs:Oberwolfach AND abs:Ozawa`; Liu [arXiv:2303.01952](https://arxiv.org/abs/2303.01952) read in the relevant sections | Nothing addresses the question. |
| Citations | OpenAlex citers of the report (1), Semantic Scholar (0), Crossref (0); OpenAlex citers of arXiv:2009.00837 (10) | The only citer of the report, Blecher–Labuschagne [arXiv:2610.06771](https://arxiv.org/abs/2610.06771), solves Blecher's item (1) of the same list (AI-assisted). It does not touch item (5). The citers of Ozawa's paper are classical Markov-chain cutoff papers. |
| Web and GitHub | Web search for the statement and for MathDB's name "entropy–variation inequality"; global GitHub issue and code search | No answer, discussion or claim. "Ozawa's entropy–variation inequality" is MathDB's own name and appears nowhere else. |
| MathOverflow, Math StackExchange, Quantum Computing StackExchange, Open Problem Garden, [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) | API and site searches; repository tree and issues | Nothing relevant. |
| [MathDB #401593](https://mathdb.com/p/401593) | The entry page | Statement matches the source verbatim. Status "open", no progress, no solutions, no comments, created 2026-08-31. Its "page 81" is the PDF page; the printed page is 1373. Part (ii) has no entry. |
| Other AI-assisted groups: hexagonmath.org, prove2.me, crabresearch.com, eulersolve.org, ndesmo/leaning, ArtificialZeng/AI-Has-Taste, JUrban/kour1, s66lem/conjectures, openai/math, Zenodo, [AlecKriebel/Math](https://github.com/AlecKriebel/Math) | Home pages, collections, repository trees, issue search, Zenodo API | No hits for this question. AlecKriebel/Math works systematically through the same catalogue's Oberwolfach problems; Ozawa's item is not in its ranked queue, but its review-hold list could not be read, so absence is not proved. |

## Not completed in that search

- UnsolvedMath (blocked by a bot checkpoint, which was not bypassed; a human should check the ids of the form `OWR-16163-*`).
- The live queue and review-hold list of AlecKriebel/Math.
- Google Scholar citers.
- The trureturing mdbook pages, read separately.
- Two smaller groups that could not be located.
- Ozawa's personal and researchmap pages.
- The full texts of Topsøe (2000) and Briët–Harremoës (arXiv:0806.4472).

None of these is likely to change the verdict. A published negative answer, or an audit of this item by AlecKriebel/Math or UnsolvedMath, would.

## Provenance of the counterexample

- The observation that the literal statement fails for the qubit pure states $\rho=\lvert0\rangle\langle0\rvert$, $\sigma=\lvert\theta\rangle\langle\theta\rvert$, with $A$ the eigenprojection of $\rho+\sigma$ for the eigenvalue $1-\cos\theta$, comes from an **unpublished external vetting report** supplied to this project on 2026-11-27. It reported ratios LHS/RHS of 1.51, 3.78 and 29.4 at $\theta=0.3$, $0.1$ and $0.01$.
- The priority check reproduced these ratios in exploratory floating point only (one implementation, not archived). They agree with the closed form of [`PROOF.md`](PROOF.md) Proposition 4.2. No result in this repository uses them.
- No public source states the negative answer, as of 2026-11-27.
- This repository adds the rational examples, complete proofs, the robustness results, two independent certificates, and the Lean formalization. None of this is claimed as new. The final credit lines need the repository owner's approval.

## Partial results that follow from published work

These special cases of the question follow from published inequalities. No source states them as answers to Ozawa's question.

| Case | Status | Source of the argument |
| --- | --- | --- |
| Commuting states, constant 8 | true | The Taylor estimate (17) of Ozawa's [arXiv:2009.00837](https://arxiv.org/abs/2009.00837), specialised to two points, plus Cauchy–Schwarz. Written out in [`PROOF.md`](PROOF.md) Lemma 7.1 and Proposition 7.2. |
| Commuting states, constant 4 | true | Topsøe, [IEEE Trans. Inform. Theory 46 (2000) 1602–1609](https://doi.org/10.1109/18.850703) (confirmed through secondary sources; the paper itself was not read). |
| $A=I$ (and multiples of $I$) | true | The quantum Pinsker inequality (Hiai–Ohya–Tsukada, [Pacific J. Math. 96 (1981) 99–109](https://doi.org/10.2140/pjm.1981.96.99)) applied to the two relative entropies with respect to the midpoint gives $\delta\ge\lVert\rho-\sigma\rVert_1^2/8$, which is more than enough. This is the priority check's two-line derivation; it is not used in this repository. |

## Comparison with related work

| Work | What it does | Relation to this repository |
| --- | --- | --- |
| Ozawa, [arXiv:2009.00837](https://arxiv.org/abs/2009.00837) (v1 2020-09-02, v2 2020-11-06) | Commutative entropy estimates for cutoff on Ramanujan graphs: a Taylor estimate for $t\log t$ (17) and a chain of inequalities (18)–(19) | The literal question (i) is the word-for-word noncommutative transcription of what (17) gives commutatively, with the same constant 8; question (ii) is a noncommutative form of (18)–(19). This is evidence for the literal reading ([`PROOF.md`](PROOF.md) Remark 7.4), not proof. |
| Topsøe (2000), [doi:10.1109/18.850703](https://doi.org/10.1109/18.850703) | Sharp commutative inequality between triangular discrimination and Jensen–Shannon divergence | Gives the commuting case with constant 4. Not used. |
| Liu, [arXiv:2303.01952](https://arxiv.org/abs/2303.01952) | Defines a quantum triangular discrimination with weight $(\rho+\sigma)^{-1/2}$ on both sides and proves a quadratic lower bound by the quantum Jensen–Shannon divergence | Different quantity. A quadratic bound does not give the linear bound that the other reading of the question would need. |
| trureturing [pull request #15993](https://github.com/the-omega-institute/trureturing/pull/15993) (merged 2026-10-12) | Refutes a conjectured inequality from Liu's paper with explicit commuting rational qubit states and a Lean proof | Different statement. Same kind of tools (explicit rational qubit example, binary entropy at a rational point, a Lean-checked scalar inequality). Our examples are not diagonal, which needs the matrix absolute value and the matrix logarithm in Lean. |
| Briët–Harremoës [arXiv:0806.4472](https://arxiv.org/abs/0806.4472); Virosztek [arXiv:1910.10447](https://arxiv.org/abs/1910.10447); Sra [arXiv:1911.02643](https://arxiv.org/abs/1911.02643) | The square root of the quantum Jensen–Shannon divergence is a metric | Background on $\delta$. The metric property gives no weighted variation bound. |
| Blecher–Labuschagne, [arXiv:2610.06771](https://arxiv.org/abs/2610.06771) | Solves item (1) of the same open-problems list (AI-assisted) | Shows that this list is being worked on. It does not touch item (5). |

## Catalogue versus source

- MathDB #401593 reproduces item (5)(i) verbatim but drops part (ii) and the context. Its status "open" is not evidence either way.
- The external vetting report gives the workshop title as "Operator spaces and quantum probability"; the actual title is the one above. Its counterexample numbers reproduce. Its remark that the reading $\lvert(\varphi-\psi)(A)\rvert$ "appears true" was not checked by the priority search, and this repository makes no claim about that reading.
