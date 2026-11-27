# How to reproduce

Everything below runs from the root of this repository. The archived runs were made on 2026-11-27 on Windows 11 with Git Bash; the scripts are plain Python and bash.

## Versions

| Tool | Version used for the archived runs |
| --- | --- |
| Python | 3.12.10 |
| python-flint (primary certificate only) | 0.7.1 (Arb ball arithmetic at 256 bits) |
| mpmath, numpy (sanity script only) | 1.3.0, 2.5.5 |
| Lean | `leanprover/lean4:v4.37.0-rc1` (file [`lean/lean-toolchain`](lean/lean-toolchain)) |
| Mathlib | commit `8ec7bd8e5f837ab7e335374928e18341c4e9f385` (file [`lean/lake-manifest.json`](lean/lake-manifest.json)) |
| LaTeX | not run: no TeX engine was installed (see the end of this file) |

## 1. The two certificates

They decide the sign of $\mathrm{LHS}^2-8\delta\mathrm{Tr}(SA^2)$ for the family at $m=1,\dots,7$, in natural logarithm and in base 2, by strict separation from 0 (14 verdicts each). They do not depend on each other.

```bash
pip install python-flint==0.7.1      # needed by the primary certificate only
python cert/OZ-1.py   > OZ-1.new.out      # primary: Arb ball arithmetic
python cert/OZ-1_x.py > OZ-1_x.new.out    # cross-check: Python standard library only
```

**Script hashes.** Each output prints the sha256 of the script that ran. The archived values are:

```
OZ-1.py    0d288d0018cd185699e7ba3cacd996614f062dce2aaf81255678d135fead5b64
OZ-1_x.py  9c06901db65be765aba0aa2c5da9260cee59669fc23d89d60a6f7e8b38461923
```

**Expected output.** Both scripts exit with code 0. The primary certificate ends with

```
PASS: OZ-1 primary certificate (Arb). Literal inequality violated for m = 4..7 (natural log)
      and m = 5..7 (base 2); not violated for m = 1..3 (natural) and m = 1..4 (base 2).
```

and the cross-check ends with

```
PASS: OZ-1 cross-check (pure Fractions). Literal inequality violated for m = 4..7 (natural log)
      and m = 5..7 (base 2); not violated for m = 1..3 (natural) and m = 1..4 (base 2).
```

The header lines (date, working directory, git commit) will differ from the archived ones. Everything else should be identical. To compare the bodies with the archived outputs:

```bash
diff <(sed -n '/^Witness family/,/^PASS/p' cert/OZ-1.out)   <(sed -n '/^Witness family/,/^PASS/p' OZ-1.new.out)
diff <(sed -n '/ln 2 enclosure/,/^PASS/p'  cert/OZ-1_x.out) <(sed -n '/ln 2 enclosure/,/^PASS/p'  OZ-1_x.new.out)
```

Both commands should print nothing. (They were checked against a second run of both scripts made on 2026-11-27: the bodies, 118 and 140 lines, were identical.)

**Runtime.** The archived runs took 27.74 s (primary) and 449.63 s (cross-check) on a machine heavily loaded by a parallel Lean build. Unloaded, the same scripts took about 1 s and 5 s.

**Archived outputs:** [`cert/OZ-1.out`](cert/OZ-1.out) and [`cert/OZ-1_x.out`](cert/OZ-1_x.out). Their first two lines and last line come from [`cert/run_cert.sh`](cert/run_cert.sh), the runner used in the original repository: it ran each script from a fresh clone and recorded the wall time. That runner expects the original repository layout (`targets/ozawa-entropy-variation/cert/`) and does not work in this repository; it is kept for the record. Use the direct commands above.

**Certified constants** (digits truncated, not rounded; each value is a truncation of the ball printed in `cert/OZ-1.out`, and agrees with the interval printed in `cert/OZ-1_x.out` to all 25 decimals that file prints):

| $m$ | LHS | $\mathrm{Tr}((\rho+\sigma)A^2)$ | $\delta$ (natural log) | (LHS/RHS)², natural log | $\delta_2$ (base 2) | (LHS/RHS)², base 2 |
| --- | --- | --- | --- | --- | --- | --- |
| 5 | 5/13 | 1/13 | 0.16302362949436594046925930… | 1.47453848334865481700577… | 0.23519338181924149141542913… | 1.02207219236025795050724… |
| 7 | 7/25 | 1/25 | 0.09803911327973198061225941… | 2.49900261032501436705753… | 0.14144054254182064515437899… | 1.73217661355872738185832… |

## 2. The sanity script (not a certificate)

```bash
pip install mpmath==1.3.0 numpy==2.5.5
python prover/check_proof.py
```

Expected: exit code 0, and the last lines

```
RESULT: all 42 checks passed.
versions: python 3.12.10 | mpmath 1.3.0 | numpy 2.5.5
```

Archived output: [`prover/out/check_proof.log`](prover/out/check_proof.log). Runtime: 52.5 s in a rerun on 2026-11-27, on a machine that was also running Lean builds.

## 3. The Lean formalization

[`lean/`](lean/) is a standalone Lake project:
- `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` are byte-identical copies from the original repository's shared Lean project;
- `Pipeline.lean` is a new root module that imports only `Pipeline.Ozawa.Main`;
- `Pipeline/Ozawa/*.lean` are byte-identical copies of the five files that passed the check.

**Steps.**

```bash
# 1. Install elan, the Lean toolchain manager: https://github.com/leanprover/elan
#    The file lean/lean-toolchain makes elan fetch leanprover/lean4:v4.37.0-rc1 automatically.
cd lean
# 2. Download the prebuilt Mathlib files for the pinned commit (needs network access).
lake exe cache get
# 3. Build the root module and the Ozawa files.
lake build
cd ..
# 4. Run the check: build, sorry/admit scan, axiom check.
bash scripts/lean_check.sh Ozawa
```

**Do not run `lake update`.** `lakefile.toml` asks for Mathlib `master`; only the manifest pins the commit `8ec7bd8e5f837ab7e335374928e18341c4e9f385`. `lake update` would move Mathlib to a newer commit, on which the files may not build. If `lake exe cache get` cannot find prebuilt files for this commit, `lake build` compiles Mathlib from source, which takes hours.

**Expected output** of step 4: `Build completed successfully` (the job count will differ from the archived 6965, which counted other projects in the original repository), an empty `sorry / admit scan`, 28 lines of the form

```
'Pipeline.Ozawa.ozawa_question_literal_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the final line

```
PASS lean_check Ozawa (Lean (version 4.37.0-rc1, x86_64-w64-windows-gnu, commit 0b77e12952ad39077d80d8bd6b66d601f225c321, Release))
```

(the platform string depends on your machine). Step 4 overwrites `lean/Pipeline/Ozawa/build.log` and `axioms.log`; the archived output of the independent rerun is [`cert/OZ-1_lean.out`](cert/OZ-1_lean.out).

**Runtime.** In the original repository, with Mathlib already built, the check took 3 min 36 s on a loaded machine. The cache download and a standalone build from scratch were not timed.

**Not yet tested in this layout.** The standalone project was assembled for this repository on 2026-11-27 but was not built here: the machine was busy with other Lean builds, and an attempt to compile the root module against the original project's build timed out after 300 s. The Lean files, the lakefile, the toolchain file and the manifest are byte-identical to those that passed; only the two-line root module is new. Building it is the first thing to do before relying on this layout.

## 4. The paper

No TeX engine (`latexmk`, `pdflatex` or `tectonic`) was installed where this was written, so no PDF is included. With a TeX distribution:

```bash
latexmk -pdf paper.tex
```

The paper uses only `amsart` and the standard packages `amssymb`, `amsthm`, `array`, `hyperref` and `booktabs`, and it is pure ASCII. Instead of a compile, it passed a static check on 2026-11-27: balanced braces, environments and math delimiters; every `\ref` and `\eqref` has a `\label`; every `\cite` has a `\bibitem` and every `\bibitem` is cited and linked; every custom macro is defined; no `$$` or `$`. What a static check cannot verify (overfull boxes, the exact page layout, hyperref warnings) has not been verified.
