# Ozawa's entropy–variation question, read literally, has a negative answer: full proof

*Written 2026-11-27. This file is self-contained: every definition is given and every step is proved here. It uses the same numbering as [`paper.tex`](paper.tex). The question is due to Narutaka Ozawa. No priority or novelty is claimed.*

## Status words

Every step below carries one of these words.

| Word | Meaning here |
| --- | --- |
| `proposed` | A complete hand argument is written below, but it has not yet passed independent review. |
| `certified` | Decided by rigorous computation in two independent implementations that agree, with archived output ([`cert/`](cert/), Section 8 below). |
| `formalized` | Checked by the Lean 4 proof assistant with the Mathlib library: the build passes, there is no `sorry`, and only the standard axioms are used ([`LEAN.md`](LEAN.md)). |
| `numerical` | Floating-point or finite evidence. No argument uses it. |
| `heuristic` | Plausible, with evidence, but not proved. |

**No step of the main theorem depends on a computation.** Every inequality has a hand proof in this file. The certificates confirm the explicit examples independently, and they are the only source of the decimal digits quoted. The Lean formalization is a third, independent check of the main theorem.

**Review status.** The hand proofs have not yet been through the project's independent AI review. **Expert verification required.** Verified so far with Lean 4 + Mathlib (the main theorem, checked twice), two independent exact computer certificates (Arb interval arithmetic and pure rational arithmetic), and AI referees (Claude models; review in progress)

## Contents

1. The question
2. Notation and the literal reading (Lemma 2.1)
3. Three lemmas (Lemmas 3.1–3.3)
4. A family of pure qubit states (Lemma 4.1, Proposition 4.2)
5. Explicit counterexamples (Lemma 5.1, Theorem 5.2, Remarks 5.3–5.4)
6. The failure cannot be repaired by the constant or by the dependence on δ (Theorems 6.1–6.2, Proposition 6.3, Corollaries 6.4–6.5)
7. Commuting states (Lemma 7.1, Proposition 7.2, Remarks 7.3–7.4)
8. Computer verification
9. Formal verification
10. Summary table

## 1. The question

Source: Oberwolfach Report 22/2018, *Interactions between Operator Space Theory and Quantum Probability with Applications to Quantum Information* (workshop 6–12 May 2018; Oberwolfach Rep. 15 (2018), no. 2), section "Open Problems", item (5), p. 1373, [doi:10.4171/OWR/2018/22](https://doi.org/10.4171/OWR/2018/22). The text was extracted from the published PDF on 2026-11-27, and the Greek letters and symbols were checked one by one.

> (5) Narutaka Ozawa:
> (i) Let $H(\varphi)$ denote the von Neumann entropy of $\varphi$ and
>
> ```math
> \delta(\varphi,\psi)=H\bigl((\varphi+\psi)/2\bigr)-\bigl(H(\varphi)+H(\psi)\bigr)/2 .
> ```
>
> Is it true that $\lvert\varphi-\psi\rvert(A)\le\bigl(8\delta(\varphi,\psi)(\varphi+\psi)(A^2)\bigr)^{1/2}$ for every $A\ge 0$?

The item has a second part (ii), about quantum channels. This file concerns part (i) only. The source fixes no further convention.

## 2. Notation and the literal reading

**Matrices.** $M_d=M_d(\mathbb{C})$ is the algebra of complex $d\times d$ matrices, $d\ge1$. $I$ is the identity matrix and $\mathrm{Tr}$ the trace. $X^\dagger$ is the conjugate transpose. A matrix $X$ is *hermitian* if $X^\dagger=X$. For hermitian $X$, we write $X\ge0$ (*positive semidefinite*) if $\langle\xi,X\xi\rangle\ge0$ for every vector $\xi$, and $X>0$ (*positive definite*) if moreover $X$ is invertible. $\lVert X\rVert$ is the operator norm. An *orthogonal projection* is a hermitian $P$ with $P^2=P$.

**States.** A *density matrix* is a $\rho\in M_d$ with $\rho\ge0$ and $\mathrm{Tr}\rho=1$. A *state* on $M_d$ is a linear functional of the form $\varphi(X)=\mathrm{Tr}(\rho X)$ with $\rho$ a density matrix. Throughout, $\varphi$ and $\psi$ are states with density matrices $\rho$ and $\sigma$, and

```math
D=\rho-\sigma,\qquad S=\rho+\sigma,\qquad \omega=\tfrac12(\rho+\sigma).
```

So $(\varphi+\psi)(A^2)=\mathrm{Tr}(SA^2)$. A state is *pure* if its density matrix is a rank-one orthogonal projection. It is *faithful* if its density matrix is positive definite.

**Entropy.** Put $\eta(\lambda)=-\lambda\ln\lambda$ for $\lambda>0$ and $\eta(0)=0$. For a density matrix $\tau$ with eigenvalues $\lambda_1,\dots,\lambda_d$ (repeated according to multiplicity), the *von Neumann entropy* is $H(\tau)=\sum_j\eta(\lambda_j)$. This is $-\mathrm{Tr}(\tau\ln\tau)$ with the convention $0\ln0=0$. The logarithm is natural unless stated otherwise. The source does not fix the base. In base 2 the entropy is $H/\ln2$, and $\delta$ becomes $\delta_2=\delta/\ln2$. The main theorem is proved for both bases.

**Ozawa's quantity.** $\delta(\rho,\sigma)=H(\omega)-\tfrac12\bigl(H(\rho)+H(\sigma)\bigr)$. It is known as the quantum Jensen–Shannon divergence of $\rho$ and $\sigma$.

**Binary entropy.** $h(x)=-x\ln x-(1-x)\ln(1-x)$ for $0\lt x\lt 1$, and $h(0)=h(1)=0$.

**Vectors.** Vectors are columns. For $a,b\in\mathbb{R}^2$, $ab^{T}$ is the $2\times2$ matrix with entries $a_ib_j$, and $\langle a,b\rangle=a^{T}b$.

### 2.1 Absolute values

Let $D\in M_d$ be hermitian, with spectral decomposition $D=\sum_j\lambda_jP_j$: the $\lambda_j$ are the distinct real eigenvalues, and the $P_j\ne0$ are orthogonal projections with $P_jP_k=0$ for $j\ne k$ and $\sum_jP_j=I$. Define

```math
D_+=\sum_{\lambda_j>0}\lambda_jP_j,\qquad D_-=-\sum_{\lambda_j<0}\lambda_jP_j,\qquad |D|=D_++D_-=\sum_j|\lambda_j|P_j .
```

Then $D_\pm\ge0$, $D=D_+-D_-$, $\lvert D\rvert\ge0$ and $\lvert D\rvert^2=D^2$. So $\lvert D\rvert$ is the positive semidefinite square root of $D^2$.

In operator algebras, the *absolute value* $\lvert\omega\rvert$ of a hermitian functional $\omega$ is $\omega_++\omega_-$. Here $\omega=\omega_+-\omega_-$ is the *Jordan decomposition*: the unique way to write $\omega$ as a difference of positive functionals with $\lVert\omega\rVert=\lVert\omega_+\rVert+\lVert\omega_-\rVert$. (A functional is *positive* if it is nonnegative on positive semidefinite matrices.) Lemma 2.1 proves, for $M_d$, the only fact we need.

**Lemma 2.1** (`proposed`). Let $D\in M_d$ be hermitian and $\omega(X)=\mathrm{Tr}(DX)$, with norm $\lVert\omega\rVert=\sup\lbrace\lvert\omega(X)\rvert:\lVert X\rVert\le1\rbrace$.
1. $\lVert\omega\rVert=\mathrm{Tr}\lvert D\rvert$.
2. The functionals $\omega_\pm=\mathrm{Tr}(D_\pm\ \cdot\ )$ are positive, $\omega=\omega_+-\omega_-$, and $\lVert\omega_+\rVert+\lVert\omega_-\rVert=\lVert\omega\rVert$.
3. Conversely, if $\omega=\omega_1-\omega_2$ with positive functionals $\omega_1,\omega_2$ and $\lVert\omega_1\rVert+\lVert\omega_2\rVert=\lVert\omega\rVert$, then $\omega_1=\omega_+$ and $\omega_2=\omega_-$. Hence $\omega_1+\omega_2=\mathrm{Tr}(\lvert D\rvert\ \cdot\ )$.

*Plan.* We compute the norm, then show that any norm-additive decomposition must put all of $D_+$ on one side and all of $D_-$ on the other.

*Proof.* (a) For $B\ge0$ and any $X$: $\lvert\mathrm{Tr}(BX)\rvert\le\lVert X\rVert\mathrm{Tr}B$. Indeed, for an orthonormal basis $(e_k)$, $\mathrm{Tr}(BX)=\mathrm{Tr}(B^{1/2}XB^{1/2})=\sum_k\langle B^{1/2}e_k,XB^{1/2}e_k\rangle$. Each term is at most $\lVert X\rVert\lVert B^{1/2}e_k\rVert^2$ in absolute value, and $\sum_k\lVert B^{1/2}e_k\rVert^2=\mathrm{Tr}B$.

(b) Part 1. By (a), $\lvert\omega(X)\rvert\le\lvert\mathrm{Tr}(D_+X)\rvert+\lvert\mathrm{Tr}(D_-X)\rvert\le\lVert X\rVert(\mathrm{Tr}D_++\mathrm{Tr}D_-)=\lVert X\rVert\mathrm{Tr}\lvert D\rvert$. Let $P=\sum_{\lambda_j>0}P_j$. Then $PD=DP=D_+$ and $(I-P)D=-D_-$. The matrix $X_0=2P-I$ is hermitian with $X_0^2=I$, so $\lVert X_0\rVert=1$. And $\omega(X_0)=\mathrm{Tr}(PD)-\mathrm{Tr}((I-P)D)=\mathrm{Tr}D_++\mathrm{Tr}D_-$. So the supremum equals $\mathrm{Tr}\lvert D\rvert$.

(c) Every linear functional on $M_d$ is $X\mapsto\mathrm{Tr}(BX)$ for a unique $B\in M_d$. (The bilinear form $(B,X)\mapsto\mathrm{Tr}(BX)$ is nondegenerate, since $\mathrm{Tr}(BB^\dagger)>0$ for $B\ne0$, and $M_d$ is finite-dimensional.) If the functional is positive, then $\langle\xi,B\xi\rangle=\mathrm{Tr}(B\xi\xi^\dagger)\ge0$ for every vector $\xi\in\mathbb{C}^d$. This forces $B$ to be hermitian, so $B\ge0$, and its norm is $\mathrm{Tr}B$ by Part 1 applied to $B$. Conversely, for $B\ge0$ the functional $\mathrm{Tr}(B\ \cdot\ )$ is positive, since $\mathrm{Tr}(BX)=\mathrm{Tr}(X^{1/2}BX^{1/2})\ge0$ for $X\ge0$.

(d) Part 2. By (c), $\omega_\pm$ are positive with norms $\mathrm{Tr}D_\pm$. Also $\omega=\omega_+-\omega_-$ because $D=D_+-D_-$, and $\mathrm{Tr}D_++\mathrm{Tr}D_-=\mathrm{Tr}\lvert D\rvert=\lVert\omega\rVert$ by Part 1.

(e) Part 3. By (c), $\omega_i=\mathrm{Tr}(B_i\ \cdot\ )$ with $B_i\ge0$, $B_1-B_2=D$ and $\mathrm{Tr}B_1+\mathrm{Tr}B_2=\mathrm{Tr}D_++\mathrm{Tr}D_-$. For $B\ge0$ and an orthogonal projection $Q$, $\mathrm{Tr}(QB)=\mathrm{Tr}(QBQ)\ge0$. With $P$ as in (b),

```math
\mathrm{Tr}D_+=\mathrm{Tr}(PD)=\mathrm{Tr}(PB_1)-\mathrm{Tr}(PB_2)\le\mathrm{Tr}(PB_1)\le\mathrm{Tr}B_1,
```

```math
\mathrm{Tr}D_-=-\mathrm{Tr}((I-P)D)=\mathrm{Tr}((I-P)B_2)-\mathrm{Tr}((I-P)B_1)\le\mathrm{Tr}((I-P)B_2)\le\mathrm{Tr}B_2 .
```

Adding gives $\mathrm{Tr}D_++\mathrm{Tr}D_-\le\mathrm{Tr}B_1+\mathrm{Tr}B_2$, which is an equality by hypothesis. So every inequality above is an equality. In particular $\mathrm{Tr}(PB_2P)=0$ and $\mathrm{Tr}((I-P)B_1(I-P))=0$. A positive semidefinite matrix with trace 0 is 0, so $PB_2P=0$. That is, $(B_2^{1/2}P)^\dagger(B_2^{1/2}P)=0$, hence $B_2P=0=PB_2$. In the same way $B_1(I-P)=0=(I-P)B_1$, so $B_1=PB_1P$. Therefore $D_+=PDP=PB_1P-PB_2P=B_1$, and $B_2=B_1-D=D_+-D=D_-$. ∎

So the absolute value of the functional $\varphi-\psi$ is $X\mapsto\mathrm{Tr}(\lvert\rho-\sigma\rvert X)$, and the literal meaning of the printed formula is

```math
|\varphi-\psi|(A)=\mathrm{Tr}\bigl(|\rho-\sigma|A\bigr).
```

### 2.2 The literal inequality

With these conventions, Ozawa's inequality (i) reads

```math
\textbf{(L)}\qquad \mathrm{Tr}\bigl(|\rho-\sigma|A\bigr)\le\Bigl(8\,\delta(\rho,\sigma)\,\mathrm{Tr}\bigl((\rho+\sigma)A^2\bigr)\Bigr)^{1/2}\qquad\text{for every }A\ge0 .
```

We call the two sides LHS and RHS. For $A\ge0$ the left side is nonnegative, since $\mathrm{Tr}(\lvert D\rvert A)=\mathrm{Tr}(A^{1/2}\lvert D\rvert A^{1/2})\ge0$. The right side is a real number when $\delta\ge0$. (This always holds, by concavity of $H$, but we never need the general fact: below, $\delta$ is either computed explicitly and positive, or assumed to be at least $1/4$, or the inequality is used in squared form.) So, when $\delta(\rho,\sigma)\ge0$, **(L)** fails for $(\rho,\sigma,A)$ exactly when

```math
\mathrm{Tr}\bigl(|\rho-\sigma|A\bigr)^2>8\,\delta(\rho,\sigma)\,\mathrm{Tr}\bigl((\rho+\sigma)A^2\bigr).
```

**Remark 2.2** (log base). Changing the base of the logarithm multiplies $\delta$ by a positive constant. So it is the same as changing the constant 8. Theorem 6.1 shows that no constant works. The explicit counterexamples of Theorem 5.2 are checked in both natural logarithm and base 2.

## 3. Three lemmas

**Lemma 3.1** (`proposed`). Let $D\in M_d$ be hermitian and $s\ge0$. If $D^2=s^2I$, then $\lvert D\rvert=sI$.

*Proof.* In the spectral decomposition $D=\sum_j\lambda_jP_j$ we have $D^2P_j=\lambda_j^2P_j$, and also $D^2P_j=s^2P_j$. Since $P_j\ne0$, $\lambda_j^2=s^2$, so $\lvert\lambda_j\rvert=s$ for every $j$. Hence $\lvert D\rvert=\sum_j\lvert\lambda_j\rvert P_j=s\sum_jP_j=sI$. ∎

**Lemma 3.2** (`proposed`). (a) If $P\in M_d$ is a rank-one orthogonal projection, then $P$ is a density matrix and $H(P)=0$. (b) If $P\in M_2$ is a rank-one orthogonal projection and $0\le x\le1$, then $\tau=(1-x)(I-P)+xP$ is a density matrix with eigenvalues $x$ and $1-x$, and $H(\tau)=h(x)$.

*Proof.* (a) The eigenvalues of $P$ are $1$ (once) and $0$ ($d-1$ times), and $\eta(1)=\eta(0)=0$. (b) In $M_2$ the projection $I-P$ also has rank one. Take unit vectors $f$ in the range of $P$ and $f'$ in the range of $I-P$. They are orthogonal, $\tau f=xf$ and $\tau f'=(1-x)f'$. So $\tau$ is hermitian with eigenvalues $x,1-x\ge0$, whose sum is 1, and $H(\tau)=\eta(x)+\eta(1-x)=h(x)$. ∎

**Lemma 3.3** (scalar facts; `proposed`).
- (a) $e^{s}\ge1+s$ for all real $s$, with equality only at $s=0$. Hence $\ln t\le t-1$ for $t>0$, with equality only at $t=1$, and $\ln(1+w)\lt w$ for $w>0$.
- (b) $e>2$. Hence $\ln2\lt 1$.
- (c) $\ln2>2/3$.
- (d) $\ln y\le2\sqrt y-2$ for $y>0$.
- (e) For $0\lt x\lt 1$: $h(x)>0$ and $h(x)\lt x\bigl(1+\ln(1/x)\bigr)$. The function $h$ is continuous and strictly increasing on $(0,1/2]$, $h(1/2)=\ln2$, and $h(x)\to0$ as $x\to0^+$. So $h$ maps $(0,1/2]$ bijectively onto $(0,\ln2]$.

*Proof.* (a) Let $g(s)=e^s-1-s$. Then $g(0)=0$, and $g'(s)=e^s-1$ is negative for $s\lt 0$ and positive for $s>0$. So $g(s)>0$ for $s\ne0$. With $s=\ln t$ this is $t\ge1+\ln t$, with equality only at $t=1$. With $t=1+w$ and $w>0$ it gives $\ln(1+w)\lt w$.

(b) $e=\sum_{k\ge0}1/k!>1+1=2$, and $\ln$ is strictly increasing, so $\ln2\lt\ln e=1$.

(c) For $t>0$,

```math
\frac1t-\Bigl(\frac23-\frac49\Bigl(t-\frac32\Bigr)\Bigr)=\frac{4t^2-12t+9}{9t}=\frac{(2t-3)^2}{9t}\ge0,
```

with equality only at $t=3/2$. Integrate over $[1,2]$, where $\int_1^2(t-\frac32)\mathrm{d}t=0$. This gives $\ln2=\int_1^2\frac{\mathrm{d}t}{t}>\frac23$.

(d) Apply (a) with $t=\sqrt y$: $\frac12\ln y\le\sqrt y-1$.

(e) For $0\lt x\lt 1$ both terms $x\ln(1/x)$ and $(1-x)\ln(1/(1-x))$ of $h(x)$ are positive. By (a) with $w=x/(1-x)$, $(1-x)\ln\frac{1}{1-x}=(1-x)\ln\bigl(1+\frac{x}{1-x}\bigr)\lt x$. So $h(x)\lt x\ln(1/x)+x$. By (d) with $y=1/x$, $\ln(1/x)\lt 2/\sqrt x$, so $h(x)\lt 2\sqrt x+x\to0$ as $x\to0^+$. Next, $h'(x)=\ln\frac{1-x}{x}>0$ for $0\lt x\lt 1/2$, so $h$ is strictly increasing on $(0,1/2]$. It is continuous there, and $h(1/2)=\ln2$. By the intermediate value theorem every value in $(0,\ln2]$ is attained exactly once on $(0,1/2]$. ∎

## 4. A family of pure qubit states

For a real number $m>0$ put $N=m^2$ and

```math
\rho=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
\sigma_m=vv^{T},\quad v=\Bigl(\frac{N-1}{N+1},\frac{2m}{N+1}\Bigr),\qquad
A_m=\frac{1}{N+1}\begin{pmatrix}1&-m\\-m&N\end{pmatrix}=\frac{1}{N+1}uu^{T},\quad u=(1,-m).
```

Write $D_m=\rho-\sigma_m$ and $S_m=\rho+\sigma_m$. Geometrically: if $\theta\in(0,\pi)$ is the angle with $\cos\theta=(N-1)/(N+1)$ and $\sin\theta=2m/(N+1)$ (that is, $m=\cot(\theta/2)$), then $\sigma_m$ is the projection onto the unit vector $(\cos\theta,\sin\theta)$, and $1/(N+1)=\sin^2(\theta/2)$. For integer $m$ the entries are rational. The two cases used below are

```math
m=5:\quad \sigma_5=\frac{1}{169}\begin{pmatrix}144&60\\60&25\end{pmatrix},\ v=\Bigl(\frac{12}{13},\frac{5}{13}\Bigr),\qquad A_5=\frac{1}{26}\begin{pmatrix}1&-5\\-5&25\end{pmatrix},\ u=(1,-5);
```

```math
m=7:\quad \sigma_7=\frac{1}{625}\begin{pmatrix}576&168\\168&49\end{pmatrix},\ v=\Bigl(\frac{24}{25},\frac{7}{25}\Bigr),\qquad A_7=\frac{1}{50}\begin{pmatrix}1&-7\\-7&49\end{pmatrix},\ u=(1,-7).
```

**Lemma 4.1** (structure of the family; `proposed`). Let $m>0$ be real, $N=m^2$, $e_1=(1,0)$, $u=(1,-m)$ and $u'=(m,1)$. Put $f_1=u'/\sqrt{N+1}$, $f_2=u/\sqrt{N+1}$, $A'=f_1f_1^{T}$ and $E=f_1f_2^{T}+f_2f_1^{T}$.
1. $(f_1,f_2)$ is an orthonormal basis of $\mathbb{R}^2$, hence of $\mathbb{C}^2$. $A_m=f_2f_2^{T}$ and $A'$ are rank-one orthogonal projections with $A_m+A'=I$ and $A_mA'=A'A_m=0$. In particular $A_m\ge0$, $A_m^2=A_m$ and $\mathrm{Tr}A_m=1$.
2. $e_1=(mf_1+f_2)/\sqrt{N+1}$ and $v=(mf_1-f_2)/\sqrt{N+1}$. In particular $v$ is a unit vector, so $\sigma_m=vv^{T}$ is a rank-one orthogonal projection, and so is $\rho=e_1e_1^{T}$.
3. $\rho=\dfrac{NA'+mE+A_m}{N+1}$ and $\sigma_m=\dfrac{NA'-mE+A_m}{N+1}$. Hence

```math
D_m=\frac{2m}{N+1}E,\qquad S_m=\frac{2N}{N+1}A'+\frac{2}{N+1}A_m .
```

4. $E^2=I$. Hence $D_m^2=\bigl(\frac{2m}{N+1}\bigr)^2I$.

*Plan.* Everything follows by writing $\rho$ and $\sigma_m$ in the orthonormal basis $(f_1,f_2)$.

*Proof.* 1. $\langle u,u'\rangle=m-m=0$ and $\lvert u\rvert^2=1+m^2=N+1=\lvert u'\rvert^2$, so $f_1,f_2$ are orthonormal. For a real unit vector $f$, the matrix $ff^{T}$ is real symmetric, $(ff^{T})^2=f(f^{T}f)f^{T}=ff^{T}$, its range is spanned by $f$, and its trace is $\lvert f\rvert^2=1$. So $A'$ and $f_2f_2^{T}$ are rank-one orthogonal projections. Also $f_2f_2^{T}=uu^{T}/(N+1)$, which is $A_m$ (the entries of $uu^{T}$ are $1,-m,-m,m^2$). The matrix $f_1f_1^{T}+f_2f_2^{T}$ fixes $f_1$ and $f_2$, so it is $I$. Finally $f_2f_2^{T}f_1f_1^{T}=f_2(f_2^{T}f_1)f_1^{T}=0$, and likewise in the other order.

2. $mu'+u=(m^2+1,\ m-m)=(N+1)e_1$ and $mu'-u=(m^2-1,\ 2m)=(N+1)v$. Divide by $N+1$ and use $u'=\sqrt{N+1}f_1$ and $u=\sqrt{N+1}f_2$. By orthonormality $\lvert v\rvert^2=(m^2+1)/(N+1)=1$.

3. By 2, $\rho=e_1e_1^{T}=\frac{1}{N+1}(mf_1+f_2)(mf_1+f_2)^{T}=\frac{1}{N+1}\bigl(m^2f_1f_1^{T}+m(f_1f_2^{T}+f_2f_1^{T})+f_2f_2^{T}\bigr)$. The same computation with $-f_2$ in place of $f_2$ gives $\sigma_m$. Subtracting and adding gives $D_m$ and $S_m$.

4. $E^2=f_1(f_2^{T}f_1)f_2^{T}+f_1(f_2^{T}f_2)f_1^{T}+f_2(f_1^{T}f_1)f_2^{T}+f_2(f_1^{T}f_2)f_1^{T}=f_1f_1^{T}+f_2f_2^{T}=I$. ∎

**Proposition 4.2** (closed form; `proposed`). For every real $m>0$: $\rho$ and $\sigma_m$ are density matrices of pure states, $A_m$ is a rank-one orthogonal projection, $\lvert D_m\rvert=\frac{2m}{N+1}I$, and

```math
\mathrm{Tr}(|D_m|A_m)=\frac{2m}{N+1},\qquad \mathrm{Tr}(S_mA_m^2)=\frac{2}{N+1},\qquad \delta(\rho,\sigma_m)=h\Bigl(\frac{1}{N+1}\Bigr),
```

```math
\frac{\mathrm{Tr}(|D_m|A_m)^2}{8\,\delta(\rho,\sigma_m)\,\mathrm{Tr}(S_mA_m^2)}=\frac{N}{4\bigl((N+1)\ln(N+1)-N\ln N\bigr)}=\frac{1-x}{4h(x)},\qquad x=\frac{1}{N+1}.
```

*Plan.* Lemma 4.1 diagonalises everything in the basis $(f_1,f_2)$. Lemmas 3.1 and 3.2 then give the absolute value and the entropies.

*Proof.* Let $s=2m/(N+1)>0$ and $x=1/(N+1)\in(0,1)$.
- By Lemma 4.1(2), $\rho$ and $\sigma_m$ are rank-one orthogonal projections, so they are density matrices of pure states (Lemma 3.2(a)). By Lemma 4.1(1), $A_m$ is a rank-one orthogonal projection.
- By Lemma 4.1(4) and Lemma 3.1, $\lvert D_m\rvert=sI$. So $\mathrm{Tr}(\lvert D_m\rvert A_m)=s\mathrm{Tr}A_m=s$.
- By Lemma 4.1(3) and (1), $S_mA_m=\frac{2}{N+1}A_m$. So $\mathrm{Tr}(S_mA_m^2)=\mathrm{Tr}(S_mA_m)=\frac{2}{N+1}=2x$.
- By Lemma 4.1(3) and $A'=I-A_m$, $\omega=\frac12S_m=(1-x)(I-A_m)+xA_m$. By Lemma 3.2(b), $H(\omega)=h(x)$. By Lemma 3.2(a), $H(\rho)=H(\sigma_m)=0$. So $\delta(\rho,\sigma_m)=h(x)$.
- Therefore, using $s^2=4Nx^2$ and $Nx=1-x$,

```math
\frac{\mathrm{Tr}(|D_m|A_m)^2}{8\,\delta\,\mathrm{Tr}(S_mA_m^2)}=\frac{4Nx^2}{16\,x\,h(x)}=\frac{Nx}{4h(x)}=\frac{1-x}{4h(x)},
\qquad (N+1)h(x)=\ln(N+1)+N\ln\frac{N+1}{N}=(N+1)\ln(N+1)-N\ln N. \qquad\blacksquare
```

*Smallest case, $m=1$.* Then $\sigma_1=\mathrm{diag}(0,1)$ commutes with $\rho$, $D_1=\mathrm{diag}(1,-1)$, $\lvert D_1\rvert=I$, $S_1=I$ and $A_1=\frac12\begin{pmatrix}1&-1\\-1&1\end{pmatrix}$. Directly: LHS $=\mathrm{Tr}A_1=1$, $\mathrm{Tr}(S_1A_1^2)=1$, $\delta=H(I/2)=\ln2$. These agree with $2m/(N+1)=1$, $2/(N+1)=1$ and $h(1/2)=\ln2$. The quotient is $1/(8\ln2)\lt 1$, so there is no violation at $m=1$, as Proposition 7.2 requires for commuting states.

## 5. Explicit counterexamples

By Proposition 4.2, for $m=5$ we have $x=1/26$, LHS $=5/13$ and $\mathrm{Tr}(S_5A_5^2)=1/13$. So **(L)** fails if and only if $(5/13)^2>8\delta\cdot\frac{1}{13}$, that is, $\delta\lt 25/104$. For $m=7$ we have $x=1/50$, LHS $=7/25$ and $\mathrm{Tr}(S_7A_7^2)=1/25$, and **(L)** fails if and only if $\delta\lt 49/200$. The next lemma proves these four scalar inequalities.

**Lemma 5.1** (`proposed`; all four `formalized` and `certified`).
1. $h(1/26)\lt 25/104$.
2. $h(1/26)/\ln2\lt 25/104$.
3. $h(1/50)\lt 49/200$.
4. $h(1/50)/\ln2\lt 49/200$.

*Plan.* All four use $h(1/n)\lt(1+\ln n)/n$, which is Lemma 3.3(e) at $x=1/n$, together with a power of 2 just above $n$.

*Proof.* 1. By definition $h(1/26)=\frac{1}{26}\ln26+\frac{25}{26}\ln\frac{26}{25}$. By Lemma 3.3(a), $\ln\frac{26}{25}=\ln\bigl(1+\frac{1}{25}\bigr)\lt\frac{1}{25}$. So

```math
h\Bigl(\frac{1}{26}\Bigr)<\frac{1+\ln26}{26},\qquad\text{and}\qquad \frac{1+\ln26}{26}<\frac{25}{104}\iff\ln26<\frac{21}{4}.
```

Now $26\lt 32=2^5$, so $\ln26\lt 5\ln2\lt 5\lt\frac{21}{4}$ by Lemma 3.3(b).

3. $50\lt 64=2^6$, so $\ln50\lt 6\ln2\lt 6$ (Lemma 3.3(b)). Hence $h(1/50)\lt\frac{1+6}{50}=\frac{28}{200}\lt\frac{49}{200}$.

4. $\frac{h(1/50)}{\ln2}\lt\frac{1}{50}\bigl(\frac{1}{\ln2}+\frac{\ln50}{\ln2}\bigr)\lt\frac{1}{50}\bigl(\frac32+6\bigr)=\frac{30}{200}\lt\frac{49}{200}$. This uses $1/\ln2\lt 3/2$ (Lemma 3.3(c)) and $\ln50\lt 6\ln2$.

2. $26=2^5\cdot\frac{13}{16}$ and $\ln\frac{13}{16}\le\frac{13}{16}-1=-\frac{3}{16}$ (Lemma 3.3(a)). So $\ln26\le5\ln2-\frac{3}{16}$. Hence

```math
\frac{h(1/26)}{\ln2}<\frac{1}{26}\Bigl(\frac{1}{\ln2}+5-\frac{3}{16\ln2}\Bigr)=\frac{1}{26}\Bigl(5+\frac{13}{16}\cdot\frac{1}{\ln2}\Bigr)<\frac{1}{26}\Bigl(5+\frac{13}{16}\cdot\frac32\Bigr)=\frac{199}{832}<\frac{200}{832}=\frac{25}{104}. \qquad\blacksquare
```

**Theorem 5.2** (negative answer to the literal question; `proposed` by hand; the strict violation is `certified`; the statement with every quantity defined from the matrices is `formalized`). For $m=5$ and for $m=7$: $\rho$ and $\sigma_m$ are density matrices of pure states on $M_2(\mathbb{C})$, $A_m\ge0$, and **(L)** fails strictly for $(\rho,\sigma_m,A_m)$, with the entropy in natural logarithm and also in base 2. Exactly:
- $m=5$: LHS $=5/13$, $\mathrm{Tr}(S_5A_5^2)=1/13$, $\delta=h(1/26)$, and $8\cdot h(1/26)\cdot\frac{1}{13}\lt\bigl(\frac{5}{13}\bigr)^2$ and $8\cdot\frac{h(1/26)}{\ln 2}\cdot\frac{1}{13}\lt\bigl(\frac{5}{13}\bigr)^2$;
- $m=7$: LHS $=7/25$, $\mathrm{Tr}(S_7A_7^2)=1/25$, $\delta=h(1/50)$, and $8\cdot h(1/50)\cdot\frac{1}{25}\lt\bigl(\frac{7}{25}\bigr)^2$ and $8\cdot\frac{h(1/50)}{\ln 2}\cdot\frac{1}{25}\lt\bigl(\frac{7}{25}\bigr)^2$.

In particular, the answer to Ozawa's question (5)(i), read literally, is **no**.

*Proof.* The values of LHS, $\mathrm{Tr}(S_mA_m^2)$ and $\delta$ are Proposition 4.2 at $m=5$ ($N=25$) and $m=7$ ($N=49$). The four strict inequalities are Lemma 5.1, multiplied by the positive numbers $8/13$ and $8/25$. Since $\delta>0$ (Lemma 3.3(e)) and $\mathrm{Tr}(S_mA_m^2)>0$, the right side of **(L)** is a positive real number, and the squared inequality gives LHS $>$ RHS. ∎

**Remark 5.3** (direct check of the case $m=5$, without Lemma 4.1; `proposed`).
- $v=(12/13,5/13)$ has $\lvert v\rvert^2=(144+25)/169=1$. So $\sigma_5=vv^{T}$ is a rank-one orthogonal projection, like $\rho$.
- $u=(1,-5)$ has $\lvert u\rvert^2=26$. So $A_5=\frac{1}{26}uu^{T}$ is the orthogonal projection onto the line spanned by $u$.
- $D=\rho-\sigma_5=\frac{1}{169}\begin{pmatrix}25&-60\\-60&-25\end{pmatrix}$. Its square is $\frac{25^2+60^2}{169^2}I=\frac{4225}{169^2}I=\frac{25}{169}I$, because the off-diagonal entries are $25\cdot(-60)+(-60)\cdot(-25)=0$ and $4225=25\cdot169$. By Lemma 3.1, $\lvert D\rvert=\frac{5}{13}I$, so LHS $=\frac{5}{13}\mathrm{Tr}A_5=\frac{5}{13}$.
- $S=\rho+\sigma_5=\frac{1}{169}\begin{pmatrix}313&60\\60&25\end{pmatrix}$. With $u'=(5,1)$:

```math
Su=\frac{1}{169}\begin{pmatrix}313-300\\60-125\end{pmatrix}=\frac{1}{169}\begin{pmatrix}13\\-65\end{pmatrix}=\frac{1}{13}u,\qquad
Su'=\frac{1}{169}\begin{pmatrix}1565+60\\300+25\end{pmatrix}=\frac{325}{169}\begin{pmatrix}5\\1\end{pmatrix}=\frac{25}{13}u'.
```

- Hence $SA_5=\frac{1}{13}A_5$ and $\mathrm{Tr}(SA_5^2)=\mathrm{Tr}(SA_5)=\frac{1}{13}$. Also $\omega=S/2=\frac{25}{26}(I-A_5)+\frac{1}{26}A_5$, so $\delta=h(1/26)$ by Lemma 3.2.

The same check for $m=7$: $\lvert v\rvert^2=(576+49)/625=1$; $D^2=\frac{49^2+168^2}{625^2}I=\frac{30625}{625^2}I=\frac{49}{625}I$ (off-diagonal entries $49\cdot(-168)+(-168)\cdot(-49)=0$, and $30625=49\cdot625$); $S=\frac{1}{625}\begin{pmatrix}1201&168\\168&49\end{pmatrix}$, $Su=\frac{1}{25}u$ and $Su'=\frac{49}{25}u'$ with $u'=(7,1)$. So LHS $=\frac{7}{25}$, $\mathrm{Tr}(SA_7^2)=\frac{1}{25}$ and $\delta=h(1/50)$.

**Remark 5.4** (where the family starts to violate; `proposed` for the monotonicity, `certified` for the signs). By Proposition 4.2 the squared quotient is $(1-x)/(4h(x))$ with $x=1/(N+1)$. On $(0,1/2]$ the numerator is positive and strictly decreasing in $x$, and $h$ is positive and strictly increasing (Lemma 3.3(e)). So the quotient is strictly decreasing in $x$, hence strictly increasing in $m$ on $[1,\infty)$. The certificates of Section 8 decide the sign at $m=3$ and $m=4$ (natural logarithm) and at $m=4$ and $m=5$ (base 2). Together: among real $m\ge1$, the triple $(\rho,\sigma_m,A_m)$ violates **(L)** exactly for $m>m_\ast$, with a threshold $m_\ast\in(3,4)$ for the natural logarithm and $m_\ast\in(4,5)$ for base 2. So the first violating integer is $m=4$ (natural logarithm) and $m=5$ (base 2). This remark is not used anywhere else.

## 6. The failure cannot be repaired by the constant or by the dependence on δ

**Theorem 6.1** (no constant works; `proposed`). For every real $m\ge1$,

```math
\mathrm{Tr}(|D_m|A_m)^2>\frac{m}{\sqrt2}\ \delta(\rho,\sigma_m)\,\mathrm{Tr}(S_mA_m^2).
```

So, for every $C>0$, the inequality **(L)** with $C$ in place of 8 fails for $(\rho,\sigma_m,A_m)$ whenever $m\ge\max(1,\sqrt2 C)$, and LHS/RHS $>(m/(8\sqrt2))^{1/2}\to\infty$. With the logarithm to a base $b>1$ (so that $\delta_b=\delta/\ln b$), the same holds for $m\ge\max(1,\sqrt2 C/\ln b)$.

*Plan.* Proposition 4.2 gives the quotient exactly. We bound the entropy from above with Lemma 3.3(e) and (d).

*Proof.* Let $m\ge1$, so $N\ge1$, and $x=1/(N+1)$. By Proposition 4.2,

```math
\frac{\mathrm{Tr}(|D_m|A_m)^2}{\delta(\rho,\sigma_m)\,\mathrm{Tr}(S_mA_m^2)}=\frac{4Nx^2}{2x\,h(x)}=\frac{2N}{(N+1)h(x)} .
```

By Lemma 3.3(e), $(N+1)h(x)\lt(N+1)x\bigl(1+\ln(1/x)\bigr)=1+\ln(N+1)$. By Lemma 3.3(d), $1+\ln(N+1)\le2\sqrt{N+1}-1\lt 2\sqrt{N+1}$. And $N+1\le2N$. Hence

```math
\frac{2N}{(N+1)h(x)}>\frac{2N}{1+\ln(N+1)}>\frac{N}{\sqrt{N+1}}\ge\frac{N}{\sqrt{2N}}=\frac{m}{\sqrt2}.
```

Since $\delta>0$ and $\mathrm{Tr}(S_mA_m^2)>0$, this is the displayed inequality. If $m\ge\max(1,\sqrt2 C)$ then $m/\sqrt2\ge C$, so $\mathrm{Tr}(\lvert D_m\rvert A_m)^2>C\delta\mathrm{Tr}(S_mA_m^2)$. With $C=8$ this says (LHS/RHS)² $>m/(8\sqrt2)$. For base $b$, $\delta_b=\delta/\ln b$, so the quotient with $\delta_b$ exceeds $m\ln b/\sqrt2$, which is at least $C$ when $m\ge\sqrt2 C/\ln b$. ∎

For $C=8$ this bound guarantees a violation from $m=12$ on ($11^2\lt 128\le12^2$). It is cruder than, and consistent with, the certified first violation at $m=4$ (Remark 5.4).

**Theorem 6.2** (no function of δ works; `proposed`). For every real $m>0$ the matrix $B_m=S_m^{-1}$ exists, is positive definite, and

```math
\mathrm{Tr}(|D_m|B_m)^2=2\,\mathrm{Tr}(S_mB_m^2).
```

Moreover $\lbrace\delta(\rho,\sigma_m):m\ge1\rbrace=(0,\ln2]$. Consequently, for every $t_0\in(0,\ln2]$ and every real $c\lt 2$, there are pure states $\varphi,\psi$ on $M_2(\mathbb{C})$ with $\delta(\varphi,\psi)=t_0$ and a matrix $A>0$ with $\lvert\varphi-\psi\rvert(A)^2>c(\varphi+\psi)(A^2)$. In particular, if $F:(0,\ln2]\to\mathbb{R}$ is any function with $F(t_0)\lt 2$ for some $t_0$, then the inequality $\lvert\varphi-\psi\rvert(A)^2\le F(\delta(\varphi,\psi))(\varphi+\psi)(A^2)$ fails for some pure qubit states and some $A>0$. This covers $F(t)=Ct^{\alpha}$ for all $C>0$ and $\alpha>0$, and $F(t)=8t$ at every $t_0\lt 1/4$.

*Plan.* On the same family we change the test matrix to $A=S^{-1}$. The quotient then becomes exactly 2, independently of $m$, while $\delta$ sweeps out all of $(0,\ln2]$.

*Proof.* By Lemma 4.1(3), $S_m=\frac{2N}{N+1}A'+\frac{2}{N+1}A_m$, where $A',A_m$ are orthogonal projections with $A'A_m=A_mA'=0$ and $A'+A_m=I$. Put

```math
B_m=\frac{N+1}{2N}A'+\frac{N+1}{2}A_m .
```

Then $S_mB_m=A'+A_m=I$, so $B_m=S_m^{-1}$. Its eigenvalues $\frac{N+1}{2N}$ and $\frac{N+1}{2}$ are positive, so $B_m>0$, and $\mathrm{Tr}B_m=\frac{N+1}{2N}+\frac{N+1}{2}=\frac{(N+1)^2}{2N}$. By Proposition 4.2, $\lvert D_m\rvert=sI$ with $s=2m/(N+1)$. Also $S_mB_m^2=B_m$. So

```math
\frac{\mathrm{Tr}(|D_m|B_m)^2}{\mathrm{Tr}(S_mB_m^2)}=\frac{s^2(\mathrm{Tr}B_m)^2}{\mathrm{Tr}B_m}=s^2\,\mathrm{Tr}B_m=\frac{4N}{(N+1)^2}\cdot\frac{(N+1)^2}{2N}=2 .
```

*Range of $\delta$.* By Proposition 4.2, $\delta(\rho,\sigma_m)=h(1/(m^2+1))$. The map $m\mapsto1/(m^2+1)$ is continuous and strictly decreasing on $[1,\infty)$, equals $1/2$ at $m=1$, and tends to $0$. So it maps $[1,\infty)$ onto $(0,1/2]$. By Lemma 3.3(e), the set of values of $\delta(\rho,\sigma_m)$ for $m\ge1$ is $(0,\ln2]$.

*Consequences.* Let $t_0\in(0,\ln2]$ and $c\lt 2$. Choose $m\ge1$ with $\delta(\rho,\sigma_m)=t_0$. Then $\mathrm{Tr}(\lvert D_m\rvert B_m)^2=2\mathrm{Tr}(S_mB_m^2)>c\mathrm{Tr}(S_mB_m^2)$, because $\mathrm{Tr}(S_mB_m^2)=\mathrm{Tr}B_m>0$. If $F(t_0)\lt 2$, take $c=F(t_0)$. For $F(t)=Ct^\alpha$ take any $t_0\in(0,\ln2]$ with $t_0\le C^{-1/\alpha}$, so that $F(t_0)\le1$. For $F(t)=8t$ take any $t_0\lt 1/4$; note $1/4\lt 2/3\lt\ln2$ by Lemma 3.3(c). ∎

*Smallest case, $m=1$:* $B_1=I$, $\lvert D_1\rvert=I$, and $(\mathrm{Tr}I)^2=4=2\mathrm{Tr}I$.

**Proposition 6.3** (the quotient is at most 2; `proposed`). For all $d\ge1$, all density matrices $\rho,\sigma\in M_d$ and all hermitian $A\in M_d$:

```math
\bigl|\mathrm{Tr}(|\rho-\sigma|A)\bigr|\le\sqrt{\mathrm{Tr}(\rho A^2)}+\sqrt{\mathrm{Tr}(\sigma A^2)},\qquad\text{hence}\qquad \mathrm{Tr}(|\rho-\sigma|A)^2\le2\,\mathrm{Tr}\bigl((\rho+\sigma)A^2\bigr).
```

So the constant 2 in Theorem 6.2 cannot be improved.

*Plan.* Write $\lvert D\rvert=UD$ with a hermitian unitary $U$, split $D=\rho-\sigma$, and apply the Cauchy–Schwarz inequality to each state separately.

*Proof.* Let $D=\rho-\sigma=\sum_j\lambda_jP_j$ and $P=\sum_{\lambda_j\ge0}P_j$. The matrix $U=2P-I$ is hermitian with $U^2=I$, and $UP_j=P_j$ if $\lambda_j\ge0$, $UP_j=-P_j$ if $\lambda_j\lt 0$. Hence $UD=\sum_j\lvert\lambda_j\rvert P_j=\lvert D\rvert$, and

```math
\mathrm{Tr}(|D|A)=\mathrm{Tr}(U\rho A)-\mathrm{Tr}(U\sigma A).
```

Let $\tau$ be a density matrix. Use the Hilbert–Schmidt inner product $\langle X,Y\rangle=\mathrm{Tr}(X^\dagger Y)$ and note $(\tau^{1/2}U)^\dagger=U\tau^{1/2}$. The Cauchy–Schwarz inequality gives

```math
|\mathrm{Tr}(U\tau A)|=\bigl|\langle\tau^{1/2}U,\ \tau^{1/2}A\rangle\bigr|\le\bigl(\mathrm{Tr}(U\tau U)\bigr)^{1/2}\bigl(\mathrm{Tr}(A\tau A)\bigr)^{1/2}=\bigl(\mathrm{Tr}(\tau A^2)\bigr)^{1/2},
```

because $\mathrm{Tr}(U\tau U)=\mathrm{Tr}(\tau U^2)=\mathrm{Tr}\tau=1$ and $\mathrm{Tr}(A\tau A)=\mathrm{Tr}(\tau A^2)$. Applying this to $\tau=\rho$ and $\tau=\sigma$ gives the first inequality. The inequality $(a+b)^2\le2(a^2+b^2)$ gives the second. ∎

**Corollary 6.4** (the exact threshold; `proposed`). (i) **(L)** holds for every pair of states with $\delta(\rho,\sigma)\ge1/4$, in every dimension. (ii) For every $t\in(0,1/4)$ there are pure states on $M_2(\mathbb{C})$ with $\delta=t$, and a matrix $A>0$, for which **(L)** fails. Both statements also hold in base 2, with $\delta_2$ in place of $\delta$.

*Proof.* (i) Let $A\ge0$. By Proposition 6.3, $\mathrm{Tr}(\lvert D\rvert A)^2\le2\mathrm{Tr}(SA^2)\le8\delta\mathrm{Tr}(SA^2)$ when $\delta\ge1/4$. Take square roots; both sides of **(L)** are nonnegative. (ii) Let $t\in(0,1/4)$. By Theorem 6.2 there is $m\ge1$ with $\delta(\rho,\sigma_m)=t$, and $\mathrm{Tr}(\lvert D_m\rvert B_m)^2=2\mathrm{Tr}(S_mB_m^2)>8t\mathrm{Tr}(S_mB_m^2)$, since $8t\lt 2$ and $\mathrm{Tr}(S_mB_m^2)>0$. So **(L)** fails for $(\rho,\sigma_m,B_m)$, and $B_m>0$. For base 2, repeat both arguments with $\delta_2=\delta/\ln2$, whose values on the family fill $(0,1]$, which contains $(0,1/4)$. ∎

So, for the literal reading, the constant 8 and the factor $\delta$ matter only through the comparison of $8\delta$ with the number 2.

**Corollary 6.5** (variants; `proposed`). (a) *Faithful states.* Let $\varepsilon=1/1000$, $\rho_\varepsilon=(1-\varepsilon)\rho+\frac{\varepsilon}{2}I$ and $\sigma_\varepsilon=(1-\varepsilon)\sigma_7+\frac{\varepsilon}{2}I$. These are positive definite density matrices, and **(L)** fails strictly for $(\rho_\varepsilon,\sigma_\varepsilon,A_7)$, in natural logarithm and in base 2. (b) *All dimensions.* For every $d\ge2$ there are states on $M_d(\mathbb{C})$ and a matrix $A\ge0$ for which **(L)** fails.

*Proof.* (a) Let $x=1/50$, $s=7/25$ and $A=A_7$. Recall from Lemma 4.1 and Proposition 4.2 for $m=7$: $D_7^2=s^2I$, $S_7A=\frac{1}{25}A$ and $\omega=(1-x)(I-A)+xA$.
- For a rank-one orthogonal projection $P\in M_2$: $(1-\varepsilon)P+\frac{\varepsilon}{2}I=(1-\frac{\varepsilon}{2})P+\frac{\varepsilon}{2}(I-P)$. By Lemma 3.2(b) (with $1-\frac{\varepsilon}{2}$ in place of $x$), this is a density matrix with eigenvalues $\frac{1999}{2000}$ and $\frac{1}{2000}$, both positive, and with entropy $h(\frac{1}{2000})$. So $\rho_\varepsilon,\sigma_\varepsilon$ are positive definite density matrices and $H(\rho_\varepsilon)=H(\sigma_\varepsilon)=h(\frac{1}{2000})$.
- $\rho_\varepsilon-\sigma_\varepsilon=(1-\varepsilon)D_7$, whose square is $((1-\varepsilon)s)^2I$. By Lemma 3.1, $\lvert\rho_\varepsilon-\sigma_\varepsilon\rvert=(1-\varepsilon)sI=\frac{6993}{25000}I$, so LHS $=\frac{6993}{25000}$.
- $\rho_\varepsilon+\sigma_\varepsilon=(1-\varepsilon)S_7+\varepsilon I$, so $(\rho_\varepsilon+\sigma_\varepsilon)A=\bigl(\frac{999}{1000}\cdot\frac{1}{25}+\frac{1}{1000}\bigr)A=\frac{128}{3125}A$ and $\mathrm{Tr}((\rho_\varepsilon+\sigma_\varepsilon)A^2)=\frac{128}{3125}$.
- $\frac12(\rho_\varepsilon+\sigma_\varepsilon)=(1-\varepsilon)\omega+\frac{\varepsilon}{2}I=(1-y)(I-A)+yA$ with $y=(1-\varepsilon)x+\frac{\varepsilon}{2}=\frac{999}{50000}+\frac{25}{50000}=\frac{64}{3125}$. By Lemma 3.2(b) its entropy is $h(y)$. So $\delta_\varepsilon:=\delta(\rho_\varepsilon,\sigma_\varepsilon)=h(\frac{64}{3125})-h(\frac{1}{2000})$, and $0\lt\delta_\varepsilon\lt h(\frac{64}{3125})$, because $h$ is strictly increasing on $(0,1/2]$ and $\frac{1}{2000}\lt\frac{64}{3125}$.
- **(L)** fails if and only if $\delta_\varepsilon\lt\bigl(\frac{6993}{25000}\bigr)^2\big/\bigl(8\cdot\frac{128}{3125}\bigr)=\frac{48902049}{204800000}$.
- By Lemma 3.3(e), $h(y)\lt y(1+\ln(1/y))$. Also $\frac{1}{y}=\frac{3125}{64}\lt 64=2^6$ (as $3125\lt 4096$), so $\ln(1/y)\lt 6\ln2\lt 6$. Natural logarithm: $\delta_\varepsilon\lt 7y=\frac{448}{3125}=\frac{29360128}{204800000}\lt\frac{48902049}{204800000}$. Base 2: $\frac{\delta_\varepsilon}{\ln2}\lt y\bigl(\frac{1}{\ln2}+6\bigr)\lt y\bigl(\frac32+6\bigr)=\frac{480}{3125}=\frac{31457280}{204800000}\lt\frac{48902049}{204800000}$, by Lemma 3.3(c).

(b) Let $d\ge2$ and take the violating triple $(\rho,\sigma_5,A_5)$ of Theorem 5.2. Put $\hat\rho=\rho\oplus0$, $\hat\sigma=\sigma_5\oplus0$ and $\hat A=A_5\oplus0$ in $M_d$ (block diagonal, with a zero block of size $d-2$). Then $\hat\rho,\hat\sigma$ are density matrices and $\hat A\ge0$. The eigenvalues of $\hat\rho$, $\hat\sigma$ and $\frac12(\hat\rho+\hat\sigma)$ are those of $\rho$, $\sigma_5$ and $\omega$ together with $d-2$ further zeros, so $\delta(\hat\rho,\hat\sigma)=\delta(\rho,\sigma_5)$ (as $\eta(0)=0$). Next, $\lvert\hat\rho-\hat\sigma\rvert=\lvert\rho-\sigma_5\rvert\oplus0$, since the spectral projections of a block-diagonal hermitian matrix are block diagonal. So $\mathrm{Tr}(\lvert\hat\rho-\hat\sigma\rvert\hat A)=\mathrm{Tr}(\lvert\rho-\sigma_5\rvert A_5)$, and $\mathrm{Tr}((\hat\rho+\hat\sigma)\hat A^2)=\mathrm{Tr}((\rho+\sigma_5)A_5^2)$. So **(L)** fails for $(\hat\rho,\hat\sigma,\hat A)$. ∎

For $d=1$ there is only one state and **(L)** reads $0\le0$. More generally, Proposition 7.2 covers every commuting pair.

## 7. Commuting states

Put $f(t)=t\ln t$ for $t>0$ and $f(0)=0$, so that $H(\tau)=-\sum_jf(\lambda_j)$.

**Lemma 7.1** (two-point inequality; `proposed`). For $p,q\ge0$ with $p+q>0$ and $a=(p+q)/2$:

```math
\frac{f(p)+f(q)}{2}-f(a)\ \ge\ \frac{(p-q)^2}{8(p+q)} .
```

*Plan.* A second-order Taylor bound for $f$ at the midpoint, with $f''(t)=1/t$ bounded below, followed by the harmonic–arithmetic mean inequality.

*Proof.* First, for $a>0$ and $c\ge0$:

```math
f(c)-f(a)-f'(a)(c-a)\ \ge\ \frac{(c-a)^2}{2(a+c)} .\qquad(\ast)
```

If $c>0$: $f$ is twice continuously differentiable on $(0,\infty)$ with $f''(t)=1/t$. By Taylor's formula with integral remainder, the left side of $(\ast)$ equals $\int_a^c(c-t)\frac{\mathrm{d}t}{t}$. Every $t$ between $a$ and $c$ satisfies $0\lt t\le a+c$, so $1/t\ge1/(a+c)$. If $c\ge a$, then $c-t\ge0$ on $[a,c]$ and $\int_a^c\frac{c-t}{t}\mathrm{d}t\ge\frac{1}{a+c}\int_a^c(c-t)\mathrm{d}t=\frac{(c-a)^2}{2(a+c)}$. If $c\lt a$, then $\int_a^c\frac{c-t}{t}\mathrm{d}t=\int_c^a\frac{t-c}{t}\mathrm{d}t\ge\frac{1}{a+c}\int_c^a(t-c)\mathrm{d}t=\frac{(a-c)^2}{2(a+c)}$. If $c=0$: the left side is $0-a\ln a+(\ln a+1)a=a$, and the right side is $a/2$.

Apply $(\ast)$ with $c=p$ and with $c=q$, and average. The linear terms cancel, since $(p-a)+(q-a)=0$, and $(p-a)^2=(q-a)^2=(p-q)^2/4$:

```math
\frac{f(p)+f(q)}{2}-f(a)\ \ge\ \frac{(p-q)^2}{16}\Bigl(\frac{1}{a+p}+\frac{1}{a+q}\Bigr)\ \ge\ \frac{(p-q)^2}{16}\cdot\frac{4}{2a+p+q}=\frac{(p-q)^2}{8(p+q)}.
```

The last step uses $\frac1y+\frac1z\ge\frac{4}{y+z}$ for $y,z>0$, which is equivalent to $(y+z)^2\ge4yz$. ∎

This is the argument behind the Taylor estimate (17) in Ozawa's paper [arXiv:2009.00837](https://arxiv.org/abs/2009.00837), §2, specialised to two points with weights $1/2$. The specialisation is ours; the paper does not state it.

**Proposition 7.2** (commuting states; `proposed`). If $\rho\sigma=\sigma\rho$, then for every hermitian $A$ (in particular every $A\ge0$), with the natural logarithm,

```math
\mathrm{Tr}(|\rho-\sigma|A)^2\le8\,\delta(\rho,\sigma)\,\mathrm{Tr}\bigl((\rho+\sigma)A^2\bigr).
```

Since $\delta_2\ge\delta$, the same holds in base 2. So **(L)** is true for commuting states.

*Plan.* Diagonalise both states at once, apply Lemma 7.1 to each pair of eigenvalues, and finish with the Cauchy–Schwarz inequality.

*Proof.* Commuting hermitian matrices have a common orthonormal eigenbasis. Conjugating $\rho,\sigma,A$ by the corresponding unitary changes none of $\mathrm{Tr}(\lvert\rho-\sigma\rvert A)$, $\delta(\rho,\sigma)$ and $\mathrm{Tr}((\rho+\sigma)A^2)$. So we may assume $\rho=\mathrm{diag}(p_1,\dots,p_d)$ and $\sigma=\mathrm{diag}(q_1,\dots,q_d)$ with probability vectors $p,q$. Then $\lvert\rho-\sigma\rvert=\mathrm{diag}(\lvert p_i-q_i\rvert)$, $\omega=\mathrm{diag}(a_i)$ with $a_i=(p_i+q_i)/2$, and by Lemma 7.1

```math
\delta(\rho,\sigma)=\sum_i\Bigl(\frac{f(p_i)+f(q_i)}{2}-f(a_i)\Bigr)\ \ge\ \sum_{i\in J}\frac{(p_i-q_i)^2}{8(p_i+q_i)},\qquad J=\lbrace i : p_i+q_i>0\rbrace .
```

(The terms with $i\notin J$ vanish.) In particular $\delta\ge0$, so $\delta_2=\delta/\ln2\ge\delta$ by Lemma 3.3(b). For hermitian $A$, $\mathrm{Tr}(\lvert\rho-\sigma\rvert A)=\sum_{i\in J}\lvert p_i-q_i\rvert A_{ii}$ with real $A_{ii}$. By the Cauchy–Schwarz inequality,

```math
\Bigl(\sum_{i\in J}|p_i-q_i|A_{ii}\Bigr)^2\le\sum_{i\in J}\frac{(p_i-q_i)^2}{p_i+q_i}\cdot\sum_{i\in J}(p_i+q_i)A_{ii}^2\ \le\ 8\,\delta(\rho,\sigma)\sum_i(p_i+q_i)(A^2)_{ii}=8\,\delta(\rho,\sigma)\,\mathrm{Tr}\bigl((\rho+\sigma)A^2\bigr),
```

where $A_{ii}^2\le\sum_j\lvert A_{ij}\rvert^2=(A^2)_{ii}$. ∎

*Smallest cases.* Lemma 7.1 at $p=q$ reads $0\ge0$. At $p=0$, $q=1$ it reads $\frac12\ln2\ge\frac18$, true since $\ln2>\frac23$. Proposition 7.2 at $d=2$, $p=(1,0)$, $q=(0,1)$ (the case $m=1$ of the family) reads $\sum_i(p_i-q_i)^2/(p_i+q_i)=2\le8\ln2$.

*Background (published, not used).* The sharp commutative constant is 4, not 8: $\sum_i(p_i-q_i)^2/(p_i+q_i)\le4\delta(p,q)$. This is due to Topsøe, [IEEE Trans. Inform. Theory 46 (2000) 1602–1609](https://doi.org/10.1109/18.850703). We did not read that paper; the statement was confirmed through secondary sources.

**Remark 7.3** (where the noncommutative transcription breaks; `proposed`). For commuting states $\lvert p_i-q_i\rvert\le p_i+q_i$ entrywise. This is what makes the weight $p_i+q_i$ sufficient in the Cauchy–Schwarz step. For matrices, $\lvert\rho-\sigma\rvert\le c(\rho+\sigma)$ fails for every constant $c$. On the family, $\lvert D_m\rvert=\frac{2m}{N+1}I$ while $S_mu=\frac{2}{N+1}u$ (Proposition 4.2 and Lemma 4.1), so $\langle u,\lvert D_m\rvert u\rangle/\langle u,S_mu\rangle=m$.

**Remark 7.4** (which reading was intended; `heuristic`, no claim). Theorem 5.2 is a statement about the printed formula under the standard meaning of its symbols. Whether that meaning was intended cannot be settled from the sources. The evidence is circumstantial:
1. *Notation.* The source prints $\lvert\varphi-\psi\rvert(A)$: the bars enclose the functional, and the argument $A$ stands outside, as in $(\varphi+\psi)(A^2)$ on the right. For a functional, bars denote the absolute value (Section 2.1). The other reading would be printed $\lvert(\varphi-\psi)(A)\rvert$.
2. *Shape and constant.* In Ozawa's paper [arXiv:2009.00837](https://arxiv.org/abs/2009.00837), §2, a Taylor estimate for $t\log t$ (display (17)) yields, through Lemma 7.1 and the Cauchy–Schwarz inequality, exactly Proposition 7.2: the commutative inequality with $\lvert p-q\rvert$ and the constant 8. So item (i), read literally, is the word-for-word noncommutative transcription of an inequality that this commutative argument gives. (The derivation is ours; the paper does not state it.)
3. *Item (ii)* of the same question is, in the same way, a noncommutative form of the chain of inequalities (18)–(19) of that paper.
4. *Against, or neutral.* The problem session (2018) predates the paper (2020). The paper never mentions a noncommutative version. No source states the intended reading. A slip for $\lvert(\varphi-\psi)(A)\rvert$, or an unstated restriction, cannot be excluded.

**This file does not address the reading $\lvert(\varphi-\psi)(A)\rvert$, and makes no claim about it.**

## 8. Computer verification

Two independent programs compute both sides of **(L)** from the definitions for the family at $m=1,\dots,7$, in natural logarithm and in base 2, and decide the sign of LHS² − 8δ·Tr(SA²). Neither program uses the closed form of Proposition 4.2 to decide; the primary one prints it only as a consistency check. The hand proofs above do not use either program.

| | Primary certificate | Independent cross-check |
| --- | --- | --- |
| Script | [`cert/OZ-1.py`](cert/OZ-1.py) | [`cert/OZ-1_x.py`](cert/OZ-1_x.py) |
| Arithmetic | python-flint 0.7.1: Arb ball arithmetic at 256 bits; exact rationals for the matrices | Python standard library only (`fractions`, `math.isqrt`); it asserts at run time that no numerical library is loaded and that every interval endpoint is a `Fraction` |
| Inputs | exact rational $\rho,\sigma_m,A_m$ from the family formula; exact checks that $\rho,\sigma_m$ are density matrices and $A_m\ge0$ | the same, with the matrices for $m=5,7$ also typed in literally and compared with the formula |
| $\lvert\rho-\sigma\rvert$ | from the spectral projections, in ball arithmetic | exactly: trace 0 and $(\rho-\sigma)^2=(-\det)I$, so $\lvert\rho-\sigma\rvert=\sqrt{-\det}\cdot I$ with a rational square root |
| Logarithms | Arb `log` | own rational enclosures from $\ln y=2\mathrm{artanh}\frac{y-1}{y+1}$, 60 terms, explicit tail bound |
| Decision | the ball of LHS² − 8δ·Tr(SA²) lies strictly on one side of 0 | the rational interval lies strictly on one side of 0 |
| Archived output | [`cert/OZ-1.out`](cert/OZ-1.out) | [`cert/OZ-1_x.out`](cert/OZ-1_x.out) |

**Result** (both outputs end with PASS, 2026-11-27; all 14 verdicts of each program agree): the literal inequality is violated for $m=4,5,6,7$ (natural logarithm) and $m=5,6,7$ (base 2), and not violated for $m=1,2,3$ (natural logarithm) and $m=1,2,3,4$ (base 2).

**Certified constants** (`certified`; digits truncated, not rounded; each value is a truncation of the ball printed in `cert/OZ-1.out`, and it agrees with the rational interval printed in `cert/OZ-1_x.out` to every decimal that file prints, which is 25):

| $m$ | LHS | $\mathrm{Tr}((\rho+\sigma)A^2)$ | $\delta$ (natural log) | (LHS/RHS)², natural log | $\delta_2$ (base 2) | (LHS/RHS)², base 2 |
| --- | --- | --- | --- | --- | --- | --- |
| 5 | 5/13 | 1/13 | 0.16302362949436594046925930… | 1.47453848334865481700577… | 0.23519338181924149141542913… | 1.02207219236025795050724… |
| 7 | 7/25 | 1/25 | 0.09803911327973198061225941… | 2.49900261032501436705753… | 0.14144054254182064515437899… | 1.73217661355872738185832… |

Commands, versions and runtimes are in [`REPRODUCE.md`](REPRODUCE.md).

**Sanity checks, not a certificate** (`numerical` where floating point is used). [`prover/check_proof.py`](prover/check_proof.py) repeats the smallest cases of every lemma and further checks: Lemma 4.1, Proposition 4.2 and Theorem 6.2 in exact rational arithmetic for 17 values of $m$; the entry arithmetic of Remark 5.3; the rational arithmetic of Lemma 5.1 and Corollary 6.5; and floating-point spot checks of Theorem 6.1 ($m\le3000$), Remark 5.4, Proposition 6.3 and Proposition 7.2 on random inputs. Its archived output, [`prover/out/check_proof.log`](prover/out/check_proof.log), ends with "RESULT: all 42 checks passed."

## 9. Formal verification

Details are in [`LEAN.md`](LEAN.md). In short:
- **Formalized** (Lean 4.37.0-rc1, Mathlib commit `8ec7bd8e5f837ab7e335374928e18341c4e9f385`; build passes, no `sorry`, only the axioms `propext`, `Classical.choice`, `Quot.sound`). Every quantity is defined from the matrices: the absolute value is Mathlib's `CFC.abs`, the matrix logarithm is `cfc Real.log`, the entropy is the real part of $-\mathrm{Tr}(X\log X)$, and $\delta$ is defined as in the source.
  - Theorem 5.2: `ozawa_literal_fails_m5`, `ozawa_literal_fails_m5_bits`, `ozawa_literal_fails_m7`, `ozawa_literal_fails_m7_bits`.
  - The negative answer as a universally quantified statement over $2\times2$ complex density matrices and $A\ge0$: `ozawa_question_literal_false` (natural log), `ozawa_question_literal_false_bits` (base 2), `ozawa_question_literal_false_rpow` (the power $1/2$ written as a real power).
  - Lemma 3.1 in general (`cfc_norm_of_mul_self`), Lemma 3.2 for $x\ne1/2$ (`cfc_twoProj` and supporting lemmas), and Lemma 5.1 (`ozawa_m5_nat`, `ozawa_m5_base2`, `ozawa_m7_nat`, `ozawa_m7_base2`).
- **Two stated deviations from the source.** The Lean statements take real parts of traces (the traces are proved equal to the real numbers 5/13, 1/13, 7/25, 1/25 for the witnesses), and they fix the dimension to 2 (which restricts the counterexample, not the question).
- **Not formalized:** Lemma 2.1 (Lean takes the matrix absolute value as the definition of $\lvert\varphi-\psi\rvert$), Lemma 4.1 and Proposition 4.2 for general $m$, Theorems 6.1 and 6.2, Proposition 6.3, Corollaries 6.4 and 6.5, Lemma 7.1 and Proposition 7.2, the family at $m\ne5,7$, and the decimal digits of Section 8.

## 10. Summary table

| Result | Hand proof | Computer | Lean |
| --- | --- | --- | --- |
| Lemma 2.1 (absolute value of a functional) | `proposed` | — | not formalized |
| Lemma 3.1 ($D^2=s^2I\Rightarrow\lvert D\rvert=sI$) | `proposed` | both certificates compute $\lvert\rho-\sigma\rvert$ independently | `formalized` (general) |
| Lemma 3.2 (two-level entropy) | `proposed` | — | `formalized` for $x\ne1/2$ |
| Lemma 3.3 (scalar facts) | `proposed` | — | three instances `formalized` |
| Lemma 4.1, Proposition 4.2 (closed form) | `proposed` | — | not formalized for general $m$ |
| Lemma 5.1 (four scalar inequalities) | `proposed` | `certified` | `formalized` |
| **Theorem 5.2 (negative answer, witnesses $m=5,7$, both bases)** | `proposed` | `certified` | `formalized` |
| Remark 5.4 (first violation $m=4$ natural, $m=5$ base 2) | `proposed` (monotonicity) | `certified` (signs, $m=1..7$) | not formalized |
| Theorem 6.1 (no constant) | `proposed` | — | not formalized |
| Theorem 6.2 (no function of $\delta$) | `proposed` | — | not formalized |
| Proposition 6.3, Corollary 6.4 (quotient at most 2; threshold $1/4$) | `proposed` | — | not formalized |
| Corollary 6.5 (faithful states; all dimensions) | `proposed` | — | not formalized |
| Lemma 7.1, Proposition 7.2 (commuting states) | `proposed` | — | not formalized |
| Remark 7.4 (intended reading) | `heuristic` | — | — |
