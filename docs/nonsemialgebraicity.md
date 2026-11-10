# Nonsemialgebraicity of Planar Discrete-Time Bilinear Controllability

8 November 2026

## Abstract

Consider the homogeneous single-input discrete-time bilinear system
$x_{k+1}=(A+u_kB)x_k$ on $\mathbb R^2\setminus\{0\}$, with arbitrary real $2\times2$ matrices $A,B$ and unrestricted real controls. We prove that its global-controllability locus is not semialgebraic. The stronger statement holds even when a proposed fixed semialgebraic criterion is required to be correct only for rational matrix entries (while controls remain real). The proof reduces controllability in an explicit nonsingular three-parameter family to growth of products of rank-one projections. A near-quarter-turn perturbation produces a limiting growth coefficient with logarithmic onset, incompatible with any polynomial relation.

## 1. Main theorems and conventions

Let $X=\mathbb R^2\setminus\{0\}$, and let $A,B\in\mathbb R^{2\times2}$ be arbitrary matrices. Write $\mathrm{Ctrl}(A,B)$ if, for every $\xi,\eta\in X$, there are $N\ge1$ and real controls $u_0,\ldots,u_{N-1}$ satisfying

```math
\eta=(A+u_{N-1}B)\cdots(A+u_0B)\xi.
```

The positive-length requirement applies even when $\xi=\eta$.

Define the global-controllability locus for all matrix pairs by

```math
\mathcal C=\{(A,B)\in\mathbb R^8:\mathrm{Ctrl}(A,B)\}.
```

A *fixed finite algebraic formula* is a finite Boolean combination of predicates $p(A,B)=0$, $p(A,B)>0$, or $p(A,B)<0$, where each $p$ is a polynomial in the eight matrix entries with fixed coefficients in $\mathbb R$. We permit arbitrary real coefficients, not just rational ones.

**Theorem 1 (Rational-input nonsemialgebraicity).** There is no semialgebraic set $S\subseteq\mathbb R^8$ such that

```math
\forall A,B\in\mathbb Q^{2\times2},\qquad
\big((A,B)\in S\iff\mathrm{Ctrl}(A,B)\big).
```

**Corollary 2 (Real-input nonsemialgebraicity).** The global-controllability locus $\mathcal C$ is not semialgebraic in $\mathbb R^8$.

Theorem 1 is the main result; Corollary 2 follows because a formula correct for all real matrices would also be correct for rational matrices.

**Corollary 3 (Auxiliary real quantifiers).** No fixed first-order formula in the language of ordered fields, with arbitrary real parameters and finitely many auxiliary real quantifiers, characterizes controllability on all real matrix pairs or on all rational matrix pairs.

*Proof.* Real quantifier elimination replaces such a formula by a finite Boolean combination of polynomial equalities and inequalities. Apply Theorem 1 and Corollary 2. $\square$

**Proof idea.** We restrict attention to a three-parameter family of systems for which controllability is exactly equivalent to a scalar growth threshold. Near a quarter-turn matrix, that threshold has a second-order perturbation coefficient determined by an integral. The coefficient approaches its critical value like $\delta/|\log\delta|$, which cannot lie on any polynomial curve. A hypothetical finite algebraic classifier would force precisely such a polynomial relation.

## 2. Exact reduction to cycle growth

Put

```math
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
M_K(u)=K^{-1}(I+uJ),\qquad P_e=ee^{\mathsf T}\quad(\|e\|=1).
```

For any real $2\times2$ matrix $K$, define its *closed-cycle growth*

(2.1)

```math
\Gamma(K)=\sup_{\substack{n\ge1,\ e_0,\ldots,e_n\in S^1\\e_n=e_0}}
\left|\prod_{i=1}^{n}e_i^{\mathsf T}Ke_{i-1}\right|^{1/n}.
```

The supremum is finite, since every factor is bounded by $\|K\|_2$. Also
$\Gamma(tK)=|t|\Gamma(K)$ for real $t$.

**Lemma 1 (Exact controllability–cycle criterion).** Suppose $K\in GL_2(\mathbb R)$, $K_{11}\ne0$, and $K_{12}K_{21}<0$. Then

(2.2)

```math
\mathrm{Ctrl}(K^{-1},K^{-1}J)\quad\Longleftrightarrow\quad\Gamma(K)>1.
```


*Proof.* An original nonzero step $y=M_K(u)x$ is equivalent to
$Ky=x+uJx$. Taking its inner product with $x$ gives
$x^{\mathsf T}Ky=\|x\|^2$; conversely that identity determines a real $u$, since $x,Jx$ are an orthogonal basis. Thus the nonzero reverse steps are precisely

(2.3)

```math
y\longmapsto x=P_eKy\ne0,\qquad e\in S^1.
```


If the original system is globally controllable, take a forward trajectory from a unit $e$ to $e/2$. Reversing it gives a closed projective cycle with multiplier $2$. Consequently $\Gamma(K)>1$.

Conversely, suppose $\Gamma(K)>1$. Some finite closed reverse cycle has absolute multiplier greater than one. Two reverse steps connect any two prescribed projective directions: choose an intermediate unit vector $f$ avoiding the two proper kernels of the nonzero linear forms $f\mapsto f^{\mathsf T}Kv$ and $f\mapsto w^{\mathsf T}Kf$. Transport the expanding cycle to the base direction $e_1$, repeat it enough times, and then square the transported return. This produces an $e_1$-based return with a positive multiplier $g>1$.

The two-step return based at $e_1$ through a unit $f$ has multiplier
$r(f)=(e_1^{\mathsf T}Kf)(f^{\mathsf T}Ke_1)$. This continuous function satisfies $r(e_1)=K_{11}^2>0$, and it vanishes at some $f_0$ because the nonzero linear form $f\mapsto e_1^{\mathsf T}Kf$ has a kernel. By the intermediate value theorem, it takes every value in $ (0,K_{11}^2)$. Repeating a chosen two-step return twice therefore realizes every sufficiently small positive multiplier. Combining these with powers of $g$ realizes every positive multiplier: given $t>0$, choose $m$ with $t/g^m$ small enough.

Moreover the coordinate two-cycle $e_1,e_2,e_1$ has multiplier $K_{12}K_{21}<0$, so a negative multiplier is available at the same base. Thus every nonzero signed multiplier is attainable there. Nonzero two-step direction bridges before and after the base returns now connect arbitrary nonzero states with exact final magnitude and sign. Reversing the constructed path via (2.3) recovers finite original real controls; no intermediate state is zero. All constructed paths have positive length. $\square$

Our perturbation family satisfies $K_{11}=\varepsilon(a+1)>0$, so the additional hypothesis is automatic there.

## 3. A quarter-turn perturbation and its growth coefficient

Fix

(3.1)

```math
a_0=\frac2\pi<a<1,\quad
K_{\varepsilon,a}=J+\varepsilon
\begin{pmatrix}a+1&0\\0&a-1\end{pmatrix},
\quad\varepsilon>0.
```

For small $\varepsilon$, $K_{\varepsilon,a}$ is invertible because
$\det K_{\varepsilon,a}=1+\varepsilon^2(a^2-1)>0$. Its off-diagonal entries are $-1$ and $1$, so Lemma 1 applies after any positive scaling; moreover $K_{11}=\varepsilon(a+1)>0$.

Define

(3.2)

```math
F(\lambda)=\frac2\pi\int_0^{\pi/2}
\sqrt{2\lambda+\sin^2t}\,dt,\qquad \lambda\ge0.
```

Since $F(0)=2/\pi$, $F$ is continuous and strictly increasing, and $F(\lambda)\to\infty$, there is a unique $\lambda(a)>0$ satisfying $F(\lambda(a))=a$. The function $a\mapsto\lambda(a)$ is continuous on $(a_0,1)$.

**Lemma 2 (Uniform quarter-turn growth asymptotic).** For every fixed $a\in(a_0,1)$,

(3.3)

```math
\log\Gamma(K_{\varepsilon,a})
=\lambda(a)\varepsilon^2+O_a(\varepsilon^3)
\qquad(\varepsilon\downarrow0).
```

The upper estimates hold uniformly over projective directions and path lengths after normalization. The lower estimates use chosen successors and paths, with remainder constants independent of the starting direction and path length. No uniformity as $a\downarrow a_0$ is asserted.

*Proof.* Write $e_\theta=(\cos\theta,\sin\theta)^{\mathsf T}$, and represent an output direction by $e_{\theta+\pi/2+t}$. Direct multiplication gives the exact scalar edge gain

(3.4)

```math
f_\varepsilon(\theta,t)=e_{\theta+\pi/2+t}^{\mathsf T}
K_{\varepsilon,a}e_\theta
=\cos t-\varepsilon\big(a\sin t+\sin(2\theta+t)\big).
```

Let $\lambda=\lambda(a)$ and set $S(\theta)=\sqrt{2\lambda+\sin^22\theta}$. By the defining equation for $\lambda$, the $\pi/2$-periodic function $a-S(\theta)$ has mean zero. It therefore admits a smooth $\pi/2$-periodic primitive $H$ satisfying

```math
H'(\theta)=a-S(\theta),\qquad
h(\theta)=-\tfrac12\sin2\theta+H(\theta).
```

Here $h$ is $\pi$-periodic. In particular,

(3.5)

```math
h(\theta+\pi/2)-h(\theta)=\sin2\theta,
\qquad h'(\theta+\pi/2)=\cos2\theta+H'(\theta).
```

Introduce the positive homogeneous angular weight
$W_\varepsilon(re_\theta)=r\exp(\varepsilon h(\theta))$ for $r\ge0$. Its logarithmic gain in a nonzero reverse step is

(3.6)

```math
D_\varepsilon(\theta,t)=\log|f_\varepsilon(\theta,t)|
+\varepsilon\big[h(\theta+\pi/2+t)-h(\theta)\big].
```

Since $\lambda>0$, all derivatives of $h$ needed below are bounded. Fix $a$ and write $v(\theta)=H'(\theta)-a=-S(\theta)$, whose absolute value is bounded by $a+1$. The elementary Taylor expansions of sine, cosine, logarithm, and $h$, with remainders bounded on this compact range, give uniformly in $\theta$

(3.7)

```math
D_\varepsilon(\theta,\varepsilon v)
=\varepsilon^2\left[-\frac{v^2}{2}
+v(H'(\theta)-a)-\frac{\sin^22\theta}{2}\right]
+O_a(\varepsilon^3)
=\lambda\varepsilon^2+O_a(\varepsilon^3).
```

This supplies one nearly maximizing successor from each direction.

For the matching global upper bound, write (3.4) as

```math
f_\varepsilon(\theta,t)=p\cos t-q\sin t,
\quad p=1-\varepsilon\sin2\theta>0,
\quad q=\varepsilon(a+\cos2\theta).
```

The maximal interval on which $f_\varepsilon>0$ and which contains $t=0$ has length $\pi$, so it contains one representative of every output projective direction with nonzero gain. On this interval,

```math
\frac{d^2}{dt^2}\log f_\varepsilon
=-1-\left(\frac{f_\varepsilon'}{f_\varepsilon}\right)^2\le-1.
```

Let $M_a=\|h''\|_\infty<\infty$, and take $\varepsilon M_a<1/2$. Then $D_\varepsilon''\le-(1-\varepsilon M_a)$. Strong concavity implies

(3.8)

```math
\sup_tD_\varepsilon(\theta,t)
\le D_\varepsilon(\theta,0)
+\frac{D_\varepsilon'(\theta,0)^2}{2(1-\varepsilon M_a)}.
```

Uniformly in $\theta$, with $z=\sin2\theta$,

```math
D_\varepsilon(\theta,0)=-\frac12\varepsilon^2z^2+O(\varepsilon^3),
\qquad
D_\varepsilon'(\theta,0)=\varepsilon(H'(\theta)-a)+O_a(\varepsilon^2).
```

Substituting into (3.8) gives

(3.9)

```math
\sup_tD_\varepsilon(\theta,t)
\le\frac{\varepsilon^2}{2}
\big[(H'-a)^2-\sin^22\theta\big]+O_a(\varepsilon^3)
=\lambda\varepsilon^2+O_a(\varepsilon^3).
```

All constants in (3.7)–(3.9) depend only on the fixed $a$, not on $\theta$, $t$, or path length. These estimates show that each weighted reverse step has gain at most $\exp(\lambda\varepsilon^2+C_a\varepsilon^3)$, while each direction admits a chosen successor with gain at least $\exp(\lambda\varepsilon^2-C_a\varepsilon^3)$.

The upper inequality telescopes around every closed cycle. For the lower inequality, iterate the chosen successors for $n$ steps. The unweighted product loses at most the fixed factor $\exp(-2\varepsilon\|h\|_\infty)$. Close its terminal direction to its starting direction with two more projections. This closure has absolute multiplier at least $\sigma_{\min}(K_{\varepsilon,a})^2/2>0$: maximize $|(e_0^{\mathsf T}Kf)(f^{\mathsf T}Ke_n)|$ over unit $f$, using

```math
\max_{\|f\|=1}|(p^{\mathsf T}f)(q^{\mathsf T}f)|
=\frac{\|p\|\|q\|+|p^{\mathsf T}q|}{2}.
```

The resulting $(n+2)$-cycle has gain at least a fixed positive factor times $\exp(n(\lambda\varepsilon^2-C_a\varepsilon^3))$. Taking its $(n+2)$-nd root as $n\to\infty$, and combining with the upper bound, gives (3.3). $\square$

## 4. Logarithmic onset and nonalgebraicity

**Lemma 3 (Logarithmic onset and nonalgebraicity).** With $a_0=2/\pi$,

(4.1)

```math
\lambda(a_0+\delta)
\sim\frac{\pi\delta}{|\log\delta|}
\qquad(\delta\downarrow0).
```

In particular, no nonzero polynomial $Q(a,z)\in\mathbb R[a,z]$ vanishes on the graph $z=\lambda(a)$ throughout $(a_0,1)$.

*Proof.* For $\lambda>0$, differentiation under the nonsingular integral in (3.2) gives

```math
F'(\lambda)=\frac2\pi\int_0^{\pi/2}
\frac{dt}{\sqrt{2\lambda+\sin^2t}}.
```

On a fixed interval $[d,\pi/2]$, $d>0$, the integral is uniformly bounded as $\lambda\downarrow0$. On $[0,d]$, use $\sin^2t=t^2+O(t^4)$ and $\sin t\ge t/2$ for small fixed $d$. The difference between the displayed integrand and $(2\lambda+t^2)^{-1/2}$ is bounded by $Ct$, uniformly for small $\lambda$. Hence

```math
F'(\lambda)=\frac2\pi\int_0^d
\frac{dt}{\sqrt{2\lambda+t^2}}+O(1)
=\frac{|\log\lambda|}{\pi}+O(1).
```

Integrating from zero, using continuity of $F$ there, yields

```math
\delta=F(\lambda)-F(0)
=\frac{\lambda}{\pi}|\log\lambda|+O(\lambda).
```

It follows that $|\log\delta|/|\log\lambda|\to1$, proving (4.1).

To rule out a polynomial relation, suppose $Q(a_0+\delta,\lambda(a_0+\delta))=0$. Expand the nonzero polynomial in monomials $\delta^i z^j$. Select the smallest total degree $m=i+j$ occurring and, among those, the smallest $j$. After substituting (4.1), the selected monomial is asymptotic to a nonzero constant times $\delta^m|\log\delta|^{-j}$. Every other monomial is smaller, either by an extra inverse logarithm or by an extra positive power of $\delta$. Cancellation is impossible. $\square$

## 5. Proof of rational-input nonsemialgebraicity

*Proof of Theorem 1 and Corollary 2.* Let

(5.1)

```math
g(\varepsilon,a)=\Gamma(K_{\varepsilon,a}),
\qquad
A=sK_{\varepsilon,a}^{-1},\quad B=AJ,
\quad\tfrac12<s<2.
```

All matrix entries in (5.1) are rational functions of $\varepsilon,a,s$. Whenever these parameters are rational, $A,B$ have rational entries. Since $A+uB=(K_{\varepsilon,a}/s)^{-1}(I+uJ)$, Lemma 1 and homogeneity of $\Gamma$ give

(5.2)

```math
\boxed{\mathrm{Ctrl}(A,B)\iff s<g(\varepsilon,a).}
```

For $0<\varepsilon<1/4$ and $a_0<a<1$, the coordinate two-cycle gives $g\ge1$, and $g\le\|K_{\varepsilon,a}\|_2\le1+2\varepsilon<2$. Thus the threshold $s=g(\varepsilon,a)$ lies strictly inside the permitted $s$-interval.

Suppose, seeking a contradiction, that a fixed finite algebraic formula correctly decides controllability for every rational pair. Pull its polynomial tests back through (5.1). After clearing denominators of fixed sign on this parameter box and simplifying identically zero tests, we obtain a finite Boolean formula with nonzero atomic polynomials

```math
p_1(\varepsilon,a,s),\ldots,p_m(\varepsilon,a,s)
\in\mathbb R[\varepsilon,a,s].
```

There must be at least one nonzero atom; otherwise the formula is constant on the family. Set $P=\prod_{j=1}^m p_j$, a nonzero polynomial.

For every rational $\varepsilon,a$ in the stated parameter intervals,

(5.3)

```math
P(\varepsilon,a,g(\varepsilon,a))=0.
```

Indeed, if all atoms were nonzero at the threshold $s=g(\varepsilon,a)$, their signs—and therefore the formula's truth value—would be locally constant in $s$. But rational $s$ occur arbitrarily close on both sides of that threshold, where (5.2) requires opposite answers. This contradicts correctness on rational matrix entries. Notice that (5.3) does not require the threshold itself to be rational.

Substitute $s=1+\varepsilon^2z$ into $P$. The resulting polynomial is nonzero (the substitution is injective for $\varepsilon\ne0$); hence for some integer $k\ge0$,

(5.4)

```math
P(\varepsilon,a,1+\varepsilon^2z)
=\varepsilon^k\big(Q(a,z)+\varepsilon R(\varepsilon,a,z)\big),
\quad Q\in\mathbb R[a,z]\setminus\{0\}.
```

Fix a rational $a\in(a_0,1)$, let rational $\varepsilon\downarrow0$, and set
$z_\varepsilon=(g(\varepsilon,a)-1)/\varepsilon^2$. By Lemma 2 and $e^t=1+t+O(t^2)$,

```math
z_\varepsilon\longrightarrow\lambda(a).
```

Equations (5.3)–(5.4) therefore imply $Q(a,\lambda(a))=0$. Rational $a$'s are dense, and $\lambda(a)$ is continuous, so

```math
Q(a,\lambda(a))=0
\quad\text{for every }a\in(a_0,1).
```

This contradicts Lemma 3. Theorem 1 follows, and Corollary 2 is its immediate consequence. $\square$

## 6. Scope, verification, and references

The results concern fixed finite polynomial-sign formulas and, by Corollary 3, formulas with finitely many auxiliary real quantifiers. They do not establish Turing undecidability for rational matrix encodings or rule out procedures with an input-dependent unbounded number of steps. Quantification over integers or rationals is a different logical language.

A Lean formalization of the finite polynomial-sign obstruction accompanies this note. The extension by real quantifier elimination is not included in the formalized result.

**References and context.** For related work on controllability of discrete-time bilinear systems, see L. Tie, “Invariant sets and controllability of discrete-time bilinear systems,” *IET Control Theory & Applications* (2018), DOI [10.1049/iet-cta.2017.1025](https://doi.org/10.1049/iet-cta.2017.1025). The real-quantifier-elimination statement used above is the classical Tarski–Seidenberg theorem; for a mathematical reference see J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Springer (1998), DOI [10.1007/978-3-662-03718-8](https://doi.org/10.1007/978-3-662-03718-8). The present proof is self-contained apart from that standard theorem for the quantified-formula extension.
