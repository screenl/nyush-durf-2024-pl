# nyush-durf-2024-pl

Axiomatic Foundations of Convex Analysis in Proof Assistants

The purpose of the DURF project will be to formalize in the proof assistant Coq
a number of fundamental properties satisfied by barycentric spaces.
A barycentric space is a generalisation of the notion of real vector space,
defined axiomatically as sets equipped with a barycentric notion of addition.
We will formally establish a result by Ehrhard-Mellies-Theorem which provides
sufficient and necessary conditions for a barycentric space to be faithfully
embedded in a real vector space.

We can see how we can certify linear programming algorithms.
And/or study probabilistic automata and probabilistic languages.

What needs to be done: find the existing libraries in Coq and Lean.



An interval $\mathbb{P}$ is a set with:
1. a commutative monoid structure $(p,q \mapsto p \wedge q,1)$
2. a commutative monoid structure $(p,q \mapsto p \vee q,0)$
3. a duality $p \mapsto \overline p$, s.t. $\overline{\overline p} = p, \overline{p \vee q} = \overline p \wedge \overline q$

Notation: $p \Rightarrow q := \overline p \vee q$

A $\mathbb{P}$-barycentric space $(\Omega,+_p)$ is a set with $+_p: \mathbb{P} \rightarrow \Omega \rightarrow \Omega \rightarrow \Omega$.
1. $a+_p b = b+_{\overline p}a$
2. $a+_1b = a$
3. $a+_pa=a$
4. $a+_p(b+_qc) = (a+_rb)+_sc$ when $p = r \wedge s, s = p \vee q, q \Rightarrow p = s \Rightarrow r$

**Proposition 1**: $\mathbb{P}$ is a $\mathbb{P}$-barycentric space.

**Observation**: the cartesian product of two P-barycentric spaces is P-barycentric:
$(x,y)+_p(x’,y’) = (x+_px,y+_py’)$

**Proposition 2**: suppose $\sim$ is an equivalence relation on $\mathbb{P}$-barycentric space $X$ s.t. $x+_px \sim x’+_py’$ when $x\sim x’$ and $y\sim y’$, $X/\sim$ is a $\mathbb{P}$-barycentric space.

Construction of the _cone_ $X_\*$ of a barycentric space $X$.
$X_\* = P \times X /\sim$ where $(1,x)\sim(1,x’)$; thus $X_\*$ is $\mathbb{P}$-barycentric.

**Proposition 3**: $X \mapsto X_\*$ is functorial.

**Proposition 4**: $1_\* = P$

**Proposition 5**: $X_{\*\*}$ is automorphic.

