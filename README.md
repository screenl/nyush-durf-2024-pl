# nyush-durf-2024-pl

Axiomatic Foundations of Convex Analysis in Proof Assistants

The purpose of the DURF project will be to formalize in the proof assistant Coq
a number of fundamental properties satisfied by barycentric spaces.
A barycentric space is a generalisation of the notion of real vector space,
defined axiomatically as sets equipped with a barycentric notion of addition.
We will formally establish a result by Ehrhard-Mellies-Theron which provides
sufficient and necessary conditions for a barycentric space to be faithfully
embedded in a real vector space.

We can see how we can certify linear programming algorithms.
And/or study probabilistic automata and probabilistic languages.

What needs to be done: find the existing libraries in Coq and Lean.


The well-established notion of real vector space defined axiomatically as follows.

A commutative monoid is a set M equipped with a binary operation + : M x M --> M and an element 0 such that

Associativity: ( x + y ) + z = x + ( y + z )

Neutrality: x + 0 = x = 0 + x

Commutativity: x + y = y + x

A real vector space V is a commutative monoid equipped with a scalar multiplication R x V --> V 
satisfying the following equations:

Action Law 1 : ( lambda mu ) x = lambda ( mu x )

Action Law 2 : 1 x = x

DistributivityR2 : lambda ( x + y ) = ( lambda x ) + ( lambda y )

DistributivityR0 : lambda 0 = 0

DistributivityL2 : (lambda + mu) x = (lambda x) + (mu x)

Distributi

In many situations of interest, we do not have a vector space but a notion of space where only barycentric addition is defined.
A typical example is the set of probability distributions on a finite set.

A barycentric space is required to satisfy four parametrized families
of equations:
\begin{center}
\begin{tabular}{cl}
$\barysum{0}{a}{b} = a$ &
\\
$\barysum{\ratio}{a}{a} = a$ &
\\
$\barysum{\ratio}{a}{b} = \barysum{1-\ratio}{b}{a}$ &
\\
%$\barysum{\ratio}{x}{(\barysum{1-\ratiob}{y}{z})}=\barysum{\ratiod}{(\barysum{1-\ratioc}{x}{y})}{z}$
%&
%whenever $\ratiod=\ratio(1-\ratiob)$ and $\ratio\ratiob=\ratiod\ratioc$.
%\\
$\barysum{\ratio}{a}{(\barysum{\ratiob}{b}{c})}=\barysum{\ratiod}{(\barysum{\ratioc}{a}{b})}{c}$
&
if $\ratiod=\ratio\ratiob$ and $\ratio(1-\ratiob)=\ratioc(1-\ratiod)$
\end{tabular}
\end{center}
for all $\ratio,\ratiob,\ratioc\in\interval$ and for all $a,b,c\in\baryspace$.
%
Note that $\barysum{1}{a}{b}=b$ as a consequence of the first and third equations,
and that the fourth equation holds precisely when $\ratiod=\ratio\ratiob=1$ and ($\ratiod=\ratio\ratiob\neq 1$ 
and $\ratioc=\frac{\ratio-\ratio\ratiob}{1-\ratio\ratiob}$).

