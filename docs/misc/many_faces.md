# The Many Faces of Geometric Algebra

Geometric Algebra (GA) or Clifford Algebra can be defined in many ways. We summarize the definitions here to inspire proper ways to formalize GA.

Some definitions are very elementary but hard to make rigorous. Some may seem rigorous but still hard to formalize. Some are very rigorous and can be formalized but fail to remain intuitive or elegant.

<del>Definitions are grouped by similarity. The definitions in the same group would have subtle yet important differences, that's why they deserve to be listed here.</del>

Definitions are mostly direct quotes from the source, with slight modifications for readability or brevity.

> The following are work-in-progress and not necessarily well organized.

### Lynn

> source: [All Hail Geometric Algebra!](https://crypto.stanford.edu/~blynn/haskell/ga.html) by [Ben Lynn](https://crypto.stanford.edu/~blynn/)

We can trivially define a product with nice properties on any set: just take [the free monoid](https://en.wikipedia.org/wiki/Free_monoid). Similarly, we can define a vector product with nice properties thanks to [free algebras](https://en.wikipedia.org/wiki/Free_algebra).

By constraining our free algebra with one simple relation, we obtain the vaunted geometric algebra. We define the geometric product by subjecting the free product to the following constraint: for any vector $\mathbf{v}$,

$$ \mathbf{v v} = \mathbf{v} \cdot \mathbf{v}$$

We could [generalize by replacing the dot product with any quadratic form, and by considering any vector space over any field](https://en.wikipedia.org/wiki/Geometric_algebra), but we focus on the standard dot product on $\mathbb{R}^{n},$ where the resulting geometric algebra is denoted $\mathbb{G}^{n}$

We could have instead written $\mathbf{v}^{2}=|\mathbf{v}|^{2},$ but this hides our need for the [polarization identity](https://en.wikipedia.org/wiki/Polarization_identity):

$$
\mathbf{u} \cdot \mathbf{v}=\frac{1}{2}((\mathbf{u}+\mathbf{v}) \cdot(\mathbf{u}+\mathbf{v})-\mathbf{u} \cdot \mathbf{u}-\mathbf{v} \cdot \mathbf{v})
$$

From our constraint, this is:

$$
\mathbf{u} \cdot \mathbf{v}=\frac{1}{2}\left((\mathbf{u}+\mathbf{v})^{2}-\mathbf{u}^{2}-\mathbf{v}^{2}\right)
$$

By elementary algebra, this implies:

$$
\mathbf{u} \cdot \mathbf{v}=\frac{1}{2}(\mathbf{u} \mathbf{v}+\mathbf{v} \mathbf{u})
$$

Hence when $\mathbf{u}$ and $\mathbf{v}$ are orthogonal, we have $\mathbf{u v}=-\mathbf{v u}$ .

### Chisolm 2012

A geometric algebra is a set $\mathcal{G}$ with two composition laws, addition and multiplication (also called the geometric product$),$ that obey these axioms.

Axiom 1. $\mathcal{G}$ is a ring with unit. The additive identity is called 0 and the multiplicative identity is called 1.

Axiom 2. $\mathcal{G}$ contains a field $\mathcal{G}_0$ of characteristic zero which includes 0 and 1.

Axiom 3. $\mathcal{G}$ contains a subset $\mathcal{G}_1$ closed under addition, and $\lambda \in \mathcal{G}_0$, $v \in \mathcal{G}_1$ implies $\lambda v = v \lambda \in \mathcal{G}_1$.

Axiom 4. The square of every vector is a scalar.

<del>Axiom 5. The inner product is nondegenerate.</del>

Axiom 6. If $\mathcal{G}_0 = \mathcal{G}_1$, then $\mathcal{G} = \mathcal{G}_0$. Otherwise,  $\mathcal{G}$ is the direct sum of all the $\mathcal{G}_r$.

For each $r$, let the grade operator $\left< \right>_r : \mathcal{G} \to \mathcal{G}_r$ project each $A \in \mathcal{G}$ onto its unique grade-$r$ component.
Then
(a) $A$ is an $r$-vector iff $A = \left<A\right>_r$.
(b) $\left<A+B\right>_r$ = $\left<A\right>_r$ + $\left<B\right>_r$.
(c) $\left< \lambda A \right>_r$ = $\left< A \lambda \right>_r$ = $\lambda \left<A\right>_r$.
(d) $\left<\left<A\right>_r\right>_s = <\left<A\right>_r\delta_{rs}$. (Thus the $\left< \right>_r$ are independent projection operators.)
(e) $\sum_r \left<A\right>_r = A$ for any $A \in \mathcal{G}$. (Thus the $\left< \right>_r$ are a complete set of projection operators.)
(f) $\left<A\right>_r = 0$ if $r \lt 0$ for all $A \in \mathcal{G}$.
Because we take the scalar part of multivectors so often, I will let $\left<A\right>$ mean $\left<A\right>_0$.

### Buchholz 2005

> Source: Chapter 2 Clifford Algebra in [A Theory of Neural Computation
with Clifford Algebras](https://macau.uni-kiel.de/servlets/MCRFileNodeServlet/dissertation_derivate_00001402/d1402.pdf) by Sven Buchholz.

> The main definition and theorems of Clifford algebras will be presented following mostly I. R. Porteous. **Clifford Algebras and the Classical Groups**. Cambridge University Press, Cambridge, 1995 and P. Lounesto. **Clifford Algebras and Spinors**. Cambridge University Press, 1997. By doing so Clifford algebras will be constructed from quadratic spaces, and, hence, will have a metric structure right from the beginning.

> There is and will always be an ongoing discussion in the Clifford (Geometric) Algebra community, if this is a good idea and how important metric aspects are for the very first foundation of Clifford (Geometric) Algebra [40]. For our approach, since being heavily based on the idea of transformation groups, they are mandatory.

#### Definition 2.1 (Real Algebra)

$A$ real algebra is a real linear space $(\mathcal{A},+, \cdot)$ endowed with a bilinear product

$$
\otimes: \mathcal{A} \times \mathcal{A} \rightarrow \mathcal{A},(\mathrm{a}, \mathrm{b}) \mapsto \mathrm{a} \otimes \mathrm{b}
$$

Hence, a real algebra is a pair $((\mathcal{A},+, \cdot), \otimes)$

#### Definition 2.2 (Types of Algebras)

An algebra $((\mathcal{A},+, \cdot), \otimes)$ is called

(i) associative, if for all $\mathrm{a}, \mathrm{b}, \mathrm{c} \in \mathcal{A}:(\mathrm{a} \otimes \mathrm{b}) \otimes \mathrm{c}=\mathrm{a} \otimes(\mathrm{b} \otimes \mathrm{c})$
(ii) commutative, if for all $\mathrm{a}, \mathrm{b} \in \mathcal{A}: \mathrm{a} \otimes \mathrm{b}=\mathrm{b} \otimes \mathrm{a}$
(iii) an algebra with identity, if there exists $1 \in \mathcal{A}$ such that for all $\mathrm{a} \in \mathcal{A}$ $1 \otimes \mathrm{a}=\mathrm{a} \otimes 1=1$

The real numbers considered as algebra $((\mathbb{R},+, \cdot), \cdot),$ for example, do comprise all the attributes of Definition 2.2

#### Proposition 2.3

For any algebra $((\mathcal{A},+, \cdot), \otimes),$ the product $\otimes$ is already uniquely determined given only the products for an arbitrary basis of $\mathcal{A}$.

#### Proposition 2.4

Any algebra $((\mathcal{A},+, \cdot), \otimes)$ is distributive by definition, or, equivalently, $(\mathcal{A},+, \otimes)$ is always a ring.

#### Proposition 2.5

Two finite dimensional algebras $\mathcal{A}$ and $\mathcal{B}$ are isomorphic, written as $\mathcal{A} \cong \mathcal{B},$ if they are isomorphic as rings, that is if there exists a bijective mapping $\phi: \mathcal{A} \rightarrow \mathcal{B}$ such that, for all $\mathrm{a}, \mathrm{b} \in \mathcal{A}$
(i) $\phi(a+b)=\phi(a)+\phi(b)$
(ii) $\phi(\mathrm{a} \otimes \mathrm{b})=\phi(\mathrm{a}) \otimes \phi(\mathrm{b})$

#### Definition 2.6 (Tensor Product)

Let $\mathcal{A}$ be a finite dimensional real associative algebra with identity. If there exist subalgebras $\mathcal{B}$ and $\mathcal{C}$ of $\mathcal{A}$ such that
(i) for any $\mathrm{b} \in \mathcal{B}, \mathrm{c} \in \mathcal{C}, \mathrm{bc}=\mathrm{cb}$
(ii) $\mathcal{A}$ is generated as an algebra by $\mathcal{B}$ and $\mathcal{C}$
(iii) $\operatorname{dim} \mathcal{A}=\operatorname{dim} \mathcal{B} \operatorname{dim} \mathcal{C}$
then $\mathcal{A}$ is said to be the tensor product of $\mathcal{B}$ and $\mathcal{C},$ written as $\mathcal{B} \otimes \mathcal{C}$

#### Definition 2.7 (Field)

Let $(\mathcal{R},+, \otimes)$ be a ring. If $(\mathcal{R} \backslash\{0\}, \otimes)$ is a (non-)commutative $g$roup$,$then $(\mathcal{R},+, \otimes)$ is called a (skew) field.

#### Definition 2.8 (The Field of Complex Numbers)

Consider the set of all ordered pairs of real numbers
$$
\mathbb{R}^{2}=\{z=(a, b) \mid a, b \in \mathbb{R}\}
$$
together with addition and multiplication defined for all $z_{1}=\left(a_{1}, b_{1}\right), z_{2}=\left(a_{2}, b_{2}\right) \in \mathbb{R}^{2}$

as

$$
\begin{array}{l}
z_{1}+z_{2}=\left(a_{1}+a_{2}, b_{1}+b_{2}\right) \\
z_{1} \otimes z_{2}=\left(a_{1} a_{2}-b_{1} b_{2}, a_{1} b_{2}+a_{2} b_{1}\right)
\end{array}
$$

Then $\mathbb{C}:=\left(\mathbb{R}^{2},+, \otimes\right)$ is called the field of complex numbers.

The imaginary unit $i$ is obtained by setting $i:=(0,1) .$ The $\operatorname{law} \mathfrak{i}^{2}=-1$ then is just a direct consequence of $(2.2) .$ Furthermore, the usual notion of a complex number $z=a+i b$ is easily obtained from the identity
$$
z=(a, b)=(a, 0)+(0,1) \otimes(b, 0)
$$

The complex numbers $\mathbb{C}$, although mostly viewed as a field, comprise yet another algebraic structure. $\mathbb{C}$ contains infinitely many subfields isomorphic to $\mathbb{R}$. Choosing one also defines a real linear structure on $\mathbb{C}$. The obvious choice for that distinguished copy of $\mathbb{R}$ in $\mathbb{C}$ is given by the map
$$
\alpha: \mathbb{R} \rightarrow \mathbb{C}, \mathfrak{a} \mapsto(a, 0)
$$
For any $\lambda \in \mathbb{R}$ and any $z=(a, b) \in \mathbb{C}$ we then get
$$
\alpha(\lambda) \otimes(\mathrm{a}, \mathrm{b})=(\lambda, 0) \otimes(\mathrm{a}, \mathrm{b})=(\lambda \mathrm{a}, \lambda \mathrm{b})
$$
which turns $\mathbb{C}$ also into a real algebra. More precisely, $\mathbb{C}$ thereby becomes a real associative and commutative algebra of dimension 2 with (1,0) as identity element.

#### Definition 2.9 (The Algebra of Quaternions)

Consider the linear space $\left(\mathbb{R}^{4},+, \cdot\right)$ with standard basis $\left\{1:=\left(1_{\mathbb{R}}, 0,0,0\right), i:=\left(0,1_{\mathbb{R}}, 0,0\right), j:=\left(0,0,1_{\mathbb{R}}, 0\right), k:=\left(0,0,0,1_{\mathbb{R}}\right)\right\}$ and
define a multiplication $\otimes$ on it according to the following table

| $\otimes$ | $1$ | $\mathrm{i}$ | $\mathrm{j}$ | $\mathrm{k}$ |
|-----------|-----|--------------|--------------|--------------|
| $1$ | $1$ | $\mathrm{i}$ | $\mathrm{j}$ | $\mathrm{k}$ |
| $\mathrm{i}$ | $\mathrm{i}$ | $-1$ | $\mathrm{k}$ | $-\mathrm{j}$ |
| $\mathrm{j}$ | $\mathrm{j}$ | $-\mathrm{k}$ | $-1$ | $\mathrm{i}$ |
| $\mathrm{k}$ | $\mathrm{k}$ | $\mathrm{j}$ | $-\mathrm{i}$ | $-1$ |

Then $\mathbb{H}:=\left(\left(\mathbb{R}^{4},+, \cdot\right), \otimes\right)$ is a real associative algebra of dimension $4,$ which is called the
algebra of quaternions. Obviously, $1$ is the identity element of $\mathbb{H}$.

Any quaternion $q \in \mathbb{H}$ can be written in the form
$$
\mathrm{q}=\mathrm{q}_{0}+\mathrm{i} \mathrm{q}_{1}+\mathrm{j} \mathrm{q}_{2}+\mathrm{k} \mathrm{q}_{3}
$$
with $\mathrm{q}, \mathrm{q}_{1}, \mathrm{q}_{2}, \mathrm{q}_{3} \in \mathbb{R} .$ Analogously as in $\mathbb{C},$ the basis vectors $\{\mathfrak{i}, \mathfrak{j}, \mathrm{k}\}$ are often named
imaginary units. In particular, the following relations hold among them
$$
\mathrm{j} \mathrm{k}=-\mathrm{k} \mathrm{j}=\mathrm{i} \quad \mathrm{k} \mathrm{i}=-\mathrm{i} \mathrm{k}=\mathrm{j} \quad \mathrm{i} j=-\mathrm{j} \mathrm{i}=\mathrm{k}
$$

$(\mathbb{H},+, \otimes)$ is a skew field.

#### Definition 2.10 (Division Algebra)

An algebra $\mathcal{A}$ is called a division algebra if, for all $a \in \mathcal{A} \backslash\{0\},$ both of the following two equations
$$
\begin{array}{l}
a x=b \\
y a=b
\end{array}
$$
are uniquely solvable for all $\mathrm{b} \in \mathcal{A}$.

#### Definition 2.11 (Zero Divisor)

Let $\mathcal{A}$ be an algebra. An element a $\in \mathcal{A}$ is called zero divisor, if there exists $\mathrm{b} \in \mathcal{A} \backslash\{0\}$ such that
$$
a b=0 \text { or } b a=0
$$

#### Theorem 2.12 (Frobenius)

Any finite dimensional real associative division algebra is isomorphic to either $\mathbb{R}, \mathbb{C},$ or $\mathbb{H}$.

#### Proposition 2.13

Let $\mathcal{A}$ be a finite-dimensional algebra. Then $\mathcal{A}$ is a division algebra, if and only if, $\mathcal{A}$ is free of zero divisors.

#### Definition 2.14 (Quadratic Form)

Let X be a real linear space endowed with a scalar product, i.e. with a symmetric bilinear form,
$$
F: X \times X \rightarrow \mathbb{R},(a, b) \mapsto a \cdot b
$$
Then the map
$$
\mathrm{Q}: X \rightarrow \mathbb{R}, \mathrm{a} \mapsto \mathrm{a} \cdot \mathrm{a}
$$
is called the quadratic form of $F$. Furthermore, the pair $(X,Q)$ is called a real quadratic space.

$Q$ is uniquely determined by $F$, and vice versa, in virtue of
$$
\mathrm{F}(\mathrm{a}, \mathrm{b})=\frac{1}{2} \cdot(\mathrm{Q}(\mathrm{a}+\mathrm{b})-\mathrm{Q}(\mathrm{a})-\mathrm{Q}(\mathrm{b}))
$$
Thus, one can arbitrarily switch between $\mathrm{Q}$ and $\mathrm{F}$.

#### Proposition 2.1

Let$(\mathrm{X}, \mathrm{Q})$ be an $\mathrm{n}$-dimensional real quadratic space. Then there exists a basis $\left\{e_{1}, \ldots, e_{n}\right\}$ of $(X, Q)$ and uniquely determined $p, q, r \in\{0, \ldots, n\}$ such that, for all $i, j \in\{1, \ldots, n\},$ the following two conditions are fulfilled

(i) $\mathrm{Q}\left(e_{i}\right)=\left\{\begin{array}{cc}1, & i \leq p \\ -1, & p+1 \leq i \leq p+q \\ 0, & p+q+1 \leq i \leq p+q+r=n\end{array}\right.$
(ii) $\mathrm{Q}\left(e_{i}+e_{j}\right)-\mathrm{Q}\left(e_{i}\right)-\mathrm{Q}\left(e_{j}\right)=0$

A basis with the above properties is called an orthonormal basis of $(\mathrm{X}, \mathrm{Q}),$ and the triple $(p, q, r)$ is called the signature of $(X, Q)$.

#### Definition 2.15 (Degenerate Space)

Let $(\mathrm{X}, \mathrm{Q})$ be a finite dimensional real quadratic space. Then $(\mathrm{X}, \mathrm{Q})$ is said to be a degenerate space if
$$
\{a \in X \mid Q(a)=0\} \neq \emptyset
$$
and to be a non-degenerate space otherwise.

#### Definition 2.16 (Clifford Algebra)

Let $(\mathrm{X}, \mathrm{Q})$ be an arbitrary finite dimensional real quadratic space and let $\mathcal{A}$ be a real associative algebra with identity. Furthermore, let
$\alpha: \mathbb{R} \rightarrow \mathcal{A}$ and $v: \mathrm{X} \rightarrow \mathcal{A}$ be linear injections such that
(i) $\mathcal{A}$ is generated as an algebra by its distinct subspaces $\{v(v) \mid v \in X\}$ and $\{\alpha(a) \mid a \in \mathbb{R}\}$
(ii) $\forall v \in X:(v(v))^{2}=\alpha(Q(v))$

Then $\mathcal{A}$ is said to be a Clifford algebra for $(\mathrm{X}, \mathrm{Q})$. The elements of a Clifford algebra are
called multivectors. The product of a Clifford algebra is named geometric product. The signature of the quadratic space is also the signature of the algebra.

#### Theorem 2.17

Any Clifford algebra is isomorphic to some matrix algebra.

Since any Clifford algebra is a real associative algebra by definition, the above important theorem holds.

#### Proposition 2.18

Let$(\mathrm{X}, \mathrm{Q})$ be an $\mathrm{n}$ -dimensional real quadratic space with an orthonormal basis $\left\{e_{i} \mid 1 \leq i<n\right\} .$ Furthermore, let $\mathcal{A}$ be a real associative algebra with identity containing $\mathbb{R}$ and $X$ as distinct linear subspaces. Then $x^{2}=Q(x),$ for all $x \in X,$ if and only if
$$
\begin{aligned}
e_{i}^{2} &=Q\left(e_{i}\right) \quad \forall i \in\{1, \ldots, n\} \\
e_{i} e_{j}+e_{j} e_{i} &=0 \quad \forall i \neq j \in\{1, \ldots, n\}
\end{aligned}
$$

#### Proposition 2.19

Any commutative Clifford algebra is of dimension $\le$ 2.

#### Proposition 2.20

Let $\mathcal{A}$ be a Clifford algebra for an $n$–dimensional quadratic space $X$. Then $\dim A \le 2^n$.

#### Definition 2.21 (Universal Clifford Algebra)

A Clifford algebra of dimension $2^n$ is called universal.

#### Definition 2.22 (Standard Quadratic Space)

For any $\mathrm{p}, \mathrm{q}, \mathrm{r} \in\{0, \ldots, \mathrm{n}\}$ define the following scalar product
$$
\mathrm{F}: \mathbb{R}^{p+q+r} \times \mathbb{R}^{p+q+r} \rightarrow \mathbb{R},(a, b) \mapsto \sum_{i=1}^{p} a_{i} b_{i}-\sum_{p+1}^{q} a_{i} b_{i}
$$
Then the corresponding standard quadratic space $\left(\mathbb{R}^{p+q+r}, Q\right)$ is denoted by $\mathbb{R}^{p, q, r}$.

#### Theorem 2.23

For any quadratic space $\mathbb{R}^{p, q, r}$, there exists a unique universal Clifford algebra. This algebra shall be denoted by $\mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r},}$ and its geometric product by $\otimes_{p, q, r}$

#### Subspace Grading

Let
$$
\mathcal{I}:=\left\{\left\{\mathfrak{i}_{1}, \ldots, i_{s}\right\} \in \mathcal{P}(\{1, \ldots, n\}) \mid 1 \leq \mathfrak{i}_{1} \leq \ldots \leq \mathfrak{i}_{s} \leq \mathfrak{n}\right\}
$$
denote the set of all naturally ordered subsets of the power set $\mathcal{P}(\{1, \cdots, n\}) .$ Furthermore, let $\left(e_{1}, \cdots, e_{n}\right)$ be an orthogonal basis of $\mathbb{R}^{p, q, r} .$ Now define, for all $I \in \mathcal{I}$ $e_{\mathrm{I}}$ to be the product
$$
e_{\mathrm{I}}:=e_{i_{1}} \ldots e_{i_{s}}
$$
In particular, let $e_{\emptyset}$ be identified with 1.

#### Proposition 2.24

Let $\left(e_{1}, \cdots, e_{n}\right)$ be an orthogonal basis of $\mathbb{R}^{p, q}, r$. Then
$$
\left\{e_{I} \mid I \in \mathcal{I}\right\}
$$

with $\mathcal{I}$ defined according to $(2.17)$ is a basis of the Clifford algebra $\mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r}}$. In particular
any multivector in $\mathcal{C}_{\mathrm{p}, \text { q,r }}$ can be written as
$$
x=\sum_{\mathrm{I} \in \mathcal{I}} x_{\mathrm{I}} e_{\mathrm{I}}
$$
whereby all $x_{1} \in \mathbb{R}$.

#### Definition 2.25 (K-Vector Part)

Let $\left(e_{1}, \cdots, e_{n}\right)$ be an orthogonal basis of $\mathbb{R}^{p, q, r} .$ For
$$
\begin{array}{l}
\text { every } \mathrm{k} \in\{0, \cdots, \mathrm{n}\} \text { the set } \\
\qquad\left\{e_{\mathrm{I}}\left|e_{\mathrm{I}} \in \mathcal{I},\right| \mathrm{I} \mid=\mathrm{k}\right\}
\end{array}
$$
spans a linear subspace of $\mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r}} .$ This linear subspace, denoted by $\mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r}}^{\mathrm{k}},$ is called the $\mathrm{k}-$
vector part of $\mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r}}$
From the above definition we get
$$
\mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r}}=\sum_{\mathrm{k}=0}^{\mathrm{n}} \mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r}}^{\mathrm{k}}
$$
We also obtain, in particular, $\mathcal{C}_{p, q, r}^{0}=\mathbb{R}$ and $\mathcal{C}_{p, q, r}^{1}=\mathbb{R}^{p, q, r} .$ Any subspace $\mathcal{C}_{p, q, r}^{k}$ is of dimension $\left(\begin{array}{l}n \\ k\end{array}\right) .$ Thus, a Clifford algebra can also be seen as an algebra of subspaces. All subspaces of even dimension form a subalgebra of $\mathcal{C}_{\mathrm{p}, \mathrm{q}, r}$.

#### Proposition 2.26

The subspace sum given by
$$
\mathcal{C}_{\mathrm{p}, \mathrm{q}, r}^{+}:=\sum_{\mathrm{k}=0 \atop \mathrm{k} \text { even }}^{\mathrm{n}} \mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r}}^{\mathrm{k}}
$$
is a subalgebra of $\mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r}}$ of dimension $2^{\mathrm{n}-1},$ which is called the even subalgebra of $\mathcal{C}_{\mathrm{p}, \mathrm{q}, \mathrm{r}}$.

#### Definition 2.27 (Grade Operator)

Define the following grade operator
$$
<\cdot>_{\mathrm{k}}: C_{\mathrm{p}, \mathrm{q}, \mathrm{r}} \rightarrow C_{\mathrm{p}, \mathrm{q}, \mathrm{r}}, \mathrm{x} \mapsto \sum_{\mathrm{I} \in \mathcal{I} \atop|\mathrm{I}|=\mathrm{k}} x_{\mathrm{I}} e_{\mathrm{I}}
$$
for any $\mathrm{k} \in\{0, \cdots, n\}$.

Using the grade operator any multivector can be written as
$$
x=\sum_{k=0}^{n}<x>_{k}
$$


### Clifford 1882

> Source: 14.1 Clifford's original defintion in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

Grassmann's exterior algebra $\wedge \mathbb{R}^{n}$ of the linear space $\mathbb{R}^{n}$ is an associative algebra of dimension $2^{n} .$ In terms of a basis $\left\{\mathbf{e}_{1}, \mathbf{e}_{2}, \ldots, \mathbf{e}_{n}\right\}$ for $\mathbb{R}^{n}$ the exterior algebra $\wedge \mathbb{R}^{n}$ has a basis

$$

\begin{array}{l}
1 \\
\mathbf{e}_{1}, \mathbf{e}_{2}, \ldots, \mathbf{e}_{n} \\
\mathbf{e}_{1} \wedge \mathbf{e}_{2}, \mathbf{e}_{1} \wedge \mathbf{e}_{3}, \ldots, \mathbf{e}_{1} \wedge \mathbf{e}_{n}, \mathbf{e}_{2} \wedge \mathbf{e}_{3}, \ldots, \mathbf{e}_{n-1} \wedge \mathbf{e}_{n} \\
\vdots \\
\mathbf{e}_{1} \wedge \mathbf{e}_{2} \wedge \ldots \wedge \mathbf{e}_{n}
\end{array}
$$

The exterior algebra has a unity 1 and satisfies the multiplication rules
$$
\begin{array}{l}
\mathbf{e}_{i} \wedge \mathbf{e}_{j}=-\mathbf{e}_{j} \wedge \mathbf{e}_{i} \quad \text { for } \quad i \neq j \\
\mathbf{e}_{i} \wedge \mathbf{e}_{i}=0
\end{array}
$$
Clifford 1882 kept the first rule but altered the second rule, and arrived at the multiplication rules
$$
\begin{array}{l}
\mathbf{e}_{i} \mathbf{e}_{j}=-\mathbf{e}_{j} \mathbf{e}_{i} \quad \text { for } \quad i \neq j \\
\mathbf{e}_{i} \mathbf{e}_{i}=1
\end{array}
$$
This time $\left\{\mathbf{e}_{1}, \mathbf{e}_{2}, \ldots, \mathbf{e}_{n}\right\}$ is an orthonormal basis for the positive definite Euclidean space $\mathbb{R}^{n} .$ An associative algebra of dimension $2^{n}$ so defined is the Clifford algebra $\mathcal{C} \ell_{n}$.

### Basis-free version of Clifford's definition

> Source: 14.2 Basis-free version of Clifford's definition in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

Here we consider as an example the exterior algebra $\wedge \mathbb{R}^{4}$ of the 4 -dimensional real linear space $\mathbb{R}^{4}$. Provide the linear space $\mathbb{R}^{4}$ with a quadratic form
$$
Q(\mathbf{x})=x_{0}^{2}-x_{1}^{2}-x_{2}^{2}-x_{3}^{2}
$$
and associate to $Q$ the symmetric bilinear form
$$
\langle\mathbf{x}, \mathbf{y}\rangle=\frac{1}{2}[Q(\mathbf{x}+\mathbf{y})-Q(\mathbf{x})-Q(\mathbf{y})]
$$
This makes $\mathbb{R}^{4}$ isometric with the Minkowski space-time $\mathbb{R}^{1,3}$. Then define the left contraction $u \mathrm{J} v \in \wedge \mathbb{R}^{1,3}$ by
(a) $\mathbf{x}\rfloor\mathbf{y}=\langle\mathbf{x}, \mathbf{y}\rangle$
(b) $\mathbf{x}\rfloor(u \wedge v)=(\mathbf{x}\rfloor u) \wedge v + \hat{u} \wedge(\mathbf{x} \rfloor v)$
(c) $(u \wedge v)\rfloor w=u\rfloor(v \perp w)$

for $\mathbf{x}, \mathbf{y} \in \mathbb{R}^{1,3}$ and $u, v, w \in \wedge \mathbb{R}^{1,3}$, where $\hat{u}$ is the grade involute of $u \in \bigwedge V$, defined for a k-vector $u \in \bigwedge^k V$ by $\hat{u} = (-1)^k u$

The identity (b) says that $x$ operates like a derivation and the identity (c) makes $\bigwedge \mathbb{R}^{1,3}$ a left module over $\bigwedge \mathbb{R}^{1,3}$ Then introduce the Clifford product of $\mathbf{x} \in \mathbb{R}^{1,3}$ and $u \in \bigwedge \mathbb{R}^{1,3}$ by the formula
$$
\mathbf{x} u = \mathbf{x} \rfloor u + \mathbf{x} \wedge u
$$

and extend this product by linearity and associativity to all of $\bigwedge \mathbb{R}^{1,3}$. Provided with the Clifford product (the linear space underlying) the exterior algebra $\bigwedge \mathbb{R}^{1,3}$ becomes the Clifford algebra $\mathcal{C} \ell_{1,3}$

#### Definition by generators and relations

> Source: 14.3 Definition by generators and relations in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

The following definition is favored by physicists. It is suitable for non-degenerate quadratic forms, especially the real quadratic spaces $\mathbb{R}^{p, q}$.

Definition. An associative algebra over $\mathbb{F}$ with unity 1 is the Clifford algebra $\mathcal{C} \ell(Q)$ of a non-degenerate $Q$ on $V$ if it contains $V$ and $\mathbb{F}=\mathbb{F} \cdot 1$ as distinct subspaces so that
(1) $\mathbf{x}^{2}=Q(\mathbf{x})$ for any $\mathbf{x} \in V$
(2) $V$ generates $\mathcal{C} \ell(Q)$ as an algebra over $\mathbb{F}$
(3) $\mathcal{C} \ell(Q)$ is not generated by any proper subspace of $V$

#### Universal object of quadratic algebras

> Source: 14.4 Universal object of quadratic algebras in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

The Clifford algebra $\mathcal{C} \ell(Q)$ is the universal associative algebra over $\mathbb{F}$ generated by $V$ with the relations $\mathbf{x}^{2}=Q(\mathbf{x}), \mathbf{x} \in V$

Let $Q$ be the quadratic form on a linear space $V$ over a field $\mathbb{F}$, and let $A$ be an associative algebra over $\mathbb{F}$ with unity $1_{A} .$ A linear mapping $V \rightarrow A$, $\mathbf{x} \rightarrow \varphi_{\mathbf{x}}$ such that
$$
\left(\varphi_{x}\right)^{2}=Q(x) \cdot 1_{A} \quad \text { for all } x \in V
$$
is called a Clifford map.

The subalgebra of $A$ generated by $\mathbb{F}=\mathbb{F} \cdot 1_{A}$ and $V$ (or more precisely by the images of $\mathbb{F}$ and $V$ in $A$ ) will be called a quadratic algebra.

The Clifford algebra $\mathcal{C} \ell(Q)$ is a quadratic algebra with a Clifford $\operatorname{map} V \rightarrow \mathcal{C} \ell(Q), \quad \mathbf{x} \rightarrow \gamma_{\mathbf{x}}$ such that for any Clifford map $\varphi: V \rightarrow A$ there
exists a unique algebra homomorphism $\psi: \mathcal{C} \ell(Q) \rightarrow A$ making the following diagram commutative:
$$
\begin{array}{c}
V \stackrel{\gamma}{\longrightarrow} \mathcal{C} \ell(Q) \\
\varphi \searrow \quad \downarrow \psi \\
\quad A
\end{array} \quad \varphi_{\mathbf{x}}=\psi\left(\gamma_{\mathbf{x}}\right)
$$
This definition says that all Clifford maps may be obtained from $\gamma: V \rightarrow \mathcal{C} \ell(Q)$ which is thereby universal.

#### Clifford algebra as a quotient of the tensor algebra

> Source: 14.5 Clifford algebra as a quotient of the tensor algebra in **Clifford Algebra in Clifford Algebras and Spinors** by P. Lounesto

Chevalley 1954 p. 37 constructs the Clifford algebra $\mathcal{C} \ell(Q)$ as the quotient algebra $\otimes V / I(Q)$ of the tensor algebra $\otimes V$ with respect to the two-sided ideal $I(Q)$ generated by the elements $\mathbf{x} \otimes \mathbf{x}-Q(\mathbf{x})$ where $\mathbf{x} \in V .$ See also $N .$ Bourbaki 1959 p. 139 and $T . Y .$ Lam 1973 p. $103 .$ The tensor algebra approach gives a proof of existence by construction - suitable for an algebraist who is interested in rapid access to the main properties of Clifford algebras over commutative rings.

In characteristic zero we may avoid quotient structures by making the exterior algebra $\bigwedge V$ concrete as the subspace of antisymmetric tensors in $\otimes V .$ For example, if $\mathbf{x}, \mathbf{y} \in V,$ then $\mathbf{x} \wedge \mathbf{y}=\frac{1}{2}(\mathbf{x} \otimes \mathbf{y}-\mathbf{y} \otimes \mathbf{x}) \in \bigwedge^{2} V .$

More generally, a simple $k$ -vector $\mathbf{x}_{1} \wedge \mathbf{x}_{2} \wedge \ldots \wedge \mathbf{x}_{k}$ is identified with
$$
Alt\left(\mathbf{x}_{1} \otimes \mathbf{x}_{2} \otimes \ldots \otimes \mathbf{x}_{k}\right)=\frac{1}{k !} \sum_{\pi} \operatorname{sign}(\pi) \mathbf{x}_{\pi(1)} \otimes \mathbf{x}_{\pi(2)} \otimes \ldots \otimes \mathbf{x}_{\pi(k)}
$$
where the linear operator $Alt: \otimes V \rightarrow \wedge V$, called alternation, is a projection operator $Alt(\bigotimes V)=\bigwedge V$ satisfying $u \wedge v=Alt(u \otimes v)$.

Similarly, we may obtain an isomorphism of linear spaces $\wedge V \rightarrow \mathcal{C} \ell(Q)$ by identifying simple $k$ -vectors with antisymmetrized Clifford products

$$
\mathbf{x}_{1} \wedge \mathbf{x}_{2} \wedge \ldots \wedge \mathbf{x}_{k} \rightarrow \mathbf{x}_{1} \dot{\wedge} \mathbf{x}_{2} \dot{\wedge} \ldots \dot{\wedge} \mathbf{x}_{k}=\frac{1}{k !} \sum_{\pi} \operatorname{sign}(\pi) \mathbf{x}_{\pi(1)} \mathbf{x}_{\pi(2)} \ldots \mathbf{x}_{\pi(k)}
$$

thus splitting the Clifford algebra $\mathcal{C} \ell(Q)$ into fixed subspaces of $k$ -vectors $\bigwedge^{k} V \subset \mathcal{C} \ell(Q)$. Any orthogonal basis $\mathbf{e}_{1}, \mathbf{e}_{2}, \ldots, \mathbf{e}_{n}$ of $V$ gives a correspon-
dence
$$
\mathbf{e}_{i_{1}} \wedge \mathbf{e}_{i_{2}} \wedge \ldots \wedge \mathbf{e}_{i_{k}} \rightarrow \mathbf{e}_{i_{1}} \dot{\wedge} \mathbf{e}_{i_{2}} \dot{\wedge} \ldots \dot{\wedge} \mathbf{e}_{i_{k}}=\mathbf{e}_{i_{1}} \mathbf{e}_{i_{2}} \ldots \mathbf{e}_{i_{k}}
$$
of bases for $\wedge V$ and $\mathcal{C} \ell(Q)$
