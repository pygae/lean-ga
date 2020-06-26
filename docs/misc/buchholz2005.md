> This file can be previewed with rendered mathematical formulas [here](https://stackedit.io/viewer#!url=https://raw.githubusercontent.com/pygae/lean-ga/master/docs/misc/buchholz2005.md).

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

Let $\mathcal{A}$ be a Clifford algebra for an $n$â€“dimensional quadratic space $X$. Then $\dim A \le 2^n$.

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