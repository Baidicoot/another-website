---
title: The λ-Calculus, in Set Theory, in Coq
---

# The $\lambda$-Calculus, in Set Theory, in Coq

I've recently been reading about [Peter Aczel's interpretation](https://www.jstor.org/stable/27588436?seq=1) of 'Constructive Zermelo-Fraenkel Set Theory' (CZF) in [Martin-Löfs Type Theory](https://en.wikipedia.org/wiki/Intuitionistic_type_theory) (MLTT). This got me thinking about the inverse interpretation; how would one go about creating a model for a simple type theory within a set theory like CZF? I resolved to experiment with constructing models of various logics in set theory; however, to do this, I first needed a set theory to experiment *in*.

### Axiomatic Set Theory

CZF is an 'axiomatic' set theory, meaning that one may only 'construct' sets by using the particular rules, called axioms, which make up the theory. The reason for this is twofold; firstly, the axiomisation of the set theory avoids the possibility of subtle inconsistencies which can invalidate proofs - the commonly-cited example is [Russell's paradox](https://en.wikipedia.org/wiki/Russell%27s_paradox).

Secondly, we can limit the axioms of our system to those that are _constructive_, meaning that each axiom (abstractly) represents a 'computation' or 'algorithm' of some sort; such a system of axioms is called a constructive theory. This has the interesting property that proofs in constructive theories can be thought of as descriptions of computations: for example, a proof of $A \to B$ can be thought of as an algorithm for constructing a proof of $B$ given a proof of $A$.

Using non-constructive theories, such as [Zermelo-Fraenkel Set Theory](https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory) (ZF), mathematicians can prove results which seem counterintuitive, such as the [Banach-Tarski paradox](https://en.wikipedia.org/wiki/Banach%E2%80%93Tarski_paradox) (which relies on the non-constructive 'axiom of choice'). The distinction between constructive and non-constructive axioms and theories is mostly philosophical, as some non-constructive axioms (such as the law of the excluded middle or the powerset) may seem perfectly intuitive on the surface.

Most set theories are but an extension of an 'underlying language' of [logic](https://en.wikipedia.org/wiki/First-order_logic) (classical logic for ZF, intuonistic logic for CZF) with the aforementioned axioms for set construction. This underlying language usually includes the normal logical operators and quantifiers, and a statement in this language is called a _predicate_. Luckily for us, many logics have already been implemented as programs for computers. This means we need not check our proofs manually; the program automatically checks the soundness of our reasoning for us!

These systems are called 'automated theorem provers' and are quite a mature technology; I will extend one, [Coq](https://coq.inria.fr/), with axioms for the construction of sets. The actual set theory I will use is called 'Intuonistic Zermelo-Fraenkel Set Theory'; as the name suggests, it is similar to CZF, but is slightly 'less' constructive. It admits the following axioms:

- The 'axiom of extensional equality'. This says that if all the members of two sets are shared, then the two sets are equal.
- The 'axiom of the union set'. This says that if $x$ is a set, then the union of $x$ (written as `⋃x` in Coq) is also a set.
- The 'axiom of the empty set'. This says that there is a set with no elements, which I write as $\emptyset$ or `∅` in Coq.
- The 'axiom of the pair'; if $a$ and $b$ are sets, then $\{a, b\}$ is a set. When used in conjunction with the above two axioms, this means that we can write sets by listing their elements.
- The 'axiom of infinity'. Commonly used as a 'superset' of the natural numbers, this is a set $\infty$ such that if $\emptyset \in \infty$ and if $x \in \infty$, then $\mathrm{Suc}(x) \in \infty$, where $\mathrm{Suc}(x) = \bigcup \{x, \{x\}\}$.
- The 'axiom of separation'. If $x$ is a set, then we can construct a new set $y$ of all the members $a \in x$ such that $\phi(x)$ holds for some property $\phi$. Informally, this is commonly written $\{a \in x : \phi(x)\}$, but I also use $\{a : \forall a \in x, \phi(x)\}$.
- The 'axiom of replacement'. This is similar to the above axiom, except instead of selecting the members of $x$ that satisfy some property, we construct a new set of all the $f(a)$ where $a \in x$, for some _functional predicate_ $f$ (such a predicate is a property $\phi(x,y)$ where for all $x$, a $y$ exists; we write this $y$ as $f(x)$). I write this $\{f(a) : \forall a \in x\}$.
- The 'axiom of the powerset'. This states that for all $x$, there is a set $\mathcal{P}(x)$ consisting of the subsets of $x$. This axiom is non-constructive as there is no algorithm that (even given an infinite amount of time) can produce all the subsets of any _infinite_ set; this is an immediate consequence of Cantor's diagonalization theorem.
- The 'axiom of $\in$-induction'. This is essentially [well-founded induction](https://en.wikipedia.org/wiki/Well-founded_relation#Induction_and_recursion) on the $\in$ relation; if a property holding of all $a \in x$ implies that the property holds of $x$, then the property holds of all sets.

I describe the process of creating a _model_ (an 'encoding') for this set theory in Coq in [addendum I](extra.html#addendum_1). You can view the _axiomisation_ of IZF in Coq [here](src/IZF.v.html).

Somewhat amazingly, using only these axioms, one is able to 'construct' much of modern mathematics, as we shall soon see!

### Set-Theoretic Constructions
As a first example construction, let us consider the Cartesian product of two sets $A \times B$. For any sets $A$ and $B$, $A \times B$ should have the property that for any $x \in A$ and $y \in B$, $\langle x, y \rangle \in A \times B$, where $\langle x, y \rangle$ denotes the ordered pair of $x$ and $y$, constructed in the usual way as $\{\{x\}, \{x, y\}\}$.

For a given $x \in A$, we can construct the set $\{\langle x, y \rangle : \forall y \in B\}$ by the axiom of replacement and a predicate $\phi(y,z)$ defined as $z = \langle x, y \rangle$. Clearly, this predicate is functional. Call this process $f(x)$, and we can then apply replacement *again*, this time using $f$, to generate the indexed set $(z_x)_{x \in A}$. Taking $\bigcup_{x \in A}z_x$, and we have the Cartesian product $A \times B$:

```coq
Definition cartesian_product (A B: set) :=
  ⋃(replacement (fun x (_: x ∈ A) => replacement (fun y (_: y ∈ B) => ⟨x,y⟩))).

Notation "A × B" := (cartesian_product A B) (at level 60, right associativity).
Lemma is_cartesian_product : forall A B x y, x ∈ A -> y ∈ B -> ⟨x,y⟩ ∈ A × B.
```

The disjoint union, or coproduct, of an indexed set $(x_i)_{i \in I}$ is the union of $(x_i)$, except every element is 'tagged' with the index of the set from which it came, meaning that for a $y \in x_j$ for some $j \in I$, then $\langle j, y \rangle \in \bigsqcup_{i \in I} x_i$, where $\bigsqcup$ is the disjoint union operation.

The disjoint union of a set $(x_i)_{i \in I}$ can be constructed using the axioms of IZF, by taking the replacement of $(x_i)$ with, given a $j \in I$, the replacement of $x_j$ with $\langle j, y \rangle$ for a given $y \in x_j$, and finding the union of the resultant set. In set notation, this is $\bigcup\{\{\langle j, y \rangle : \forall y \in x_j\} : \forall j \in I\}$, which is easily converted to Coq:

```coq
Definition disjoint_union {I} (f: forall j, j ∈ I -> set) :=
  ⋃(replacement (fun j p => replacement (fun y (_: y ∈ f j p)  => ⟨j,y⟩))).

Lemma is_disjoint_union :
  forall {S f x y}
         (p: x ∈ S),
         y ∈ f x p -> ⟨x,y⟩ ∈ disjoint_union f.
```

That derivation is almost identical to our derivation for the Cartesian product! In fact, the Cartesian product is *definitionally equal* to the case of the disjoint union where $x_i$ is always $B$ for any $i \in A$:

```coq
Lemma cartesian_product_is_extreme_disjoint_union :
  forall {A B}, A × B ≡ disjoint_union (fun x (_: x ∈ A) => B).
Proof.
  intros. reflexivity.
Qed.
```

This is a pretty good example of how a constructive approach can allow you to discover nuances about the properties of operations that would remain undiscovered otherwise.

We can also define a binary version of the union and disjoint union operations:

```coq
Definition union2 x y :=
  ⋃(x +> (y +> ∅)).
Notation "x ∪ y" := (union2 x y) (at level 60).

Lemma union2_prop : forall {A B x},
  x ∈ A ∪ B <-> x ∈ A \/ x ∈ B.

Definition left x := ⟨∅,x⟩.
Definition right x := ⟨Suc ∅,x⟩.

Definition disjoint_union2 x y.
Notation "x + y" := (disjoint_union2 x y) (at level 60).

Lemma disjoint_union2_prop : forall {A B x},
  x ∈ A + B <-> (exists a, x ≡ left a /\ a ∈ A) \/ (exists b, x ≡ right b /\ b ∈ B).
```

We can derive a stronger form of our axiom of infinity by separating out the elements of $\infty$ that satisfy the _inductive property_. The inductive property, which is written $\mathrm{Ind}(x)$, says that 'if $\phi(\emptyset)$ and for all $\phi(a)$ we can derive $\phi(\mathrm{Suc}(a))$, then we can derive $\phi(x)$ for any property $\phi$':

$$
\mathrm{Ind}(x) = \forall \phi, (\phi(\emptyset) \wedge \forall a, \phi(a) \to \phi(\mathrm{Suc}(a))) \to \phi(x)
$$

If for any $x$ we have $\mathrm{Ind}(x)$, then we say that $x$ is in the _standard model_ of arithmetic - this is pretty much the same as saying $x$ can be expressed by repeating the $\mathrm{Suc}$ operation over the empty set a finite number of times.

It is important to note that the inductive property cannot be written in 'first-order' logic where only quantification over sets is allowed; in order to express the inductive property correctly, we _must_ quantify over all propositional functions $\phi$, which requires '[second-order](https://en.wikipedia.org/wiki/Second-order_logic)' logic. It is possible to _construct_ the standard model of arithmetic in ZF using only first-order logic, but not express the inductive property in it.

We can construct the standard model of arithmetic (which we call $\omega$) by selecting the elements $x \in \infty$ that have the inductive property:

$$
\omega = \{x : \forall x \in \infty, \mathrm{Ind}(x)\}
$$

As, by definition, all elements of $\omega$ have the inductive property, we can prove that one can perform mathematical induction over $\omega$ itself; if, for any property $\phi$, both $\phi(\emptyset)$ and $\forall n, \phi(n) \to \phi(\mathrm{Suc}(n))$ hold, then $\phi(x)$ holds for all $x \in \omega$. This makes $\omega$ so useful for further constructions that it is sometimes even stated axiomatically, as the axiom of _strong infinity_:

$$
\exists \omega, \forall \phi, \phi(\emptyset) \wedge (\forall n, \phi(n) \to \phi(\mathrm{Suc}(n))) \to \forall x \in \omega, \phi(x)
$$

The exponential set $A^B$, of functions $f : B \to A$ has a pretty obvious construction; all functions $B \to A$ are subsets of $B \times A$, and so to construct $A^B$ we can simply restrict $\mathcal{P}(B \times A)$ to only those subsets $R$ which are *functional* (for all $x \in B$, if $\langle x, y \rangle \in R$ for a $y \in A$, then $y$ is unique) and *left-total* (for all $x \in B$, there exists a $y \in A$ such that $\langle x, y \rangle \in R$), using separation:

```coq
Definition functional (R: set) :=
  forall {a b}, ⟨a,b⟩ ∈ R -> forall {c}, ⟨a,c⟩ ∈ R -> b ≡ c.

Definition left_total (R D: set) :=
  forall {a}, a ∈ D -> exists {b}, ⟨a,b⟩ ∈ R.

Definition exponential (A B: set) :=
  separation (fun R => functional R /\ left_total R B) (powerset (B × A)).

Lemma member_exp_function :
  forall {A B R}, R ∈ exponential A B -> functional R /\ left_total R B.
```

From the exponential set and the principle of $\in$-induction, we can actually derive some useful and surprising tools for constructing more complex sets, such as the principle of $\in$-_recursion_. The principle of $\in$-recursion states, that for every formula of the underlying language $\phi(x,y)$ such that $\forall x, \exists ! y, \phi(x,y)$, then there exists a formula $\chi(x,y)$ such that $\chi(x,y) \leftrightarrow \phi(\{b : a \in x \wedge \chi(a,b)\},y)$. Expressed as a function, this can be written as:

$$
\forall G, \exists F, F(x) = G(\{F(y) : y \in x\})
$$

However, in order to prove $\in$-recursion, we must first prove that the 'transitive closure' of any set $x$ is itself a set. The transitive closure of any set, $TC(x)$, is defined by the properties $\forall y \in x, y \in TC(x)$ and $\forall y \in TC(x), \forall z \in y, z \in TC(x)$ - that is, if for any $z$ and $x$ there is a chain of the form $z \in ... \in x$, then $z \in TC(x)$. Notice that $x \subset TC(x)$. This is provable inside our model using $\in$-induction and collection:

```coq
Lemma TC : forall x, exists TCx,
  (forall y, y ∈ x -> y ∈ TCx)
  /\ (forall y, y ∈ TCx -> forall z, z ∈ y -> z ∈ TCx).
```

Using the transitive closure, we can prove the existence of $\in$-recursion as follows:

For any formula $\phi(x,y)$ such that $\forall x, \exists ! y \in Y, \phi(x,y)$, and a set $X$ which we are recursing over, consider elements of the set:

$$
\{F \in Y^{TC(X)} : \forall x \in TC(X), \phi(\{F(a) : a \in x\},F(x))\}
$$

Call this set $\mathbb{F}$. We can prove that $\mathbb{F}$ contains a _unique_ element, meaning that $\forall f g \in \mathbb{F}, \forall x \in TC(X), f(x) = g(x)$, by $\in$-induction over $x$. In the inductive case, we need to prove that $f(a) = g(a)$ given $\forall b \in a, f(b) = g(b)$. From this, it is obvious that $\{f(b) : b \in a\} = \{g(b) : b \in a\}$. As $\phi$ relates this to a _unique_ set $c$, then $f(a) = c = g(a)$.

Taking $f = \bigcup \mathbb{F}$, by the uniqueness property above, $f$ will be the function we want, provided we can prove that $\mathbb{F}$ is inhabited. $\mathrm{dom}(f) = \emptyset$ iff $\mathbb{F}$ is uninhabited, so proving $TC(X) \subseteq \mathrm{dom}(f)$ suffices. Once again, $\in$-induction comes to our aid! Using the predicate $\forall v \in TC(X) \to \exists w, \langle v,w \rangle \in f$, the inductive case becomes:

$$
\forall a, (\forall b \in a, b \in TC(X) \to \exists c, \langle b, c \rangle \in f) \to a \in TC(X) \to \exists d, \langle a, d \rangle \in f
$$

The assumption $a \in TC(X)$ proves that $\forall b \in a, b \in TC(X)$ by the property of the transitive closure. Therefore, we can use replacement to construct the set $\{f(b) : b \in a\}$, for which there exists a unique set $d$ such that $\phi(\{f(b) : b \in a\},d)$. By the construction of $f$, $f(a)$ is exactly the set $d$, and so $\langle a,d \rangle \in f$. From this, $\forall v \in TC(X) \to \exists w, \langle v,w \rangle \in f$, i.e. $TC(x) \subseteq \mathrm{dom}(f)$, thereby proving the existence of $f$ - for a given $X$. Whenever we use $\in$-recursion over a set $S$, we can just set $X = S$, meaning we can safely ignore the added complexity of $X$ from now on.

Formalizing the reasoning above is somewhat out of the scope of this project, so I just add an axiom implementing the functionality of $\in$-recursion:

```coq
Axiom ϵ_rec : (forall x, (forall y, y ∈ x -> set) -> set) -> set -> set.
Axiom ϵ_rec_prop : forall {F x},
  ϵ_rec F x ≡ F x (fun y _ => ϵ_rec F y).
```

This is the last axiom I will add to the system; everything else is derived from the Coq model described in [addendum I](extra.html#addendum_1).

### Inductively Defined Sets

We now have enough theory to begin constructing some interesting sets!

A set is 'inductively defined' if all members of the set can be _finitely_ described in terms of operations on other members of that set - a classic example is the set of natural numbers:

- $0$ is a natural number
- $n+1$ is a natural number if $n$ is a natural number

You can see that the set of $\lambda$-calculus terms is also inductively defined - each term is either a constant or 'base case' ($0$ for the natural numbers, or variables for $\lambda$-terms) or a composition of terms already in the set ($n+1$ in the example above, abstraction and application for $\lambda$-terms). We can formalise this notion of inductive definability by introducing the concept of a 'description' of an inductively defined set.

The description of a set $X$ is a class function $\Gamma$ such that $X$ is the 'least fixed point' of $\Gamma$ - that is, $X$ is the _smallest_ set such that $\Gamma(X) = X$.

As an example, consider $\Gamma_\mathbb{N}(X) = X + 1$, the description of the natural numbers. If $1$ is the set containing the single element $\bullet$, then the least fixed point of $\Gamma_\mathbb{N}$ must contain $\mathrm{right}(\bullet)$; repeating this process, we see that it must also contain $\mathrm{left}(\mathrm{right}(\bullet))$, as well as $\mathrm{left}(\mathrm{left}(\mathrm{right}(\bullet)))$, and so on. If we define $0$ as $\mathrm{right}(\bullet)$ and $n+1$ as $\mathrm{left}(n)$, then the similarities with the inductive definition we gave above become clear.

It is often possible to gain an understanding of what the least fixed point of a given set will 'look' like by looking at its description. If we consider only 'polynomial' descriptions - descriptions in the form $a + b \times x + c \times x \times x + \dots$, where $a,b,c,\dots$ are independent of $X$ - then each term of the polynomial - $a \times x^n$ - is an operation combining $n$ other elements of $x$ (and an element of $a$) to construct a new element of $x$. When $n = 0$, the 'operations' are constant; these are the base cases of the inductive definition.

For example, we can write the description for the terms of the $\lambda$-calculus as $\Gamma_\lambda(X) = \mathrm{vars} + \mathrm{vars} \times X + X \times X$, given a set of variables $\mathrm{vars}$. The constant term $\mathrm{vars}$ is the base case - we can construct a $\lambda$-term from a variable. The second term states that we can construct a $\lambda$-term from another $\lambda$-term _and_ a variable - this is the abstraction $(\lambda v. M)$. Finally, with two $\lambda$-terms - $X \times X$ - we can construct $(M N)$, which is itself a $\lambda$-term.

We can 'isolate' the base cases of any polynomial $\Gamma$ by taking $\Gamma(\emptyset)$; any other varying term must be in the form $a \times \emptyset^n$ for $n > 0$. Since $\emptyset$ has no members, then the Cartesian product of any set with $\emptyset$ must also have no members. As these constant terms are always 'included' in $\Gamma(X)$ for all $X$, we have $\Gamma(\emptyset) \subseteq \Gamma(X)$. We can use this property to algorithmically construct the least fixed point for $\Gamma$.

The least fixed point of any $\Gamma$ should contain all base cases - $\Gamma(\emptyset)$ - all terms constructed from the base cases - $\Gamma(\Gamma(\emptyset))$ - and so on. This gives us a candidate for the least fixed point $\emptyset \cup \Gamma(\emptyset) \cup \Gamma(\Gamma(\emptyset)) \cup \dots$, alternatively expressed as $\bigcup_{i=0}^\infty \Gamma^i(\emptyset)$. In order to prove that this actually is a fixed point of $\Gamma$, we need to prove:

$$
\Gamma(\bigcup_{i=0}^\infty \Gamma^i(\emptyset)) = \bigcup_{i=0}^\infty \Gamma^i(\emptyset)
$$

The two operators used in polynomial descriptions are both distributive over the binary union operator, meaning that $a \times (b \cup c) = (a \times b) \cup (a \times c)$ and $a + (b \cup c) = (a + b) \cup (a + c)$. This in turn means that polynomial equations are distributive over the binary union: $\Gamma(a \cup b) = \Gamma(a) \cup \Gamma(b)$. We now have:

$$
\Gamma(\bigcup_{i=0}^\infty \Gamma^i(\emptyset)) = \bigcup_{i=0}^\infty \Gamma(\Gamma^i(\emptyset)) = \bigcup_{i=1}^\infty \Gamma^i(\emptyset)
$$

The property that $\Gamma(\emptyset) \subseteq \Gamma(X)$ for all $X$ means that $\Gamma(\emptyset) \cup \Gamma(X) = \Gamma(X)$; this applies to the case above as well:

$$
\Gamma(\bigcup_{i=0}^\infty \Gamma^i(\emptyset)) = \Gamma(\emptyset) \cup \bigcup_{i=1}^\infty \Gamma^i(\emptyset) = \bigcup_{i=0}^\infty \Gamma^i(\emptyset)
$$

We can use $\in$-recursion to construct infinite sets like $\Gamma(\emptyset) \cup \Gamma(\Gamma(\emptyset)) \cup \dots$. I define a function `ϵ_iter` to iterate a function $\Gamma$ over a set recursively:

```coq
Definition ϵ_iter Γ := ϵ_rec (fun _ f => ⋃(replacement (fun x H => Γ(f x H)))).

Lemma ϵ_iter_prop : forall {Γ X},
  ϵ_iter Γ X = ⋃ (replacement (fun Y _ => Γ (ϵ_iter Γ Y))).
```

We can then define the least fixed point of any polynomial as that polynomial iterated over $\omega$. As $\omega$ contains arbitrarily-nested sets, then `ϵ_iter Γ ω` must contain arbitrary iterations of $\Gamma$. We can, for instance, use this to construct naturals and binary trees (trees where every non-leaf node has two children).

```coq
Definition lfp Γ := ϵ_iter Γ ω.

Definition Γ_nat X := X + (Suc ∅).
Definition zero := right ∅.
Definition suc n := left n.

Definition Γ_tree X := (X × X) + (Suc ∅).
Definition leaf := right ∅.
Definition branch l r := left ⟨l,r⟩.

Definition nats := lfp Γ_nat.
Definition trees := lfp Γ_tree.
```

We can then use the same methodology as before to prove that `nats` and `trees` _are_ fixed points for their respective signatures, and use this fact to prove properties expected of them:

```coq
Lemma nat_lfp : Γ_nat nats ≡ nats.

Lemma zero_in_nats : zero ∈ nats.
Lemma suc_in_nats : forall {n}, n ∈ nats -> suc n ∈ nats.

Lemma tree_lfp : Γ_tree trees ≡ trees.

Lemma leaf_in_trees : leaf ∈ trees.
Lemma branch_in_trees : forall {l r},
  l ∈ trees -> r ∈ trees -> branch l r ∈ trees.
```

This approach generalises quite well and so can be used to implement the syntax of the $\lambda$-calculus.

### Terms of the $\lambda$-Calculus

For an explanation of the $\lambda$-calculus see [addendum II](extra.html#addendum_2). I'll go ahead and assume you already know what it is now, so be warned!

To keep complexity to a minimum, I will create a model of the $\lambda$-calculus using [de Brujin indices](https://en.wikipedia.org/wiki/De_Bruijn_index) instead of the normal variables. Problems can arise when normalising $\lambda$-terms meaning you have to _rename_ bound variables in order to avoid 'name conflicts'. Consider the evaluation of $((\lambda y. (\lambda x. y)) x)$. Naively performing a $\beta$-reduction on this term yields $(\lambda x. x)$, which is probably not what was intended - the free $x$ has suddenly become bound.

To avoid this issue, de Brujin instead used natural numbers to represent variables, and removed variables from abstractions altogether; when a natural number variable occurs in an expression, the 'value' of the variable directly refers to the abstraction to which it is bound. Specifically, a variable $n$ has $n$ other abstractions between it and the abstraction to which it is bound. For example, using de Brujin indices, the expression $(\lambda x. x)$ becomes $(\lambda. 0)$ and the expression $(\lambda x. (\lambda y. x y))$ becomes $(\lambda. (\lambda. 1 0))$.

Unfortunately, de Brujin indices are not an entirely free lunch. When substituting using de Brujin indices, we need to increment free variables in the expression being substituted every time we pass a $\lambda$-abstraction, so they do not become bound mistakenly. For example, we would not like $((\lambda. (\lambda. 1)) 0)$ to $\beta$-reduce to $(\lambda. 0)$; instead we have to 'lift' the free variables in the expression $0$ to reduce it to $(\lambda. 1)$. Moreover, we need to 'lower' free variables whenever we take the body out from an abstraction.

$\lambda$-terms using de Brujin indices ($\lambda_{dB}$-terms) the following syntax:

- any natural number (member of $\omega$) is a term
- if $M$ is a term, $(\lambda. M)$ is a term
- if $M$ and $N$ are terms, $(M N)$ is a term

From this we can derive $\Gamma_{\lambda_{dB}}(X) = \omega + X + X \times X$ as a description for terms of the $\lambda_{dB}$-calculus:

```coq
Definition Γ_lam X := ω + X + X × X.

Definition var n := left (left n).
Definition lam m := left (right n).
Definition app m n := right ⟨m,n⟩.
```

Since `Γ_lam` is a polynomial function, we can create the set of terms in exactly the same way as we did for `nats` and `trees` above:

```coq
Definition terms := lfp Γ_lam.

Lemma lam_lfp : Γ_lam terms = terms.
Lemma var_term : forall {n}, n ∈ ω -> var n ∈ terms.
Lemma lam_term : forall {m}, m ∈ terms -> lam m ∈ terms.
Lemma app_term : forall {m n},
  m ∈ terms -> n ∈ terms -> app m n ∈ terms.
```

We can use this to construct, for example, the identity function $(\lambda. 0)$ and prove that it is a term:

```coq
Definition id := lam (var ∅).

Lemma id_term : id ∈ terms.
```

### Inductively Defined Functions

Similarly to how we can use inductive definitions to define sets, we can use inductive definitions to describe and construct recursive functions. Consider the recursive function for converting from our inductive definition of the naturals to $\omega$:

$$
\begin{gathered}
f(\mathrm{right}(\bullet)) = \emptyset \\
f(\mathrm{left}(x)) = \mathrm{Suc}(f(x))
\end{gathered}
$$

To construct a description $\Gamma_f$ for this function (such that $\Gamma_f f = f$), notice that the $f(\mathrm{right}(\bullet)) = \emptyset$ case is non-recursive; therefore, $\langle \mathrm{right}(\bullet), \emptyset \rangle$ should be a base case and an element of $\Gamma_f(\emptyset)$. Then, for the recursive case, with every iteration of $\Gamma_f$, we can 'add' a new mapping $\langle \mathrm{left}(x), \mathrm{Suc}(y) \rangle$ to $\Gamma_f(F)$, provided that $F(x) = y$; given the set-theoretic encoding of functions, this is the same as saying $\langle x, y \rangle \in F$. Iterating $\Gamma_f$ like we did for inductive definitions should then cover all cases of $f$.

Unlike in a normal inductive definition, we do _not_ want to be able to discriminate between the base and recursive cases of $f$, so we should use the union instead of the disjoint union:

$$
\begin{gathered}
\Gamma_f(F) = \{ \langle \mathrm{right}(\bullet), \emptyset \rangle \} \cup \{ \langle \mathrm{left}(x), \mathrm{Suc}(y) \rangle : \forall x \in \mathbb{N}, \forall y \in \omega, \langle x, y \rangle \in F \} \\
f = \bigcup_{i = 0}^\omega \Gamma_f^i(\emptyset)
\end{gathered}
$$

Essentially, given an equation for a recursive function $r$, one can express the 'term' of the description corresponding to that equation by replacing each recursive application $r(a)$ in the right-hand-side of the equation with an element $x$ of $\mathrm{img}(r)$; a case may then be 'added' to the function if $\langle a, x \rangle$ is already a member of the function. We can write definitions for (both total and partial) _general recursive_ functions using this method - a general recursive function being one that you can program an algorithm to solve. For a nontrivial example, see [addendum III](extra.html#addendum_3).

### An Evaluator for the $\lambda$-Calculus

With the ability to create arbitrary recursive functions we can finally encode an evaluator for the $\lambda$-calculus within the set theory. I will be translating a minimal [Haskell evaluator](src/eval.hs.html) for $\lambda_{dB}$, with each Haskell function corresponding to a set-theoretic one.

I wanted to keep my evaluator as simple as possible, so I opted to write a 'call-by-name weak-head-normal-form' (CBV WHNF) evaluator; 'call-by-name' means that a function's argument is not evaluated to normal form before being substituted into the function's body, while 'weak-head-normal-form' means that any abstraction $(\lambda . b)$ is in normal form, even if $b$ is not.

First off, the Haskell implementation defines two functions, `lift` and `lower`, to handle lifting and lowering of free variables in de Brujin-indexed $\lambda$-terms as described above. I have assigned new variables to each function call to simplify the translation process, and better display the similarities between the Haskell and IZF implementations:

```haskell
data Term
    = Var Int
    | Lam Term
    | App Term Term

lift :: (Int, Term) -> Term
lift (i, Var v) | v < i = Var v
lift (i, Var v) | v >= i = Var (v+1)
lift (i, Lam b) =
    let c = lift (i+1, b) in Lam c
lift (i, App f a) =
    let g = lift (i, f)
        b = lift (i, a)
    in App g b
```

On ordinals (such as the members of $\omega$), the $<$ relation corresponds to $\in$, while the $\le$ relation corresponds to $\subseteq$. Using this, we can write descriptions for the above function, using $\omega$ instead of `Int`:

$$
\begin{aligned}
\Gamma_\mathrm{lift}(X) = &\{\langle \langle i, v \rangle, v \rangle : \forall v i \in \omega, v \in i\} \\
\cup &\{\langle \langle i, v \rangle, \mathrm{Suc}(v) \rangle : \forall v i \in \omega, i \subseteq v\} \\
\cup &\{\langle \langle i, (\lambda . b) \rangle, (\lambda . c) \rangle: \forall b c \in \mathrm{terms}, \forall i \in \omega, \langle \langle \mathrm{Suc}(i), b \rangle, c \rangle \in X\} \\
\cup &\{\langle \langle i, (f a) \rangle, (g b) \rangle : \forall f g a b \in \mathrm{terms}, \forall i \in \omega, \langle \langle i, f \rangle, g \rangle \in X \wedge \langle \langle i, a \rangle, b \rangle \in X\}
\end{aligned}
$$

We can now use this description to construct the function itself:

$$
\mathrm{lift} = \bigcup_{i = 0}^\omega \Gamma_\mathrm{lift}^i(\emptyset)
$$

To express this in our Coq model of set theory, I attempt to replicate the usual set-builder notation shown above. Unfortunately, the notation `{x | P}` is already used in Coq, so I have to make do with a textual form; `for x, y, z ∈ S, exp` is simply the repeated application of the axioms of replacement on `exp`, introducing `x`, `y` and `z` as variables bound within the replacement. The expression `given P, exp` is a strange one; if a proof of `P` cannot be provided, it is the empty set. Otherwise, it is the set `exp`. I use this to emulate the conditional part of set-builder notation:

```coq
Notation "'for' x , .. , y ∈ X , Z" :=
  (⋃ (@replacement X (fun x _ => .. (⋃ (@replacement X (fun y _ => Z))) ..)))
    (at level 200, x closed binder, y closed binder).
Notation "'given' P , Z" := (⋃ (selection (fun _ => P) (Z+>∅))) (at level 200, P at level 200).

Definition liftΓ X :=
  (for x, y ∈ ω, given y ∈ x, ⟨⟨x,var y⟩,var y⟩+>∅)
    ∪ (for x, y ∈ ω, given x ⊆ y, ⟨⟨x,var y⟩,var (Suc y)⟩+>∅)
    ∪ (for b, c ∈ terms, for x ∈ ω,
        given ⟨⟨Suc x,b⟩,c⟩ ∈ X,
        ⟨⟨x,lam b⟩,lam c⟩+>∅)
    ∪ (for f, a, g, b ∈ terms, for x ∈ ω,
        given ⟨⟨x,f⟩,g⟩ ∈ X,
        given ⟨⟨x,a⟩,b⟩ ∈ X,
        ⟨⟨x,app f a⟩,app g b⟩+>∅).

Definition lift := lfp liftΓ.
```

We can use the same process to construct the other functions of the evaluator:

```haskell
lower :: (Int, Term) -> Term
lower (i, Var v) | v < i = Var v
lower (i, Var v) | v >= i = Var (v-1)
lower (i, App f a) =
    let g = lower (i, f)
        b = lower (i, a)
    in App g b
lower (i, Lam b) =
    let c = lower (i+1, b)
    in Lam c

subst :: (Int, Term, Term) -> Term
subst (i, st, Var v) | i == v = st
subst (i, st, Var v) | i /= v = Var v
subst (i, st, App f a) =
    let g = subst (i, st, f)
        b = subst (i, st, a)
    in App g b
subst (i, st, Lam b) =
    let c = subst (i+1, lift (0, st), b)
    in Lam c
```

When we want to 'call' an already-defined function $f$ from within our set theory, we simply need to check that $\langle i, o \rangle \in f$ for some $i \in \mathrm{dom}(f)$, and $o \in \mathrm{img}(f)$:

```coq
Definition lowerΓ X :=
  (for i, v ∈ ω, given v ∈ i, ⟨⟨i,var v⟩,var v⟩+>∅)
    ∪ (for i, v ∈ ω, given i ⊆ (Suc v), ⟨⟨i,var (Suc v)⟩,var v⟩+>∅)
    ∪ (for f, a, g, b ∈ terms, for i ∈ ω,
        given ⟨⟨i,f⟩,g⟩ ∈ X,
        given ⟨⟨i,a⟩,b⟩ ∈ X,
        ⟨⟨i,app f a⟩,app g b⟩+>∅)
    ∪ (for b, c ∈ terms, for i ∈ ω,
        given ⟨⟨Suc i,b⟩,c⟩ ∈ X,
        ⟨⟨i,lam b⟩,lam c⟩+>∅).

Definition lower := lfp lowerΓ.

Definition substΓ X :=
  (for v ∈ ω, for st ∈ terms, ⟨⟨⟨v,st⟩,var v⟩,st⟩+>∅)
    ∪ (for i, v ∈ ω, for st ∈ terms, given i <> v,
        ⟨⟨⟨i,st⟩,var v⟩,var v⟩+>∅)
    ∪ (for i ∈ ω, for st, f, g, a, b ∈ terms,
        given ⟨⟨⟨i,st⟩,f⟩,g⟩ ∈ X,
        given ⟨⟨⟨i,st⟩,a⟩,b⟩ ∈ X,
        ⟨⟨⟨i,st⟩,app f a⟩,app g b⟩+>∅)
    ∪ (for i ∈ ω, for st, st', b, c ∈ terms,
        given ⟨⟨∅,st⟩,st'⟩ ∈ lift,
        given ⟨⟨⟨Suc i,st'⟩,b⟩,c⟩ ∈ X,
        ⟨⟨⟨i,st⟩,lam b⟩,lam c⟩+>∅).

Definition subst := lfp substΓ.
```

The CBN WHNF evaluation function has only two cases; `Lam b` is already in normal form, so evaluates to itself, while `App f a` first evaluates `f` to an abstraction `Lam b`, before substituting `a` in `b`. A free variable has no computation rules and is never evaluated. This means that the `eval` function has only two cases and is extremely simple:

```haskell
eval :: Term -> Term
eval (Lam b) = Lam b
eval (App f a) =
    let (Lam b) = eval f
        sb = subst (0, a, b)
        lb = lower (0, sb)
        vb = eval lb
    in vb
```

This is easily translated into IZF:

```coq
Definition evalΓ X :=
  (for b ∈ terms, ⟨lam b,lam b⟩+>∅)
    ∪ (for f, a, b, sb, lb, vb ∈ terms,
        given ⟨f,lam b⟩ ∈ X,
        given ⟨⟨⟨∅,a⟩,b⟩,sb⟩ ∈ subst,
        given ⟨⟨∅,sb⟩,lb⟩ ∈ lower,
        given ⟨lb,vb⟩ ∈ X,
        ⟨app f a,vb⟩+>∅).

Definition eval := lfp evalΓ.
```

Now that we have an `eval` function encoded within our set theory, we can finally try it out! Perhaps the simplest evaluation that this system can express is $((\lambda. 0) (\lambda. 0))$, the identity function applied to itself, which simply evaluates to $(\lambda. 0)$. To prove that $\langle ((\lambda. 0) (\lambda. 0)), (\lambda. 0) \rangle \in \mathrm{eval}$ (i.e. that $\mathrm{eval}((\lambda. 0) (\lambda. 0)) = (\lambda. 0)$) we first need to prove that $\mathrm{eval}(\lambda. 0) = (\lambda. 0)$. This comes from the first part of our definition of $\Gamma_\mathrm{eval}$:

```coq
Lemma eval_lam : forall {b}, ⟨lam b,lam b⟩ ∈ eval.
Lemma eval_id : ⟨id,id⟩ ∈ eval.
```

We can also prove that $(\lambda. 0)$ substituted into the variable $0$ (which is the body of $\mathrm{id}$) is just $(\lambda. 0)$, and that $(\lambda. 0)$ is constant under the `lower` and `lift` operations:

```coq
Lemma id_lift : ⟨⟨∅,id⟩,id⟩ ∈ lift.
Lemma id_lower : ⟨⟨∅,id⟩,id⟩ ∈ lower.
Lemma id_subst : ⟨⟨⟨∅,id⟩,id⟩,id⟩ ∈ subst.
```

Using these intermediate proofs, we can prove that $((\lambda. 0) (\lambda. 0))$ evaluates to $(\lambda. 0)$ in our model!

```coq
Lemma eval_id_id : ⟨app id id,id⟩ ∈ eval.
```

Normally one would prove that our model 'works' _in general_ by proving that it is equivalent to a 'trusted' model of the $\lambda$-calculus implemented in Coq, but this post is already quite long, so I will postpone that to another time. It would also be nice to prove $\in$-recursion correct _within_ the Coq model of IZF, but that would require some considerable proof automation on my part; even the proofs for simple evaluations were quite long! In any case, this was fun to mess around with, and served as a nice introduction to constructive set theory for me, which I hadn't encountered previously.