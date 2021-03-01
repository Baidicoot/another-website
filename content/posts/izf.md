---
title: The λ-Calculus, in Set Theory, in Coq
---

# The λ-Calculus, in Set Theory, in Coq

I've recently been reading about [Peter Aczel's interpretation](https://www.jstor.org/stable/27588436?seq=1) of 'Constructive Zermelo-Fraenkel Set Theory' (CZF) in [Martin-Löf's Type Theory](https://en.wikipedia.org/wiki/Intuitionistic_type_theory) (MLTT). This got me thinking about the inverse interpretation; how would one go about creating a model for a simple type theory within a set theory like CZF? I resolved to experiment with constructing models of various logics in set theory; however, to do this, I first needed a set theory to experiment *in*.

### The Set Theory

Enter Coq, an 'automated theorem prover', and implementation of a type theory not dissimilar to MLTT, the 'Calculus of Inductive Constructions' (CIC). Coq provides the perfect environment in which to interpret set theory à la Aczel; 'inductive types', the types created with the $\mathbb{W}$ axiom in MLTT, come 'free' in Coq, meaning you needn't [worry about extensionality](https://mazzo.li/epilogue/index.html%3Fp=324.html) when using them. Moreover, Coq already has a impredicative universe of propositions, `Prop`, which corresponds to Aczel's universe $\mathbb{P}$. Aside from theoretic concerns, Coq's handling of custom notations is definitely something to envy.

Aczel created a type $\mathbb{V}$ to represent 'iterative small classes' - small sets. $\mathbb{V}$ is defined as $(\mathbb{W} t : (\Sigma A : \mathbb{U}) A \to \mathbb{P}) \mathrm{fst}(t)$, meaning that an element of $\mathbb{V}$ is comprised of a (small) type $A$, a predicate $P : A \to \mathbb{P}$, alongside an indexing function $f : A \to \mathbb{V}$. The set represented by any inhabitant of $\mathbb{V}$ can be thought of as the image of the values $x : A$ through $f$, provided there is a proof of $P x$.

$\mathbb{V}$ roughly corresponds to a Coq inductive type:

```coq
Inductive V : Type :=
  mkV : forall (a : Type) (P: a -> Prop), ({x | P x} -> V) -> V.
```

However, it makes sense to generalize this definition by discarding `P`,

```coq
Inductive set : Type :=
  mk : forall (a : Type), (a -> set) -> set.
```

as any `mkV A P f` can be equivalently represented by `mk {x: A | P x} f`. From a set-theoretic standpoint, you can think of the `set` created by `mk a f` as the indexed set $(f_i)_{i \in a}$.

The 'equivalence' of two sets is defined via structual induction; the proposition $A \equiv B$ pretty much states 'for every $x \in A$, there is an element $y \in B$, such that $x \equiv y$', and vice-versa:

```coq
Fixpoint equiv (x y: set) : Prop :=
  match x, y with
  | mk a f, mk b g =>
    (forall x, exists y, equiv (f x) (g y))
    /\ (forall y, exists x, equiv (f x) (g y))
  end.

Notation "x ≡ y" := (equiv x y) (at level 70) : zf_scope.
```

The fact that this equivalence relation is in `Prop` (as opposed to `Type`) will have an impact on the axioms that are defineable for this interpretation further down the line; most notably, the impredicativity of `Prop` means that axioms like that of the powerset are provable in this interpretation - having `equiv A B : Type` makes this impossible. This has the effect of making this set theory more similar to 'Intuonistic Zermelo-Fraenkel Set Theory' (IZF) than to CZF.

We can already prove various lemmas about this definition of equivalence (namely the fact that it actually *is* an equivalence - that $\equiv$ is reflexive, symmetric, and transitive):

```coq
Lemma equiv_refl : forall {x: set}, x ≡ x.
Lemma equiv_sym : forall {x y: set}, x ≡ y -> y ≡ x.
Lemma equiv_trans : forall {x y: set}, x ≡ y -> forall {z: set}, y ≡ z -> x ≡ z.
```

The proposition $x \in (y_i)$ for an indexed set $(y_i)_{i \in I}$ simply means that there is an index $z \in I$ such that $y_z \equiv x$. As `mk a f` represents a set indexed by `a`, this directly translates to:

```coq
Definition member (x y: set) :=
  match y with
  | mk a f => exists i, f i ≡ x
  end.

Notation "x ∈ y" := (member x y) (at level 70) : zf_scope.
```

Similarly, the proposition $(x_i) \subseteq (y_i)$ for indexed sets $(x_i)_{i \in I}$ and $(y_j)_{j \in J}$ means that for all indexes $a \in I$, there is an index $b \in J$ such that $x_a \equiv y_b$:

```coq
Definition subset (x y: set) :=
  match x,y with
  | mk a f, mk b g => forall x, exists y, f x ≡ g y
  end.

Notation "x ⊆ y" := (subset x y) (at level 70) : zf_scope.
```

In order to prove that our definitions match those in traditional set theory, we need to prove that these relations are sound with respect to equivalence (meaning that equivalent terms can be substituted),

```coq
Lemma member_substs_left : forall {s a b}, a ≡ b -> a ∈ s -> b ∈ s.
Lemma member_substs_right : forall {s a b}, a ≡ b -> s ∈ a -> s ∈ b.
Lemma subset_substs_left : forall {x y z}, x ≡ y -> x ⊆ z -> y ⊆ z.
Lemma subset_substs_right : forall {x y z}, x ≡ y -> z ⊆ x -> z ⊆ y.
```

and that these relations have the same relationship with each other as in traditional set theory:

```coq
Lemma subset_ext : forall {x y}, (forall z, z ∈ x -> z ∈ y) -> x ⊆ y.
Lemma equiv_ext : forall {x y}, (forall z, z ∈ x <-> z ∈ y) -> x ≡ y.
(* etc... *)
```

Proving these properties for all subsequent definitions, while entirely possible, is rather painful and involves a lot of 'proof-passing', so I just add the following axiom, stating that $A \equiv B$ is equivalent to $A = B$, which greatly simplifies matters later on:

```coq
Axiom equiv_is_eq : forall {A B}, A ≡ B -> A = B.
```

We can now go ahead and construct, and prove properties of, the various ways of manipulating sets in IZF; first up, the axiom of the union set. Having defined the function `index` to extract the indexing type from a `set`, $\bigcup s$ of a set $s$ can be defined as:

```coq
Definition union (s: set) :=
  match s with
  | mk a f =>
    mk {x & index (f x)}
       (fun p => let (x,i) := p in
              let xi := f x in
              match xi return index xi -> set with
              | mk b g => fun i => g i
              end i)
  end.

Notation "⋃ x" := (union x).
```

Here the dependent pattern-matching syntax of Coq clouds the meaning of the definition somewhat - essentially, $\bigcup (s_i)_{i \in I}$ is a set not only indexed by $I$, but also indexed by the index of $s_j$, for some $j \in I$. This means that a member of a member of $s$ is simply a member of $\bigcup s$, so that the property $\forall x, \forall y \in x, \forall z \in y, z \in \bigcup x$ holds:

```coq
Lemma in_member_union : forall {x y z}, y ∈ x -> z ∈ y -> z ∈ ⋃x.
```

The axiom of the empty set $\emptyset$ states that there is a set with no elements - this can be encoded as a `set` indexed by `False` or $\bot$, representing falsity or contradiction in [intuonistic logic](https://en.wikipedia.org/wiki/Intuitionistic_logic). `False` has no inhabitants, and so any set indexed by `False` is also uninhabited, so $\forall x, x \notin \emptyset$.

```coq
Definition empty_set := mk False (False_rect set).

Notation "∅" := empty_set : zf_scope.
Notation "x ∉ y" := (x ∈ y -> False) (at level 70) : zf_scope.
Lemma empty : forall x, x ∉ ∅.
```

Complementary to the axiom of the empty set is the axiom of infinity; this is a set $\omega$ for which the property $\forall x \in \omega, \mathrm{Suc}(x) \in \omega$ holds, where $\mathrm{Suc}(x) = x \cup \{x\}$. Usually the $\mathrm{Suc}$ operation is defined in terms of unions and 'pairs' (another axiom), but instead I will define it in terms of insertion, with an axiom $\forall x y, \exists z, x \in z \wedge y \subseteq z$:

```coq
Definition insert (e: set) (s: set) :=
match s with
| mk a f => mk (True + a) (fun i =>
  match i with
  | inl _ => e
  | inr i => f i
  end)
end.
Definition Suc s := insert s s.
```

For every natural number $n$, we can iterate the $\mathrm{Suc}$ operation $n$ times on the empty set to generate the $n$th element of $\omega$:

```coq
Fixpoint fin n :=
  match n with
  | S n => Suc (fin n)
  | Z => ∅
  end.
```

$\omega$ is then defined as the `set` indexed by natural numbers with `fin` as the indexing function. Given an element of $\omega$, we know that that element has an index $n \in \mathbb{N}$ (by our definition of membership above), and so $\mathrm{Suc}(n)$ is simply the set with index $n + 1$:

```coq
Definition infinity := mk nat fin.
Notation "ω" := infinity.

Lemma Suc_member_infinity : forall {x}, x ∈ ω -> Suc x ∈ ω.
```

We can also transform the type-theoretic induction principle for the natural numbers to a set-theoretic one, formalizing that our model of $\omega$ corresponds to the one in the standard model for arithmetic - this extra definition turns our axiom of infinity into the axiom of *strong infinity*:

```coq
Definition ω_induction :
  {P: set -> Prop} (H: P ∅)
  (H0: forall x, P x -> P (Suc x))
  (x: set) (H1: x ∈ ω) : P x.
```

The next axiom is that of set 'separation' $\{x \in A | \phi(x)\}$ (i.e. comprehension *with a specified domain*), the subset of $A$ for which the property $\phi$ holds. This has a very obvious implementation; for any set $A$ with an indexing function `s : a -> set`, the set $\{x \in A | \phi(x)\}$ should be indexed by the subset of `a` for which `ϕ(f a)` holds:

```coq
Definition seperation (P: set -> Prop) (x: set) :=
  match x with
  | mk a s => mk {x | P (s x)} (fun p => let (x,_) := p in s x)
  end.
```

The axiom of the powerset states that for every set $x$, there exists a set $\mathcal{P}(x)$ such that $\forall y \in \mathcal{P}(x), y \subseteq x$. The powerset axiom is generally considered 'non-constructive', as there is no general way to construct the powerset of an infinite set, differentiating IZF from the *constructive* CZF.

```coq
Definition powerset (s: set) :=
  match s with
  | mk a f => mk (a -> Prop)
    (fun P => mk {x: a & P x}
      (fun i => let (x,_) := i in f x))
  end.

Lemma subset_in_powerset : forall {x y}, x ⊆ y -> x ∈ powerset y.
```

For any `mk a f : set`, the `powerset` of that set is indexed by `a -> Prop` - translated from Coq, this means $\mathcal{P}(s)$ is a family of sets $x_i$, where $i \in 2^s$ is the chatacteristic function of any subset.

The axiom of replacement essentially states that given a set $S$ and a function $f : S \to U$, then the image of $f$ through $S$ is also a set. I also strengthen the axiom of replacement, stating that *every* element in the replacement of $S$ using $f$ has a nonempty fibre (inverse image) in $S$:

```coq
Definition replacement {s} (f: forall x, x ∈ s -> set) : set.

Lemma image_in_replacement :
  forall {s f}, forall x (p: x ∈ s), f x p ∈ replacement f.
  
Lemma nonempty_fibre :
  forall {s f z}, z ∈ replacement f -> exists x (p: x ∈ s), f x p ≡ z.
```

It is important to note that the 'function' $f$ is *not* a normal set-constructed ('object-level') one; it is instead a binary relation $\phi$, expressed in the underlying logic of IZF, with the property that $\forall x \in S, \exists ! y \in U, \phi(x,y)$.

Actually, (this phrasing of) the axiom of replacement can be expressed in terms of a more general axiom, the axiom of strong collection. The axiom of strong collection is essentially an extended axiom of replacement that also operates over non-functional (but still total!) relations - that is, relations $\phi$ for which $\forall x, \exists y, \phi(x,y)$ holds (note the lack of _uniqueness_ of $y$). This is, regrettably, not definable using the 'membership in `Prop`' mantra, and so I must assert its existence using a (Coq) `Axiom`:

```coq
Axiom collection : forall {D P}, (forall x, x ∈ D -> exists y, P x y) -> set.
Axiom collection_prop : forall {D P x},
  x ∈ collection P <-> exists i, i ∈ D /\ P i x.
```

The next axiom is slightly more involved; it describes structual induction on the $\in$ relation. More specifically, given a property $\phi$, if, in order to prove $\phi(x)$ holds for *any* set $x$, it suffices to prove that if $\phi$ holds for all members of $x$, then $\phi$ holds for all sets. Expressed concisely, $(\forall x, [\forall y \in x, \phi(y)] \to \phi(x)) \to \forall z, \phi(z)$ for any $\phi$.

```coq
Definition ϵ_induction
  {P: set -> Prop} (H: prop_resp_equiv P)
  (H0: forall x, (forall y, y ∈ x -> P y) -> P x)
  (s: set) : P s.
```

With these nine axioms - extensional equivalence, unions, the empty set, strong infinity, insertion, seperation, replacement, powersets, and $\in$-induction - we can construct all the same set theory as in traditional ZF without the law of the excluded middle. All that is left is to do so.

### Set-Theoretic Constructions
As a first example construction, let us consider the cartesian product of two sets $A \times B$. For any sets $A$ and $B$, $A \times B$ should have the property that for any $x \in A$ and $y \in B$, $\langle x, y \rangle \in A \times B$, where $\langle x, y \rangle$ denotes the ordered pair of $x$ and $y$, constructed in the usual way as $\{\{x\}, \{x, y\}\}$.

For a given $x \in A$, we can construct the set $\{\langle x, y \rangle | y \in B\}$ by the axiom of replacement and a binary relation $\phi(y,\langle z, w \rangle)$ defined as $y = w \wedge z = x$. Call this process $f(x)$, and define a relation $\chi(x,s)$ as $s = f(x)$. We can then apply replacement *again*, this time using $\chi$, to generate the indexed set $(z_x)_{x \in A}$. Taking $\bigcup_{x \in A}z_x$, and we have the cartesian product $A \times B$:

```coq
Definition cartesian_product (A B: set) :=
  union (replacement (fun x (_: x ∈ A) => replacement (fun y (_: y ∈ B) => ⟨x,y⟩))).

Notation "A × B" := (cartesian_product A B) (at level 60, right associativity).
Lemma is_cartesian_product : forall A B x y, x ∈ A -> y ∈ B -> ⟨x,y⟩ ∈ A × B.
```

The disjoint union, or coproduct, of an indexed set $(x_i)_{i \in I}$ is the union of $(x_i)$, except every element is 'tagged' with the index of the set from which it came, meaning that for a $y \in x_j$ for some $j \in I$, then $\langle j, y \rangle \in \bigsqcup_{i \in I} x_i$, where $\bigsqcup$ is the disjoint union operation.

The disjoint union of a set $(x_i)_{i \in I}$ can be constructed using the axioms of IZF, by taking the replacement of $(x_i)$ with, given a $j \in I$, the replacement of $x_j$ with $\langle j, y \rangle$ for a given $y \in x_j$, and finding the union of the resultant set. In set notation, this is $\bigcup\{\{\langle j, y \rangle | y \in x_j\} | j \in I\}$, which is easily converted to Coq:

```coq
Definition disjoint_union {I} (f: forall j, j ∈ I -> set) :=
  ⋃(replacement (fun j p => replacement (fun y (_: y ∈ f j p)  => ⟨j,y⟩))).

Lemma is_disjoint_union :
  forall {S f x y}
         (p: x ∈ S),
         y ∈ f x p -> ⟨x,y⟩ ∈ disjoint_union f.
```

That derivation is almost identical to our derivation for the cartesian product! In fact, the cartesian product is *definitionally equal* to the case of the disjoint union where $x_i$ is always $B$ for any $i \in A$:

```coq
Lemma cartesian_product_is_extreme_disjoint_union :
  forall {A B}, A × B ≡ disjoint_union (fun x (_: x ∈ A) => B).
Proof.
  intros. exact equiv_refl.
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

The exponential set $A^B$, of functions $f : B \to A$ has a pretty obvious construction; all functions $B \to A$ are subsets of $B \times A$, and so to construct $A^B$ we can simply restrict $\mathcal{P}(B \times A)$ to only those subsets $R$ which are *functional* (for all $x \in B$, if $\langle x, y \rangle \in R$ for a $y \in A$, then $y$ is unique) and *left-total* (for all $x \in B$, there exists a $y \in A$ such that $\langle x, y \rangle \in R$), using seperation:

```coq
Definition functional (R: set) :=
  forall {a b}, ⟨a,b⟩ ∈ R -> forall {c}, ⟨a,c⟩ ∈ R -> b ≡ c.

Definition left_total (R D: set) :=
  forall {a}, a ∈ D -> exists {b}, ⟨a,b⟩ ∈ R.

Definition exponential (A B: set) :=
  seperation (fun R => functional R /\ left_total R B) (powerset (B × A)).

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

Call this set $\mathbb{F}$. We can prove that $\mathbb{F}$ contains a _unique_ element, meaning that $\forall f g \in \mathbb{F}, \forall x \in TC(X), f(x) = g(x)$, by $\in$-induction over $x$. In the inductive case, we need to prove that $f(a) = g(a)$ given $\forall b \in a, f(b) = g(b)$. As then $\{f(b) : b \in a\} = \{g(b) : b \in a\}$. As $\phi$ relates this to a _unique_ set $c$, then $f(a) = c = g(a)$.

Taking $f = \bigcup \mathbb{F}$, by the uniqueness property above, $f$ will be the function we want, provided we can prove that $\mathbb{F}$ is inhabited. $\mathrm{dom}(f) = \emptyset$ iff $\mathbb{F}$ is uninhabited, so proving $TC(X) \subseteq \mathrm{dom}(f)$ suffices. Once again, $\in$-induction comes to our aid! Using the predicate $\forall v \in TC(X) \to \exists w, \langle v,w \rangle \in f$, the inductive case becomes:

$$
\forall a, (\forall b \in a, b \in TC(X) \to \exists c, \langle b, c \rangle \in f) \to a \in TC(X) \to \exists d, \langle a, d \rangle \in f
$$

The assumption $a \in TC(X)$ proves that $\forall b \in a, b \in TC(X)$ by the property of the transitive closure. Therefore, we can use replacement to construct the set $\{f(b) : b \in a\}$, for which there exists a unique set $d$ such that $\phi(\{f(b) : b \in a\},d)$. By the construction of $f$, $f(a)$ is exactly the set $d$, and so $\langle a,d \rangle \in f$. Therefore, $\forall v \in TC(X) \to \exists w, \langle v,w \rangle \in f$, i.e. $TC(x) \subseteq \mathrm{dom}(f)$, thereby proving the existence of $f$ - for a given $X$. Whenever we use $\in$-recursion over a set $S$, we can just set $X = S$, meaning we can safely ignore the added complexity of $X$ from now on.

Formalizing the reasoning above is somewhat out of the scope of this project, so I just add an axiom implementing the functionality of $\in$-recursion:

```coq
Axiom ϵ_rec : (forall x, (forall y, y ∈ x -> set) -> set) -> set -> set.
Axiom ϵ_rec_prop : forall {F x},
  ϵ_rec F x ≡ F x (fun y _ => ϵ_rec F y).
```

This is the last axiom I will add to the system, and subsequent proofs use only the `ϵ_rec` and `equiv_is_eq` axioms.

### Properties of Naturals

We will need some proofs about $\omega$ for when we construct more complex sets (which we will construct by $\in$-recursion over $\omega$). Firstly, we can prove that $\omega$, and all elements of $\omega$, are von Neumann ordinals, using $\omega$-induction:

```coq
Lemma ω_ordinal : forall x, x ∈ ω -> x ⊆ ω.
Lemma nat_ordinal : forall x, x ∈ ω -> forall y, y ∈ x -> y ⊆ x.
```

Therefore, the relations $x \in y$ and $x \subsetneq y$ correspond to $x < y$ and $x \subseteq y $ corresponds to $x \leq y$. By von Neumann's definition, the ordinal $x$ is the interval $[0,x)$, and so every member of $x$ is itself in $\omega$. A direct consequence of this is that the predicessor of any element of $\omega$ is also an element of $\omega$ (as $\forall x, x \in \mathrm{Suc}(x)$):

```coq
Lemma fin_contains_nats : forall {x y}, x ∈ ω -> y ∈ x -> y ∈ ω.
Lemma pred_is_nat : forall {x}, Suc x ∈ ω -> x ∈ ω.
```

We can use $\omega$-induction to prove that comparison for the naturals is decidable, and derive some related proofs:

```coq
Lemma nat_cmp_dec :
  forall {x y}, x ∈ ω -> y ∈ ω -> x ∈ y \/ x ≡ y \/ y ∈ x.
Lemma least_nat :
  forall {x}, x ∈ ω -> ∅ ∈ x \/ x ≡ ∅.
Lemma ω_nojunk :
  forall {x}, x ≡ ∅ \/ exists n, n ∈ ω /\ x ≡ Suc n.
```

Finally, we can use these comparisons to prove the existence of an upper bound (maximum) for two naturals, which is itself a natural:

```coq
Lemma nat_cmp_leq :
  forall {x y}, x ∈ ω -> y ∈ ω -> x ⊆ y \/ y ⊆ x.
Lemma maximum :
  forall {x y}, x ∈ ω -> y ∈ ω -> exists m, m ∈ ω /\ x ⊆ m /\ y ⊆ m.
```

### The $\lambda$-calculus

We now have enough theory begin the construction of a model for the $\lambda$-calculus! I'll begin with a quick introduction to the $\lambda$-calculus; anyone who is already familiar with it can safely skip this section.

The $\lambda$-calculus (LC) is a system used to express computation. Much like in arithmetic, computing the value of an expression involves applying a series of transformations upon the expression until it reaches a 'normal form' (consider the transformations used to reduce $2 + 5 + 8$ to $13$). An expression, or _term_, of the $\lambda$-calculus can be created with the following rules:

- any _variable_ (usually represented by a lowercase letter, e.g. $v$) is a term
- $(M N)$ is a term if $M$ and $N$ are terms; this is called 'application'
- $(\lambda v. M)$ is a term if $M$ is a term and $v$ is a variable; this is 'abstraction'

In an abstraction $(\lambda v. M)$, $M$ is called the _body_ of the abstraction, and the $\lambda$ serves as a kind of quantifier for $v$; inside the body of $(\lambda v. M)$, any occurance of $v$ is considered _bound_, while in a term where $v$ is not quantified (for example $(N v)$), any occurance of $v$ is considered _free_.

The $\lambda$-calculus has one rule for the reduction of expressions, $\beta$-reduction, which states that you can reduce any term of the form $((\lambda v. M) N)$ by substituting all (free) occurances of $v$ in $M$ with $N$. You can think of this as simplifying an application of a function $f v \mapsto M$ in the expression $f(N)$ - indeed, the $\lambda$-calculus is just a calculus of function creation and application.

To normalise (or evaluate) a $\lambda$-term, one simply repeats $\beta$-reductions until the resulting term is in a 'normal form'; different presentations often use different normal forms, but in this post I will use 'weak head normal form', meaning that the resulting term is an abstraction $(\lambda v. M)$ - note that the body of the abstraction, $M$, does _not_ need to be in normal form.

As an example, the expression $((\lambda x. x) (\lambda y. y))$ is not an abstraction, so we apply $\beta$-reduction to simplify it. Substituting all occurances of $x$ with $(\lambda y. y)$ in the expression $x$, we arrive at the expression $(\lambda y. y)$, which _is_ in normal form, and so we can stop simplification. Therefore, the normalised version of $((\lambda x. x) (\lambda y. y))$ is $(\lambda y. y)$.

Not all terms actually have a normal form; consider the expression $((\lambda x. (x x)) (\lambda x. (x x)))$. Applying $\beta$-reduction on this means we substitute all free occurances of $x$ with $(\lambda x. (x x))$ in the expression $(x x)$. This is simply $((\lambda x. (x x)) (\lambda x. (x x)))$, which is exactly the expression we started with, meaning that no amount of $\beta$-reduction will succeed in producing a normal form for this expression. Therefore, evaluation (simplifying an expression to a normal form) is a partial function.

### Inductively Defined Sets

A set is 'inductively defined' if all members of the set can be _finitely_ described in terms of operations on other members of that set - a classic example is the set of natural numbers:

- $0$ is a natural number
- $n+1$ is a natural number if $n$ is a natural number

You can see that the set of $\lambda$-calculus terms is also inductively defined - each term is either a constant or 'base case' ($0$ for the natural numbers, or variables for $\lambda$-terms) or a composition of terms already in the set ($n+1$ in the example above, abstraction and application for $\lambda$-terms). We can formalise this notion of inductive definability by introducing the concept of a 'description' of an inductively defined set.

The description of a set $X$ is a class function $\Gamma$ such that $X$ is the 'least fixed point' of $\Gamma$ - that is, $X$ is the _smallest_ set such that $\Gamma(X) = X$.

As an example, consider $\Gamma_\mathbb{N}(X) = X + 1$, the description of the natural numbers. If $1$ is the set containing the single element $\bullet$, then the least fixed point of $\Gamma_\mathbb{N}$ must contain $\mathrm{right}(\bullet)$; repeating this process, we see that it must also contain $\mathrm{left}(\mathrm{right}(\bullet))$, as well as $\mathrm{left}(\mathrm{left}(\mathrm{right}(\bullet)))$, and so on. If we define $0$ as $\mathrm{right}(\bullet)$ and $n+1$ as $\mathrm{left}(n)$, then the similarities with the inductive definition we gave above become clear.

It is often possible to gain an understanding of what the least fixed point of a given set will 'look' like by looking at its description. If we consider only 'polynomial' descriptions - descriptions in the form $a + b \times x + c \times x \times x + \dots$ - then each term of the polynomial - $a \times x^n$ - is an operation combining $n$ other elements of $x$ (and an element of $a$) to construct a new element of $x$. When $n = 0$, the 'operations' are constant; these are the base cases of the inductive definition.

For example, we can write the description for the terms of the $\lambda$-calculus as $\Gamma_\lambda(X) = \mathrm{vars} + \mathrm{vars} \times X + X \times X$, given a set of variables $\mathrm{vars}$. The constant term $\mathrm{vars}$ is the base case - we can construct a $\lambda$-term from a variable. The second term states that we can construct a $\lambda$-term from another $\lambda$-term _and_ a variable - this is the abstraction $(\lambda v. M)$. Finally, with two $\lambda$-terms - $X \times X$ - we can construct $(M N)$, which is itself a $\lambda$-term.

### Inductively Defined Sets

A set is 'inductively defined' if all members of the set can be _finitely_ described in terms of operations on other members of that set - a classic example is the set of natural numbers:

- $0$ is a natural number
- $n+1$ is a natural number if $n$ is a natural number

Our description of the terms of the $\lambda$-calculus above matches this format, and so it is an inductively defined set. We can formalise this notion of inductive definability using a concept from category theory and computer science, namely that of the 'initial algebra'. This is quite an abstract concept, so I will describe it through the example of the natural numbers.

Translating from the category-theoretic terminology, consider a class function $F : \mathbb{V} \to \mathbb{V}$, which maps every set $X$ to $1 + X$, where $1$ is the set containing one element $\bullet$. We say that an _algebra_ of $F$ is the pair of a 'carrier' set $X$ and a set function $f : 1 + X \to X$ (so then $X$ is _closed_ over the operation $f$). We can then 'decompose' $f$ into two functions $g : 1 \to X$ and $h : X \to X$, where $f(\mathrm{left}(x)) = g(x)$ and $f(\mathrm{right}(x)) = h(x)$. Noticing that, since $1$ has only one element $\bullet$, the image of $g$ must have a single element $g(\bullet)$, we can draw a correspondence between the natural numbers and $X$; $g(\bullet)$ corresponds to $0$, and $h(n)$ corresponds to $n+1$. In fact, $\langle \mathbb{N},+1 \rangle$ _is_ a an algebra of $F$.

However, $\langle \mathbb{N},+1 \rangle$ is not the _sole_ algebra of $F$. Consider a set $Y$, that has elements $p$, $q$, and $r(x)$ for all $x \in Y$. Taking $f_Y : 1 + Y \to Y$ to map $\mathrm{left}(\bullet) \mapsto p$ and $\mathrm{right}(n) \mapsto r(n)$, we can see that $\langle Y,f_Y \rangle$ is _also_ an algebra for $F$! In fact, $1$ is an algebra for $F$, where $f_1 : 1 + 1 \to 1$ simply maps all input to $\bullet$. This is pretty bad, as it means that 'the algebra of $F$' is not enough to describe what we are looking for.

To solve this, category theorists introduced the concept of the _initial_ algebra (which turns out to be unique). In order for an algebra to be initial, there must be a _unique homomorphism_ from the intitial algebra to all other possible algebras of. 'Homomorphism' here means a 'structure-preserving map between algebras', meaning that given a homomorphism $h : A \to B$, then any properties of $A$ hold in $\mathrm{Img}(h)$. This immediately disqualifies $\langle Y,f_Y \rangle$ as being the initial algebra for $F$, as $q$ is 'unaccounted for' for all $h$. It also disqualifies $\langle 1,f_1 \rangle$ as being the initial algebra for $F$, as since all elements of $1$ are equal, it is impossible to construct a homomorphism to, for example, $\mathbb{N}$; in $1$, $n+1 = n$, while in $\mathbb{N}$ this obviously does not hold. As it happens, $\mathbb{N}$ is the initial algebra for $F$, and indeed the initial algebra for a class function $F$ is usually what we need when constructing data types.

In order to calculate the initial algebra of any class functions $\Gamma : \mathbb{V} \to \mathbb{V}$ it suffices to find the 'least fixedpoint' of $\Gamma$, which is the set $X$ such that $X = \Gamma X$. Whether $\Gamma$ _has_ a least fixedpoint is an entirely different question however; by Cantor's diagonal argument, we can see that, for example, there is no least fixedpoint of the powerset operation. However, we can obtain a least fixedpoint for all the functions $\Gamma$ we are interested in - which are all polynomial equations - by repeated iteration of $\Gamma$. It is also important to note that for all polynomial functions $\Gamma$, $\Gamma(\emptyset) \subseteq \Gamma(X)$ for all sets $X$ - this is because $\Gamma(\emptyset)$ represents the 'base cases' of the inductive set we are defining, which should of course be included in any set created with the application of $\Gamma$. I define an 'iterator' for class functions over sets using $\in$-recursion:

```coq
Definition ϵ_iter Γ := ϵ_rec (fun _ f => ⋃(replacement (fun x H => Γ(f x H)))).

Lemma ϵ_iter_prop : forall {Γ X},
  ϵ_iter Γ X = ⋃ (replacement (fun x _ => Γ (ϵ_iter Γ x))).
```

I also prove some behaviours of set operations over the empty set:

```coq
Lemma union_empty : ⋃∅ ≡ ∅.

Lemma replacement_empty : forall {Γ},
  @replacement ∅ Γ ≡ ∅.
```

Taking $\Gamma$ to be the function $F$ as defined above, mapping $X \mapsto 1 + X$, you can see that `ϵ_iter F (Suc (Suc ∅))` is equal to $\bigcup \{F(\bigcup \{F(\emptyset) : y \in x \}) : x \in \mathrm{Suc}(\mathrm{Suc}(\emptyset)) \}$. This is in turn equal to $F(F(\emptyset)) \cup F(\emptyset) \cup \emptyset$. In general, `ϵ_iter Γ n` for an ordinal $n$ is equal to $\bigcup_{i = 0}^{i = n} \Gamma^i(\emptyset)$. If we let $n = \omega$ then we obtain $\bigcup_{i = 0}^{i = \omega} \Gamma^i(\emptyset)$. Since $\Gamma(\bigcup_{i = 0}^{i = \omega} \Gamma^i(\emptyset)) = \bigcup_{i = 1}^{i = \omega+1} \Gamma^i(\emptyset)$, and $\omega + 1 = \omega$, we have $\bigcup_{i = 1}^{i = \omega} \Gamma^i(\emptyset)$. As $\Gamma(\emptyset) \subseteq \Gamma(X)$ for all $X$ - at least for the $\Gamma$ we are interested in, described above - then we have $\Gamma(\bigcup_{i = 0}^{i = \omega} \Gamma^i(\emptyset)) = \bigcup_{i = 0}^{i = \omega} \Gamma^i(\emptyset)$, so $\bigcup_{i = 0}^{i = \omega} \Gamma^i(\emptyset)$ is the least fixedpoint of $\Gamma$.