---
title: The λ-Calculus, in Set Theory, in Coq - Extras
---

# The $\lambda$-Calculus, in Set Theory, in Coq - Extras

A collection of extra, vaguely rambling, content that didn't make it into the [final version](index.html).

<span id="addenum_1"></span>

## Addenum I - Coq Encoding of Intuonistic Set Theory

Coq, which implements a type theory not dissimilar to MLTT, the 'Calculus of Inductive Constructions' (CIC), provides the perfect environment in which to interpret set theory à la Aczel; 'inductive types', the types created with the $\mathbb{W}$ axiom in MLTT, come 'free' in Coq, meaning you needn't [worry about extensionality](https://mazzo.li/epilogue/index.html%3Fp=324.html) when using them. Moreover, Coq already has a impredicative universe of propositions, `Prop`, which corresponds to Aczel's universe $\mathbb{P}$. Aside from theoretic concerns, Coq's handling of custom notations is definitely something to envy.

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

### Properties of Naturals

I needed some proofs about $\omega$ for when I constructed more complex sets through induction. First, I proved that $\omega$, and all elements of $\omega$, are von Neumann ordinals, using $\omega$-induction:

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

<span id="addenum_2"></span>

## Addenum II - The $\lambda$-Calculus

The $\lambda$-calculus (LC) is a system used to express computation. Much like in arithmetic, computing the value of an expression involves applying a series of transformations upon the expression until it reaches a 'normal form' (consider the transformations used to reduce $2 + 5 + 8$ to $13$). An expression, or _term_, of the $\lambda$-calculus can be created with the following rules:

- any _variable_ (usually represented by a lowercase letter, e.g. $v$) is a term
- $(M N)$ is a term if $M$ and $N$ are terms; this is called 'application'
- $(\lambda v. M)$ is a term if $M$ is a term and $v$ is a variable; this is 'abstraction'

In an abstraction $(\lambda v. M)$, $M$ is called the _body_ of the abstraction, and the $\lambda$ serves as a kind of quantifier for $v$; inside the body of $(\lambda v. M)$, any occurance of $v$ is considered _bound_, while in a term where $v$ is not quantified (for example $(N v)$), any occurance of $v$ is considered _free_.

The $\lambda$-calculus has one rule for the reduction of expressions, $\beta$-reduction, which states that you can reduce any term of the form $((\lambda v. M) N)$ by substituting all (free) occurances of $v$ in $M$ with $N$. You can think of this as simplifying an application of a function $f v \mapsto M$ in the expression $f(N)$ - indeed, the $\lambda$-calculus is just a calculus of function creation and application.

To normalise (or evaluate) a $\lambda$-term, one simply repeats $\beta$-reductions until the resulting term is in a 'normal form'; different presentations often use different normal forms, but in this post I will use 'weak head normal form', meaning that the resulting term is an abstraction $(\lambda v. M)$ - note that the body of the abstraction, $M$, does _not_ need to be in normal form.

As an example, the expression $((\lambda x. x) (\lambda y. y))$ is not an abstraction, so we apply $\beta$-reduction to simplify it. Substituting all occurances of $x$ with $(\lambda y. y)$ in the expression $x$, we arrive at the expression $(\lambda y. y)$, which _is_ in normal form, and so we can stop simplification; the normalised version of $((\lambda x. x) (\lambda y. y))$ is $(\lambda y. y)$.

Not all terms actually have a normal form; consider the expression $((\lambda x. (x x)) (\lambda x. (x x)))$. Applying $\beta$-reduction on this means we substitute all free occurances of $x$ with $(\lambda x. (x x))$ in the expression $(x x)$. This is simply $((\lambda x. (x x)) (\lambda x. (x x)))$, which is exactly the expression we started with, meaning that no amount of $\beta$-reduction will succeed in producing a normal form for this expression. Therefore, evaluation (simplifying an expression to a normal form) is a partial function.

<span id="addenum_3"></span>

## Addenum III - Inductively Defined Functions

Consider the Ackerman-Péter function:

$$
\begin{gathered}
\mathrm{ack}(0,n) = \mathrm{Suc}(n) \\
\mathrm{ack}(\mathrm{Suc}(m),0) = \mathrm{ack}(m,1) \\
\mathrm{ack}(\mathrm{Suc}(m),\mathrm{Suc}(n)) = \mathrm{ack}(m,\mathrm{ack}(\mathrm{Suc}(m),n))
\end{gathered}
$$

The base cases of this function are $\mathrm{ack}(0, n) = \mathrm{Suc}(n)$ for all $n \in \omega$. For the first recursive case, for all $m, x \in \omega$, if $x = \mathrm{ack}(m,1)$, then $\mathrm{ack}(\mathrm{Suc}(m),0) = x$. Similarly, for the second recursive case, for all $m, n, x, y \in \omega$, if $x = \mathrm{ack}(\mathrm{Suc}(m),n)$ and $y = \mathrm{ack}(m,x)$, then $\mathrm{ack}(\mathrm{Suc}(m),\mathrm{Suc}(n)) = y$. We can express this as a description like so:

$$
\begin{aligned}
\Gamma_{\mathrm{ack}}(A) = &\{ \langle \langle \emptyset, n \rangle, n \rangle : \forall n \in \omega \} \\
\cup &\{\langle \langle \mathrm{Suc}(m), \emptyset \rangle, x \rangle : \forall m, x \in \omega, \langle \langle m, \mathrm{Suc}(\emptyset) \rangle, x \rangle \in A\} \\
\cup &\{\langle \langle \mathrm{Suc}(m), \mathrm{Suc}(n) \rangle, y \rangle : \forall m, n, x, y \in \omega, \langle \langle \mathrm{Suc}(m), n \rangle, x \rangle \in A \wedge \langle \langle m, x \rangle, y \rangle \in A\}
\end{aligned}
$$

This is a rather complex example, but it shows how recursive functions can be constructed as inductively defined sets:

$$
\mathrm{ack} = \bigcup_{i = 0}^\omega \Gamma_{\mathrm{ack}}^i(\emptyset)
$$