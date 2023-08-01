## Dependent type theory

*Andreas Nuyts*

The simply-typed lambda-calculus (STLC) from TAPL chapter 9 [^TAPL] is, as its name suggests, simply-typed. Chapters 23-24 and 29-30 will discuss richer type systems in which it is possible to quantify universally (∀) or existentially (∃) over types and even type operators. These quantifiers bind type (operator) variables, leading to a system in which contexts do not only list term variables - e.g. `x : Bool` - but also type (operator) variables.

Dependent type systems take this idea further by treating types as "first class citizens": types are ordinary terms and there is a type of types - in Agda called `Set`, a convention that we will follow here for simplicity even though `Type` would arguably have been a better name - so that we can say e.g. `Bool : Set`.

While most chapters in TAPL treat languages and type systems very thoroughly, discussing practical and metatheoretical aspects such as implementation and correctness of type-checking and termination of evaluation, this chapter primarily aims to provide you with just the information needed to confidently use dependent type theory without getting too confused.

### 1 Motivation

We discuss four motivations for dependent type systems: programming, proving, using proofs in programs, and formalizing programming languages.

#### 1.1 Programming

Just like simply-typed languages, dependently typed languages are *programming languages*. While simple type systems can catch, at compile time, basic errors such as returning a number when a string was required, dependent types can prevent more subtle errors. The archetypical example is that of the vector type.

TAPL §11.12 [^TAPL] discusses the `List` type. For every type `A`, we get a type `List A` with constructors

```
nil : List A
cons : A -> List A -> List A
```

so that we can form e.g. a three-element list by writing `cons a1 (cons a2 (cons a3 nil))`.

The operations provided in TAPL for analyzing/using lists are

```
isnil : List A -> Bool
head : List A -> A
tail : List A -> List A
```

The problem with this approach is that `head nil` and `tail nil` are not defined. In the TAPL presentation, they are neither values, nor do they evaluate further. A possible solution is to analyze lists using a `fold` operation:

```
fold : B -> (A -> B -> B) -> List A -> B
fold nilB consB nil = nilB
fold nilB consB (cons a as) = consB a (fold nilB consB as)
```

While it's nice that `fold`, unlike `head` and `tail`, is a total function (meaning that it is defined on all input values), this does not really change the fact that sometimes we know for sure that a list is non-empty and then maybe we do want to have operations for extracting its head and tail.

In a dependently typed language like Agda, we can define a type of vectors which is indexed by the length of its elements:

```agda
data Vec (A : Set) : Nat -> Set where
  nil : Vec 0
  cons : {n : Nat} -> A -> Vec A n -> Vec A (suc n)
```

For such a type, we can define total `head` and `tail` functions by requiring, in their type, that the length of the given vector is not zero (i.e. it is a successor of something):

```agda
head : {n : Nat} -> Vec A (suc n) -> A
head (cons a as) = a
tail : {n : Nat} -> Vec A (suc n) -> Vec A n
tail (cons a as) = as
```

We do not need to provide clauses for `nil` since the length of `nil` is not of the form `suc n`, so that `head nil` and `tail nil` are ill-typed programs.

#### 1.2 Proving

Dependent type theory is not only a programming language, but can also be used as a constructive logic. Here, the word "constructive" indicates a logic in which a proposition can only be asserted by providing evidence for it. Mathematical propositions are built up using logical connectives (and, or, not, implication, …). The type `Proof A` of evidence needed to assert a proposition `A` can be defined by induction on the proposition. For example:

* Evidence for `A ∧ B` consists of evidence for `A` and evidence for `B`, so we can define `Proof (A ∧ B) = Proof A × Proof B`. Then a proof `a : Proof A` and a proof `b : Proof B` can be paired up as `(a, b) : Proof (A ∧ B)`.
* Evidence for `∃ (x : A) . P(x)` consists of an element `a : A` and evidence for `P(a)`. The so-called Σ-type of dependent type theory classifies pairs where the *type* of the second component depends on the *value* of the first component. So we can define `Proof (∃ (x : A) . P(x)) = Σ (x : A) . Proof (P(x))`.[^Σ-syntax] Then a witness `a : A` and a proof `p : Proof (P(a))` can be paired up as `(a, p) : Proof (∃ (x : A) . P(x))`.

In fact, one does not really define the function `Proof : MathProp -> Set` by induction. Instead, the type of mathematical propositions `MathProp` is defined to be exactly `Set`, and the logical connectives are defined to be exactly the corresponding type formers, e.g. `_∧_` is defined as `_×_`. Thus, `Proof` becomes the identity function (`Proof A = A`), and propositions *are* types. Specifically, a proposition is the type of its proofs. Conversely, any type `A` can be read as the proposition "`A` is inhabited", which can be proven by providing an element of `A`.

The correspondence between propositions and types is called the Curry-Howard correspondence. Some authors call it the Curry-Howard isomorphism which may create the incorrect impression that it is about *doing* something (an isomorphism is an invertible operation, but the operation concerned is simply the identity, i.e. we need not do anything) rather than *understanding* something (namely that propositions are types).

##### Example

The tautological statement "If A implies (B or C), then (A and not B) implies C" can be written, using the Curry-Howard correspondence (see the sheet), as

```agda
taut : {A B C : Set} -> (A -> B ⊎ C) -> (A × (B -> ⊥) -> C)
```

and proven as follows:

```agda
taut f (a , notb) with f a
taut f (a , notb) | inl b with notb b
taut f (a , notb) | inl b | ()
taut f (a , notb) | inr c = c
```

##### Example

The following is a property of constructive logic: If for each `x ∈ X`, there exists some `y ∈ Y` such that `P x y`, then there is a function `f : X -> Y` such that for each `x ∈ X`, we have `P x (f x)`.

```agda
property : {X Y : Set} {P : X -> Y -> Set} ->
  ((x : X) -> Σ[ y ∈ Y ] P x y) ->
  Σ[ f ∈ (X -> Y) ] ((x : X) -> P x (f x))
property p = ( λ x -> proj₁ (p x) , λ x -> proj₂ (p x) )
```

#### 1.3 Programs requiring evidence

To use an example from TAPL's sequel ATTAPL [^ATTAPL], suppose we want to index a vector. A partial function for indexing lists would be the following:

```agda
_!!_ : List A -> Nat -> A
cons a as !! 0 = a
cons a as !! suc n = as !! n
```

However, this function is clearly undefined for the empty list and, more generally, for indices that are out of bounds. In dependent type theory, we can ensure that the index is less than the length of the list by requiring the caller to provide, as one of the functions arguments, evidence that this is the case:

```agda
_!!_ : {n : Nat} -> Vec A n -> (Σ[ i ∈ Nat ] (i < n)) -> A
nil !! (i , ())
cons a as !! (0 , _) = a
cons a as !! (suc n , p) = as !! (n , decrement< p)
```

where `decrement<` has type (is proof of the proposition) `{m n : Nat} -> (suc m < suc n) -> (m < n)`. This time, we do have a clause for the empty list, but we do not have to provide a right hand side as the existence of evidence of the proposition `i < 0` is absurd, as signalled by the absurd pattern `()`.

As a side note, instead of `Σ[ i ∈ Nat ] (i < n)`, most libraries will instead use `Fin n`, the "finite type with `n` elements", namely the natural numbers that are strictly less than `n`:

```agda
data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)
```

#### 1.4 Formalizing programming languages

Most of the TAPL book is about the formalization of various programming languages. We can use a dependently typed language such as Agda as a metalanguage in which we can do this work in a computer-assisted and computer-verified way. Terminologically, this creates some potential for confusion: we are now considering two languages, each with its types, terms, values, judgements, etc. To disambiguate, the language we are formalizing is often called the **internal language** or the **object language**, whereas the dependently typed metalanguage is called the **metalanguage** or **metatheory**. We can further distinguish between internal types and metatypes, internal terms and metaterms, etc.

Thanks to (meta)type dependency, we can consider a (meta)type of internal derivations, parametrized by an internal context, term and type:

```agda
IDeriv : ICtx -> ITerm -> IType -> Set
```

Now `IDeriv Γ t T` can be read as either the metatype of internal derivations, or as the metaproposition "The internal judgement `Γ ⊢ t : T` is derivable", evidence for which is exactly a derivation tree. Note that the metatype of `IDeriv Γ t T` is `Set`, the metatype of metatypes. In Agda, we can use mixfix notation to actually write `Γ ⊢ t ∈ T` instead of `IDeriv Γ t T`:

```agda
_⊢_∈_ : ICtx -> ITerm -> IType -> Set
_⊢_∈_ = IDeriv
```

Derivation trees are of course generated by inference rules, so the type `Deriv` can be defined as a datatype (using a `data` declaration) whose constructors are the inference rules. Proofs by induction on derivations, can then be constructed as functions taking an argument of type `Deriv`, defined recursively by case distinction on the inference rule used last.

### 2 The Lambda-Cube

This section is not essential and is included mainly in order to clarify how dependent type theory relates to other extensions of the STLC, in particular to universal and existential types discussed in TAPL chapters 23-24.

Dependent type theory arises essentially by extending the STLC with 3 features. These features can be considered separately, so the STLC can be extended with any of the `2^3 = 8` feature subsets, yielding 8 different languages. These languages are sometimes represented as the corners of a cube called the lambda-cube; the 3 dimensions then correspond to the 3 features. One corner of the cube is then the STLC - lacking all three features - and the opposite corner - having all three features - is the Calculus of Constructions, one particular flavour of dependent type theory.

Each of the features introduces a new lambda-abstraction rule, creating a new class of functions. In the STLC, we have lambda-abstraction for functions sending terms to terms:

```
Γ, x : A ⊢ b : B
-----------------------
Γ ⊢ λ(x : A).b : A -> B
```

The other features will be concerned with functions whose input and/or output are types or type operators. Before we can discuss these, we need to introduce the notion of *kinds*, which classify types and type operators. We will write `T :: K` (with a double colon) to say that type (operator) `T` has kind `K`. We need at least one kind, namely the kind `*` of types, e.g. `Bool :: *`.

#### 2.1 Type operators: Sending types to types

A first thing we can allow is the creation of **type operators** sending types (or type operators) to types (or type operators):

```
Γ, X :: K ⊢ T :: K'
-------------------------
Γ ⊢ Λ(X :: K).T : K -> K'
```

The **kind** of the above lambda-abstraction is the function kind `K -> K'`.

For example, the programming language Haskell features the `State` monad. A program of type `State S A` is a program that computes a value of type `A` using a single mutable variable of type `S` but is otherwise pure. Using type-level lambda-abstraction, we could define

```
State :: * -> * -> *
State = Λ(S :: *).Λ(A :: *).(S -> S × A)
```

and by consequence, `State S A = S -> S × A`, i.e. a stateful computation is just a function that takes an initial state and produces a final state and a return value.

Note the subtle difference between `Λ` and `->`: the lambda abstractions `Λ(S :: *)` and `Λ(A :: *)` indicate that `State` *itself* takes two arguments `S` and `A` of kind `*`. The function type `S -> ...` indicates that the *elements* of `State S A` take an argument of type `S`.

Type operators are discussed in TAPL chapter 29 [^TAPL].

#### 2.2 Polymorphic functions: Sending types to terms

Secondly, we can consider **polymorphic functions** sending types (or type operators, if that extension is available) to terms:

```
Γ, X :: K ⊢ b : B
-----------------------
Γ ⊢ Λ(X :: K).b : ∀(X :: K).B
```

Here, it is important that the type `B` is allowed to mention the variable `X`. The **type** of the above lambda-abstraction is the so-called **universal type** `∀(X :: K).B`, which universally quantifies over the kind `K`.

Examples of polymorphic functions are polymorphic list operations, which are agnostic to the type of the elements of the lists involved:

```
nil : ∀(X :: *).List X
cons : ∀(X :: *).X -> List X -> List X
isnil : ∀(X :: *).List X -> Bool
```

An example of a polymorphic function definable by lambda-abstraction is the polymorphic identity function:

```
id : ∀(X :: *).X -> X
id = Λ(X :: *).λ(x : X).x
```

The STLC extended with polymorphic functions is called System F or the polymorphic lambda-calculus and is discussed in TAPL chapter 23 [^TAPL]. In System F, the only kind is `*` so we have only polymorphism w.r.t. types. If we further extend with type operators, we obtain System Fω, which is discussed in TAPL chapter 30.

#### 2.3 Dependent types: Sending terms to types

Finally, we can consider functions sending terms `x` to types `P(x)`:

```
Γ, x : A ⊢ T :: K
-----------------------
Γ ⊢ λ(x : A).T :: A -> K
```

The **kind** of a dependent type is a function kind, whose domain is merely a type.

Due to the introduction of type dependency, the usual term-to-term lambda-abstraction from the STLC can actually create dependent functions:

```
Γ, x : A ⊢ T :: K
Γ, x : A ⊢ t : T
-----------------------
Γ ⊢ λ(x : A).t : Π(x : A).T
```

The type of a dependent function is a Π-type, also called a dependent function type. In Agda, it is denoted `(x : A) -> T` or `∀(x : A) -> T` or `∀ x -> T` when the domain `A` can be inferred. When `T` does not depend on `x`, i.e. when we are not using type dependency, then we can also resort to the original notation `A -> T`. Because of the collateral appearance of the Π-type, the STLC extended with dependent types is called the λΠ-calculus.

Under the Curry-Howard correspondence, a type `P(x)` depending on `x` can be regarded as a proposition which says something about `x`, i.e. a dependent type `P :: A -> *` can be regarded as a predicate on `A`. Due to this ability to make and prove statements about terms, the λΠ-calculus is also called the logical framework (LF).

An example of a function sending terms to types is `Vec :: * -> Nat -> *`. Using products and the unit type, we could even define it recursively:

```
Vec :: * -> Nat -> *
Vec A 0 = Unit
Vec A (suc n) = A × Vec A n
```

However, note that `Vec` also takes a type argument, so this example also requires the existence of type operators.

#### 2.4 The universe `Set`

Dependent type theory requires not just the third feature (dependent types) but also type-level operators and polymorphic functions. If we have all of them, then both terms and type operators can depend on both terms and type operators, so there is no longer any need to distinguish between them. Hence, we can abolish the distinction between the typing judgement for terms `Γ ⊢ a : A` and the kinding judgement for type operators `Γ ⊢ T :: K`, and simply view `T` as a term and `K` as a type. At that point, the notation `*` for the type of types becomes more unusual and we will instead write `Set`. The type `Set` is the type of types and is also known as the **universe**.[^hierarchy]

### 3 Inference rules of dependent type theory

In this section, we formally specify dependent type theory. Specifically, we consider Martin-Löf type theory (MLTT [^MLTT]) which is the flavour of dependent type theory that Agda is arguably based on. The differences between variants of dependent type theory (MLTT, CoC, pure type systems, …) are quite subtle and will not be discussed here further.

Again, the goal is not to use this as a basis for a metatheoretical study of dependent type theory, but rather to provide you with a specification that you can use as a reference to understand what's going on when using a dependently typed language.

#### 3.1 Judgement forms

In the STLC, types can be defined by a simple grammar and contexts are just lists of types (assuming a nameless representation of variables; alternatively, they are lists of typed variables), so the only truly interesting judgement is the term judgement `Γ ⊢ t : T`. In dependent type theory, both the type on the right of the turnstyle (`⊢`) and the types of the variables listed in the context, can refer to terms, including previously introduced variables, so well-formedness of contexts and types becomes a cause of concern. For this reason, in MLTT, we consider the following judgement forms:

* `Γ ctx` - `Γ` is a well-formed context,

* `Γ ⊢ T type` - `T` is a well-formed type in context `Γ`,

* `Γ ⊢ t : T` - `t` is a well-typed term of type `T` in context `Γ`.

Under the Curry-Howard correspondence, the latter two judgements may also be read as:

* `Γ ⊢ T type` - `T` is a well-formed proposition in context `Γ`,

* `Γ ⊢ t : T` - The proposition `T` is true in context `Γ`, as is evident from the well-formed proof `t`.

Note in particular that it is impossible to assert the proposition `T` without providing evidence for it: it is by providing evidence that we assert that a proposition is true.

##### Presupposition

You might wonder what `Γ ⊢ T type` means in case `Γ` is *not* a well-formed context. Generally, judgements of dependent type theory are read according to the principle of presupposition. What is means is that it is considered illegal to state `Γ ⊢ T type` if `Γ` is not already a well-formed context. The act of uttering a type-judgement already presupposes derivability of the corresponding context judgement. Similarly, the judgement `Γ ⊢ t : T` presupposes `Γ ⊢ T type` and hence also `Γ ctx`. So to be clear:

* `Γ ⊢ T type` does **not** mean: "`Γ` is a well-formed context **and** `T` is a well-formed type in context `Γ`."

* `Γ ⊢ T type` does **not** mean: "**If** `Γ` is a well-formed context **then** `T` is a well-formed type in context `Γ`."

* `Γ ⊢ T type` **does** mean: "`T` is a well-formed type in context `Γ`, which we already knew or were already assuming was well-formed."

#### 3.2 Contexts

Contexts in MLTT are still lists of types (assuming a nameless representation of variables) or lists of typed variables (otherwise), but what is important is how we restrict the appearance of variables in types of variables.

If we read a derivation-tree of a program bottom-up, then we start in the empty context, and we add a variable to the context whenever we move under a binder. As such, the order of the variables in the context is clearly meaningful. Moreover, it is also clear that the binder is being type-checked in a certain context, namely the context consisting of all previously bound variables. This is exactly the discipline that we will enfore: the type of every variable in the context, can depend on any previously bound variables, i.e. any variables to its left.

Unsurprisingly, formation of contexts starts with the empty context. This is a typing rule without premises:

```
-----
Ø ctx
```

Subsequently, we can extend a context `Γ` with a variable `x : T`, where `T` must be well-formed in context `Γ`:

```
Γ ctx (presupposed)
Γ ⊢ T type
------------
Γ, x : T ctx
```

Because the first premise `Γ ctx` is evidently needed for the second premise to be even statable (by the principle of presupposition), it is often omitted in presentations of dependently typed systems.

#### 3.3 The dependent function type

Dependent functions are functions whose output *type* may depend on the input *value*. For example, we could create a function that creates a vector of any given length, intialized with zeroes:

```agda
zeroes : (n : Nat) -> Vec Nat n
zeroes 0 = nil
zeroes (suc n) = cons 0 (zeroes n)
```

Now the type `Vec Nat n` of `zeroes n` depends on the precise argument `n` we have provided. For the function type to be well-formed, the domain can use any variables currently in scope, and the codomain can use one additional variable, namely the one referring to the functions argument:

```
Γ ctx       (presupposed)
Γ ⊢ T1 type (presupposed)
Γ, x : T1 ⊢ T2 type
---------------------
Γ ⊢ Π(x : T1).T2 type
```

This type is called the dependent function type or Π-type. It is alternatively denoted `(x : T1) -> T2`. When `T2` does not depend on `x`, we simply write `T1 -> T2` instead.

Possible Agda notations are:

* `(x : T1) -> T2`

* `∀ (x : T1) -> T2`

* `∀ x -> T2` (when `T1` can be inferred)

* `T1 -> T2` (when `T2` does not depend on `T1`)

Note that both the domain `T1` and the codomain `T2` may or may not be `Set` (or built from `Set`), so that the above function type encompasses all function types available in the languages of the lambda-cube:

* Ordinary non-dependent term-level functions, e.g. `iszero : Nat -> Bool`,
* Polymorphic functions, e.g. `id : (X : Set) -> X -> X`,
* Type operators, e.g. `State : Set -> Set -> Set`,
* Dependent types, e.g. `Vec Bool : Nat -> Set`,
* Dependent term-level functions, e.g. `zeroes : (n : Nat) -> Vec Nat n`.

The abstraction rule looks quite familiar, of course with adapted type:

```
Γ ctx               (presupposed)
Γ ⊢ T1 type         (presupposed)
Γ, x : T1 ⊢ T2 type (presupposed)
Γ, x : T1 ⊢ t : T2
------------------------------
Γ ⊢ λ(x : T1).t : Π(x : T1).T2
```

Often, we omit the type label on the binder and simply write `λx.t`. Some possible Agda notations are:

* `λ(x : T1) -> t`

* `λ x -> t` (when `T1` can be inferred)

Finally, we have the application rule, which applies a function to a concrete term. Since the output type depends on the argument, we need to substitute the provided argument in the type:

```
Γ ctx               (presupposed)
Γ ⊢ T1 type         (presupposed)
Γ, x : T1 ⊢ T2 type (presupposed)
Γ ⊢ f : Π(x : T1).T2
Γ ⊢ t : T1
--------------------
Γ ⊢ f t : [x ↦ t]T2
```

##### Example: The type of `cons`

We now know enough to derive well-formedness of the type of `cons`, which is

```agda
cons : (X : Set) -> X -> List X -> List X
```

Recall that `A -> B` is syntactic sugar for `(x : A) -> B` where `B` does not depend on `x`.

It is derived as follows:

```
              -----------------------------------------
              X : Set, x : X, xs : List X ⊢ X : Set
              -----------------------------------------
              X : Set, x : X, xs : List X ⊢ X type
              -----------------------------------------
              X : Set, x : X, xs : List X ⊢ List X type
                                       :
----------------------------           :
X : Set, x : X ⊢ X : Set               :
----------------------------           :
X : Set, x : X ⊢ X type                :
----------------------------           :
X : Set, x : X ⊢ List X type           :
----------------------------------------------------
              X : Set, x : X ⊢ List X -> List X type
                                       :
              -----------------        :
              X : Set ⊢ X : Set        :
              -----------------        :
              X : Set ⊢ X type         :
----------    ------------------------------------
⊢ Set type    X : Set ⊢ X -> List X -> List X type
--------------------------------------------------
⊢ (X : Set) -> X -> List X -> List X type
```

##### Implicit arguments

Agda has a feature called implicit arguments. We emphasize that this is merely a usability feature and is typically absent in theoretical presentations of type theory. All it does is allowing users to declare certain arguments as implicit, which allows you to omit them in both abstractions and applications. The syntax for implicit arguments is:

* For function types:
   * `{x : T1} -> T2`
   * `∀ {x : T1} -> T2`
   * `∀ {x} -> T2` (when `T1` can be inferred)
* For abstraction:
   * `λ {x : T1} -> t`
   * `λ {x} -> t` (when `T1` can be inferred)
   * `t` (infer the abstraction altogether)
* For application:
   * `f {t}`
   * `f {x = t}` (use value `t` for argument `x` when `f` takes multiple implicit arguments)
   * `f` (when the argument can be inferred)

Of course, this feature only works if Agda is able to infer the given arguments. For example, if I declare addition of natural numbers with implicit arguments:

```agda
_+_ : {x y : Nat} -> Nat
```

and then write `_+_ : Nat`, leaving the operands implicit, then Agda will have a hard time inferring these. Conversely, if I define the aforementioned function `zeroes` with an implicit argument:

```agda
zeroes : {n : Nat} -> Vec Nat n
```

and then write `zeroes` where a value of type `Vec Nat 3` is required, then Agda will infer that I mean `zeroes {3}`. As such, implicit arguments are a usability feature that is usable thanks to dependent types, but in principle can be considered regardless of type dependency.

##### Relation to pair, tuple and record types

TAPL §11.6-8 explain how pair types generalize to tuple types and subsequently to record types. Essentially, the pair type `T₁ × T₂` is the binary product of two types `T₁` and `T₂`. Tuple types are then simply `n`-ary products of `n` potentially different types, and record types are `L`-ary products of an `L`-indexed collection of types, where `L` is a metatheoretic set of field labels.

In each instance, elements of the product type (pairs, tuples, records) are created by assigning to every metatheoretic index `i ∈ I` (where `I` is, respectively, the metatheoretic set `{1, 2}`, `{1, ..., n}` or `L`) a term `tᵢ : Tᵢ`.

Conversely, given an element of the product type (a pair, tuple, or record), we can extract one component for every index `i`.

What we have to do in order to transition from pair/tuple/record types to Π-types is *internalizing* the index set `I`. Indeed, to construct an element of type `Π(i : I).T i`, we need to assign to each internal index `i : I` a term `t i : T i`, thus creating a dependent function (internal tuple) `λ(i : I).t i`.

Conversely, given an element of the Π-type `f : Π(i : I).T i`, we can extract one component `f i` for every internal index `i : I`, simply by function application.

Some authors confusingly call the Π-type the dependent product type. A better name would be the "internal-ary" product type because what changes w.r.t. the binary product type `T₁ × T₂` is not dependency of `Tᵢ` on `i`, but the arity.

##### Relation to non-dependent functions

In mathematics, if we take the product of always the same number, we call this a power. The type-theoretic equivalent is taking the product of always the same type, i.e. `Π(i : I).T` where `T` does not depend on `I`. This type is simply denoted `I -> T` and called a (non-dependent) function type. In category theory, it is called an exponential object and denoted `Tᴵ`.

#### 3.4 The dependent pair type

Dependent pairs are pairs whose second component's *type* depends on their first component's *value*. For example, we could define the type `List A` of lists of arbitrary length as `Σ(n : Nat).Vec A n`. Then to give a list of arbitrary length, we first need to decide on a specific length, and then give a vector of that specific length. A list of 3 elements would be given by `(3, cons a1 (cons a2 (cons a3 nil)) ) : (n : Nat) × Vec A n` where indeed the second component has type `Vec A 3`.

The type formation rule is almost identical to that of the Π-type:

```
Γ ctx       (presupposed)
Γ ⊢ T1 type (presupposed)
Γ, x : T1 ⊢ T2 type
---------------------
Γ ⊢ Σ(x : T1).T2 type
```

This type is called the dependent pair type or Σ-type. It is alternatively denoted `(x : T1) × T2`. When `T2` does not depend on `x`, we simply write `T1 × T2` instead.

When using the Agda standard library, the notation for the Σ-type is `Σ[ x ∈ T1 ] T2` (with that exact usage of whitespace) or, in the non-dependent case, `T1 × T2`.

Pairs are simply formed by providing both components, where the first component will be substituted into the type of the second component:

```
Γ ctx               (presupposed)
Γ ⊢ T1 type         (presupposed)
Γ, x : T1 ⊢ T2 type (presupposed)
Γ ⊢ t1 : T1
Γ ⊢ t2 : [x ↦ t1]T2
----------------------------
Γ ⊢ (t1 , t2) : Σ(x : T1).T2
```

The rule for the first projection is quite straightforward:

```
Γ ctx               (presupposed)
Γ ⊢ T1 type         (presupposed)
Γ, x : T1 ⊢ T2 type (presupposed)
Γ ⊢ p : Σ(x : T1).T2
--------------------
Γ ⊢ fst p : T1
```

For the second projection, we substitute the first projection into the type:

```
Γ ctx               (presupposed)
Γ ⊢ T1 type         (presupposed)
Γ, x : T1 ⊢ T2 type (presupposed)
Γ ⊢ p : Σ(x : T1).T2
--------------------
Γ ⊢ snd p : [x ↦ fst p]T2
```

##### Relation to sum and variant types

TAPL §11.9 introduces the sum type `T₁ + T₂`, also called coproduct, disjoint union or tagged union. An alternative notation used in the Agda standard library is `T₁ ⊎ T₂`. The name tagged union derives from the fact that values of `T₁ + T₂` are just values of either `T₁` or `T₂`, tagged with the constructors `inl` and `inr` to remember where they come from. As such, even for non-disjoint types, the sum operation acts as a disjoint union as overlap is avoided by appending the tags.

TAPL §11.10 explains how the sum type generalizes to the variant type, which forms the coproduct of an `L`-indexed collection of types, where `L` is a metatheoretic set of (co)field labels or tags.

Both for sums and variants, elements are created by choosing a metatheoretic label `i ∈ I` (where `I` is either the metatheoretic set `{1, 2}` or the label set `L`) and then providing a term `t : Tᵢ`.

To create a function from the sum or variant type to a type `C`, we work by case analysis on the tag: we need to provide for every `i ∈ I` a function `fᵢ : Tᵢ -> C`.

By internalizing the set of tags `I` and requiring it to be a type, we arrive at the Σ-type `Σ(i : I).T i`. To create an element, we pick a label `j : I` and provide a term `t : T j`, and pair them up as `(j , t) : Σ(i : I).T i`.

To create a function `(Σ(i : I).T i) -> C`, we can work by case analysis. We need to provide for every `i : I` a function `f i : T i -> C`. Since `I` is internal, these can be wrapped up in a single dependent function `f : Π(i : I).T i -> C`. Then we can uncurry `f` to obtain `λp . f (fst p) (snd p) : (Σ(i : I).T i) -> C`.

Some authors confusingly call the Σ-type the dependent sum type. A better name would be the "internal-ary" sum type because what changes w.r.t. the binary sum type `T₁ + T₂` is not dependency of `Tᵢ` on `i`, but the arity.

##### Relation to non-dependent pair types

In mathematics, if we take the sum of always the same number, we call this a product. The type-theoretic equivalent is taking the sum of always the same type, i.e. `Σ(i : I).T` where `T` does not depend on `I`. This type is simply denoted `I × T` and called a (non-dependent) pair type.

##### Dependent record types

We've seen that the Σ-type or dependent pair type generalizes the non-dependent pair type. Another generalization of the non-dependent pair type is the record type. These generalizations can be combined, yielding dependent record types.

To specify a dependent record type with `n` fields in context `Γ`, we need to provide:

* a metatheoretic *list* of field names `l₁`, …, `lₙ` (not a set; the order is important),

* for each field `lᵢ`, a type `Tᵢ` in context `Γ, x₁ : T₁, ..., xᵢ₋₁ : Tᵢ₋₁`.

Then in order to inhabit that record type, we need to provide:

* for each field `lᵢ`, a term `tᵢ` of type `[x₁ ↦ t₁, ..., xᵢ₋₁ ↦ tᵢ₋₁]Tᵢ`.

From a tuple `p` of the dependent record type, we can extract a component `p.lᵢ` of type `[x₁ ↦ p.l₁, ..., xᵢ₋₁ ↦ p.lᵢ₋₁]Tᵢ`.

An example is the type of monoids, definable in Agda:

```agda
record Monoid : Set₁ where
  constructor mkMonoid
  field
    Carrier : Set
    mempty : Carrier
    _<>_ : Carrier -> Carrier -> Carrier
    lunit : {x : Carrier} -> mempty <> x ≡ x
    runit : {x : Carrier} -> x <> mempty ≡ x
    assoc : {x y z : Carrier} -> ((x <> y) <> z) ≡ (x <> (y <> z))
```

We have listed 6 fields, and each field's type is allowed to refer to the values of the previous fields. When we create an instance, we first have to decide upon the carrier. This carrier will then be substituted into the types of all the following fields. Conversely, given a monoid instance `m`, the neutral element `m .mempty` will have type `m .Carrier`.

Just like record types can be straightforwardly desugared to nested product types, dependent record types can be desugared to nested Σ-types. For instance, the `Monoid` type would desugar to `Σ(Carrier : Set).Σ(mempty : Carrier).{!etcetera!}`.

#### 3.5 The universe

Agda features a type of all types `Set`, called the universe. [^hierarchy] Its formation rule simply says that, regardless of what variables are in scope, the universe exists:

```
Γ ctx
------------
Γ ⊢ Set type
```

There are introduction rules corresponding to all type formation rules, for example there is a variant of the formation rule of the Π-type where all type judgements - both premises and conclusion - have to be replaced by corresponding term judgements of type `Set`.

Then there is a rule asserting that every element of `Set` is, in fact, a type:

```
Γ ctx (presupposed)
Γ ⊢ T : Set
-----------
Γ ⊢ El T type
```

The operation `El` is generally omitted, i.e. we generally write `T` instead of `El T`. In Agda, `El` is always omitted.

#### 3.6 Data types

Agda supports data type declarations. For instance, we can define the type of lists:

```agda
data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A
```

While data type spawning combinators have been researched, data type declarations are most often regarded not as part of dependent type theory, but rather as extensions of the system. In other words, by writing the above lines in an Agda file, we are *extending* the type system that Agda applies to our code with a couple of inference rules.

First of all, we get a type formation rule:

```
Γ ctx (presupposed)
Γ ⊢ A type
-----------
Γ ⊢ List A type
```

We also get rules for the constructors:

```
Γ ctx (presupposed)
Γ ⊢ A type (presupposed)
------------------------
Γ ⊢ nil : List A
```

```
Γ ctx (presupposed)
Γ ⊢ A type (presupposed)
Γ ⊢ a : A
Γ ⊢ as : List A
------------------------
Γ ⊢ cons a as : List A
```

Finally, there is a so-called elimination rule, which allows to create a function `(xs : List A) -> C` (where `C` may depend on `xs`) by list induction:

```
Γ ctx (presupposed)
Γ ⊢ A type (presupposed)
Γ ⊢ as : List A
Γ, xs : List A ⊢ C type
Γ ⊢ cnil : [xs ↦ nil]C
Γ, y : A, ys : List A, ihyp : [xs ↦ ys]C
    ⊢ ccons : [xs ↦ cons y ys]C
--------------------------------
Γ ⊢ case as return xs.C of {
      nil ↦ cnil
      cons y (ys ↦ ihyp) ↦ ccons
    } : [xs ↦ as]C
```

The syntax used for the dependent eliminator is not accepted by Agda (although it is inspired by the `case_return_of_` operation available in the standard library) but serves to make clear what all the parts mean.

In the above rule, `as` is the list that we want to prove satisfies the property `C` by induction. The `return` clause serves to specify the property `C` that we want to prove; this property need not only be defined for `as` but rather for an arbitrary list `xs`, so that it can be considered for smaller lists in the inductive argument. `cnil` is the proof that `nil` satisfies `C`. `ccons` is the proof that `cons y ys` satisfies `C` if `ys` does (as witnessed by the induction hypothesis `ihyp`).

Note that if `C` does not actually depend on `xs`, then this scheme simplifies to list recursion.

In Agda, we usually do not use dependent eliminators directly. Instead, Agda features an (in practice) much more powerful pattern matching system that is (or should be) non-straightforwardly desugarable to applications of dependent eliminators. [^cockx-phd]

### 4 The Curry-Howard correspondence

For now, we refer to the overview sheet.

### 5 Equality

#### 5.1 Motivation

If we know that term `t` has type `Vec A (2 + 3)` and we need something of type `Vec A 5`, can we use `t`?

More generally, if we know that term `t` has type `T1` and we need something of type `T2`, which we know is equal, can we use `t`?

These questions cannot be answered before we know what "equal" means. Since types can now depend on terms, we need to know in particular what equality means for terms. Here are some properties that would be nice to have:

1. Equality should be an equivalence relation, i.e. reflexive, symmetric and transitive,

2. Equality should be a congruence, i.e. respected by any operation our language provides,

3. If one term reduces to another, then they should be regarded as equal,

4. If two terms of the same pair/tuple/record type have equal projections, then they should be regarded as equal,

5. If two terms `f1` and `f2` of the same function type are pointwise equal, i.e. `f1 x` equals `f2 x` where `x` is a fresh variable in the functions' domain, then they should be regarded as equal,

6. If it is assumed in the context that two terms are equal, then they should be regarded as equal,

7. More generally, if it can be proven from the context that two terms are equal, then they should be regarded as equal.

We can start by remarking that it is hard to have (6) without having (7). Indeed, if context `Γ` proves `t1 ≡ t2`, i.e. `Γ ⊢ e : t1 ≡ t2` (where `e` is the proof) then any judgement `Γ, x : t1 ≡ t2 ⊢ J` can be substituted to become `Γ ⊢ [x ↦ e]J`. Now in the extended context, we have the *assumption*, so according to (6) we expect that `t1` and `t2` will be equal. But it would be problematic if substitution (which can be triggered by function application) were to break equality. So `t1` and `t2` should also be equal in context `Γ`.

Now property (7) seems a bit strong and in fact it is: it turns out that the equality relation generated by (roughly) the above requirements, which we will call **propositional equality**, is undecidable. [^hofmann-phd] 

So to answer our question:

> If we know that term `t` has type `T1` and we need something of type `T2`, which we know is equal, can we use `t`?

The answer is: No, not in general, not if you want type-checking to be algorithmic.

However, we do not want to give up on the earlier question:

> If we know that term `t` has type `Vec A (2 + 3)` and we need something of type `Vec A 5`, can we use `t`?

which does not rely on properties (6) and (7). It turns out that the equality relation generated by properties 1-5 is in fact decidable and even has computable normal forms. This relation is called **judgemental** or **definitional equality**. This notion of equality is added to the type system in the form of two additional judgement forms:

* `Γ ⊢ t1 = t2 : T` - Terms `t1` and `t2` of type `T` are judgementally equal.
  
  This presupposes `Γ ⊢ t1 : T` and `Γ ⊢ t2 : T`, and hence also `Γ ⊢ T type` and `Γ ctx`.

* `Γ ⊢ T1 = T2 type` - Types `T1` and `T2` are judgementally equal.
  
  This presupposes `Γ ⊢ T1 type` and `Γ ⊢ T2 type` and hence also `Γ ctx`.

A positive answer to our second question is ensured by the conversion rule, which allows us to coerce terms between judgementally equal types:

```
Γ ⊢ t : T1
Γ ⊢ T1 = T2 type
----------------
Γ ⊢ t : T2
```

#### 5.2 Judgemental equality

1. There are inference rules to enforce reflexivity, symmetry and transitivity of both equality judgements, e.g.
   
   ```
   Γ ⊢ T1 = T2 type
   ----------------
   Γ ⊢ T2 = T1 type
   ```

2. For every inference rule for terms and for types, there is a counterpart expressing that it respects judgemental equality, e.g.
   
   ```
   Γ ⊢ a = a' : A
   Γ ⊢ as = as' : List A
   ---------------------
   Γ ⊢ cons a as = cons a' as' : List A
   ```
   
   In particular, there is a counterpart for the `El` rule:
   
   ```
   Γ ⊢ T = T' : Set
   ----------------
   Γ ⊢ El T = El T' type
   ```

3. For every redex (reducible expression), there is a so-called **β-rule** expressing that the redex (called β-redex) is equal to its reduced form, e.g.
   
   ```
   Γ, x : T1 ⊢ t2 : T2
   Γ ⊢ t1 : T1
   -------------------
   Γ ⊢ (λx.t2) t1 = [x ↦ t1]t2 : [x ↦ t1]T2
   ```

4. For the Σ-type and every user-defined record-type, there is a so-called **η-rule** expressing that the record is equal to its η-expansion, which is the pair/tuple/record of all its projections:
   
   ```
   Γ ⊢ p : Σ(x : T1).T2
   --------------------
   Γ ⊢ p = (fst p , snd p) : Σ(x : T1).T2
   ```
   
   In the standard library, the unit type is defined as a record type with zero fields. The η-law then expresses that any term of that type is equal to `tt`.

5. Similarly, there is an **η-rule** for the function type:
   
   ```
   Γ ⊢ f : Π(x : T1).T2
   --------------------
   Γ ⊢ f = λx.(f x) : Π(x : T1).T2
   ```

These 5 collections of rules generate the judgemental equality relation. Then if we use a term `t : T1` in a hole where a term of type `T2` is required, Agda will check whether the conversion rule from §5.1 applies, i.e. whether `Γ ⊢ T1 = T2 type`. If yes, then the usage is accepted. If no, then Agda will issue a type error, typically mentioning inequality of corresponding subterms of `T1` and `T2`.

#### 5.3 Propositional equality

Whereas judgemental equality is a judgement, propositional equality is a proposition, i.e. a type. In Agda, it can be defined as an indexed data type, called the identity type or (propositional) equality type:

```agda
data _≡_ {A : Set} (x : A) : (y : A) → Set where
  instance refl : x ≡ x
```

(If you wonder why `x` appears before the colon and `y` appears after it: Variables introduced before the colon are *parameters* of the type family. They are chosen once and remain the same throughout the data type declaration. An example of a parameter is the element type `A` in `Vec A n`. The variables after the colon are *indices* of the type family and can be determined by individual constructors. An example of an index is the length index `n` in `Vec A n`, which is `0` for `nil` and `suc n` for `cons`. For the propositional equality type, the `refl` constructor determines that one hand of the equation must be equal to the other, so at least one hand of the equation must be treated as an index.)

Just as in §3.6, a data type declaration is treated as an extension to the theory and leads to a number of additional typing rules. First, we have the formation rule:

```
Γ ⊢ T type
Γ ⊢ t1 : T
Γ ⊢ t2 : T
----------
Γ ⊢ t1 ≡ t2 type
```

There is a single introduction rule:

```
Γ ⊢ T type
Γ ⊢ t : T
----------
Γ ⊢ refl : t ≡ t
```

This rule expresses that propositional equality is reflexive, but in fact it means more. Indeed, by combining the `refl` rule and the conversion rule, we can deduce that judgemental equality implies propositional equality. Indeed, assume `Γ ⊢ t1 = t2 : T`:

```
---------------        (assumption)       (presupposed)
Γ ⊢ t1 = t1 : T        Γ ⊢ t1 = t2 : T    Γ ⊢ t1 : T
--------------------------------------    ------------------
Γ ⊢ (t1 ≡ t1) = (t1 ≡ t2) : T             Γ ⊢ refl : t1 ≡ t1
------------------------------------------------------------
Γ ⊢ refl : t1 ≡ t2
```

Another way to put this is the following: due to the conversion rule, types do not distinguish between judgementally equal terms. Thus, types do not speak about syntactic terms, but about terms up to judgemental equality. `refl` proves that any term - considered up to judgemental equality - is propositionally equal to itself. In the above derivation, `t1` and `t2` are the same up to judgemental equality, hence `refl` applies.

We would like propositional equality to also satisfy property (2):

> Equality should be a congruence, i.e. respected by any operation our language provides,

This is expressed by the dependent eliminator, called the J-rule:

```
Γ ctx (presupposed)
Γ ⊢ T type (presupposed)
Γ ⊢ t1 : T (presupposed)
Γ ⊢ t2 : T (presupposed)
Γ ⊢ e : t1 ≡ t2
Γ, x2 : T, w : t1 ≡ x2 ⊢ C type
Γ ⊢ crefl : [x2 ↦ t1 , w ↦ refl]C
--------------------------------
Γ ⊢ case (t2 , e) return x2.w.C of {
      (t1 , refl) ↦ crefl
    } : [x2 ↦ t2 , w ↦ e]C
```

What this says is the following: suppose that we want to prove a property `C` for a term `t2` which we know is propositionally equal to `t1` (as evidenced by `e`). The property `C` in general should mention an arbitrary term `x2 : T` which is known to be propositionally equal to `t1` (as evidenced by `w`, which `C` may in principle also mention although this is often not the case). Then it suffices to prove `C` in the situation where `w` is in fact `refl` and hence, `x2` is (judgementally equal to) `t1`. In the above rule, this proof is called `crefl`.

Again, in Agda we will rarely use the J-rule directly; instead, we will use the pattern matching infrastructure built on top of it.

Remarkably, with these few rules, propositional equality satisfies most of the desired properties:

1. Reflexivity is proven by `refl`. Symmetry and transitivity are provable by pattern matching.

2. To see that propositional equality is a congruence, apply the J-rule to a type `C` that mentions neither `t1` nor `w`, i.e. `C = P(x2)`. Then by proving `crefl : P(t1)`, the rule gives us a proof of `P(t2)`.

3. If one term reduces to another, then they are judgementally equal and hence, by the conversion rule, propositionally equal.

4. For pair, tuple and record types with a finite number of components, we can prove that records with equal fields are equal by pattern matching on each of the componentwise equality proofs. For tuple and record types with an infinite number of components (e.g. infinite streams), we need to postulate this property without proof.

5. For functions, we also need to postulate that pointwise equality implies equality, a property called **function extensionality**:
   
   ```agda
   postulate
     funext : {A : Set} {B : A -> Set}
              {f1 f2 : (x : A) -> B x}
              (p : (x : A) -> f1 x ≡ f2 x)
           -> f1 ≡ f2
   ```
   
   By postulating that the given type has an element, we postulate that the corresponding proposition is true. Logically, this has the desired effect of asserting the function extensionality. However, from a programming perspective, we have postulated the existence of a function without providing computational content. Normally, in type theory, every closed proof of propositional equality (closed meaning: in the empty context, not depending on any variables) should reduce to `refl`. This will not be the case for proofs making use of `funext`.

6. A context that assumes propositional equality of two terms `t1` and `t2` is one that contains a variable `w : t1 ≡ t2`. Then the propositional equality holds as proven by `w`:
   
   ```
   Γ, w : t1 ≡ t2, Δ ⊢ w : t1 ≡ t2
   ```

7. For propositional equality, this property is tautological, because the statement expressing that propositional equality of `t1` and `t2` is provable from context `Γ`, is the same judgement as the statement that the equality is true in context `Γ`, namely
   
   ```
   Γ ⊢ p : t1 ≡ t2
   ```

### 6 Normalization

Just like the STLC (TAPL chapter 12 [^TAPL]), dependent type theory satisfies a normalization result: closed well-typed terms reduce to values (of the same type) in a finite number of steps. From a programming perspective, this property is useful for the same reason it was useful in the STLC: it guarantees that our programs will not diverge. From a proving perspective, however, it has a number of interesting corollaries. First of all, notice that under the Curry-Howard correspondence, closed terms correspond to proofs not relying on any assumptions. Some corollaries are:

* Closed propositional equality proofs `⊢ e : t1 ≡ t2` reduce to `⊢ refl : t1 ≡ t2`, well-typedness of which implies that `t1` and `t2` are actually *judgementally* equal.

* Closed proofs of falsity `⊢ e : ⊥` reduce to a value `⊢ v : ⊥`. Since `⊥` has zero constructors, there are no values of type `⊥`, so there cannot be any closed proofs of falsity. This means that dependent type theory is consistent: we cannot prove falsity without making any assumptions.

In §3.6, we presented the typing rule for the dependent list eliminator, which allows writing proofs by recursion or induction on a list. As mentioned, in Agda we do not usually use such dependent eliminators. Instead, Agda provides a pattern matching mechanism that is in practice much more powerful. Using it, we could for example define list concatenation as follows:

```agda
_++_ : {X : Set} -> List X -> List X -> List X
nil ++ ys = ys
(cons x xs) ++ ys = cons x (xs ++ ys)
```

What is remarkable here is that the definition of `_++_` refers to itself. If Agda would allow such self-references without any constraints, then clearly we could write diverging definitions, such as

```agda
_+++_ : {X : Set} -> List X -> List X -> List X
xs +++ ys = xs +++ ys
```

This would allow, in particular, proving falsity:

```agda
undefined : ⊥
undefined = undefined
```

To keep programs terminating and to keep Agda (reasonably) consistent, there is a termination checker. The termination checker approves of a self-referencing program if there is one argument that is always smaller in recursive calls than in the parent call. For example, in the definition of `_++_`, the recursive call is accepted because we are doing correct recursion on the first argument: the argument `xs` is a strict subterm of the first argument to the parent call `cons x xs`. This guarantees termination, e.g.:

```
              cons 1 (cons 2 (cons 3 (nil)))    ++ cons 4 nil
= cons 1 (            cons 2 (cons 3 (nil))     ++ cons 4 nil   )
= cons 1 (cons 2 (            cons 3 (nil)      ++ cons 4 nil   ))
= cons 1 (cons 2 (cons 3 (            nil       ++ cons 4 nil   )))
= cons 1 (cons 2 (cons 3 (cons 4 nil)))
```

### 7 Other concepts and further reading

ATTAPL [^ATTAPL], the sequel to TAPL [^TAPL], also contains a chapter on dependent type theory.

There are multiple flavours of dependent type theory. Agda is roughly based on Martin-Löf type theory (MLTT [^MLTT]), whereas Coq is based on the Calculus of Constructions (CoC [^CoC]). Pure type systems are a class of possibly dependent languages, including all languages in the lambda-cube, specified by a collection of "sorts" (in the lambda-cube, the sorts are "type" and "kind"), a collection of "axioms" creating a hierarchy (e.g. "the sort of types is a kind"), and a collection of "rules" for creating functions (e.g. "for every domain kind and codomain type, there is a function type" leading to universal types).

The derivation structure of dependent type theory is complex: every judgement form can be a premise to any other judgement form, while the principle of presupposition means that one judgement needs to be derived before another can be stated. In order to formalize dependent type theory in dependent type theory, we need a mutually defined mutually dependent collection of inductive type families adhering to a scheme called induction-induction. If we treat judgemental equality not as a judgement, but as an equivalence relation on derivations to be quotiented out, then we are adhering to a scheme called quotient-induction-induction.[^tt-in-tt][^kovacs-phd]

The usual take on the propositional equality type is that it is a singleton when both hands are equal and empty otherwise. In homotopy type theory (HoTT [^hottbook]), this viewpoint is abandoned and the propositional equality type is instead viewed as the type of isomorphisms between both hands of the equation. For example, the type `Bool ≡ Bool` then contains two elements: the two endomorphisms of the booleans, given by the identity and the negation function.

The hardest part about implementing dependent type theory (without usability features such as holes and implicit arguments) is the equality checking algorithm required by the conversion rule. One way to tackle this problem is by putting both hands of the equality judgement to be checked in normal form (so-called βη-normal form or β-short η-long form) by reducing all β-redexes and η-expanding all pairs, tuples, records and functions. Implementing this algorithm is one thing, but then it remains non-trivial to prove that it is terminating (a normal form is computed in finite time), correct (every term is judgementally equal to its normal form) and complete (equal terms have syntactically equal normal forms - or α-equivalent normal forms if using a named representation of variables). Normalization by evaluation (NbE [^AMS95]), either syntactically (using logical relations) or via a categorical construction, is a technique applicable to lambda-calculi in general and usable as part of an implementation of dependent type theory in particular.

Dependent type theory is implemented by specialized languages like Agda, Coq, Idris, Lean, … Besides those, there is also retrofitted support for dependent types in Haskell (Dependent Haskell) and restricted support for "path-dependent" types in Scala. (The word "path" here has nothing to do with the notion of "paths" in HoTT.)

[^Σ-syntax]: For practical parsing reasons, Agda has a slightly clumsier syntax for the Σ-type. In Agda, we would write `Σ[ x ∈ A ] Proof (P(x))` instead of `Σ (x : A) . Proof (P(x))`, with that exact usage of whitespace.

[^hierarchy]: It is however inconsistent to have `Set : Set` as it allows for problematic self-references. Instead, Agda has a universe hierarchy `Set : Set₁ : Set₂ : ...`.

[^TAPL]: Pierce, Benjamin C. Types and programming languages. MIT press, 2002.

[^ATTAPL]: Pierce, Benjamin C., ed. Advanced topics in types and programming languages. MIT press, 2004.
Pierce, Benjamin C. Types and programming languages. MIT press, 2002.

[^cockx-phd]:
    ```bibtex
    @phdthesis{cockx-phd,
    author    = {Jesper Cockx},
    title     = {Dependent Pattern Matching and Proof-Relevant Unification},
    school    = {Katholieke Universiteit Leuven, Belgium},
    year      = {2017},
    url       = {https://lirias.kuleuven.be/handle/123456789/583556},
    timestamp = {Tue, 27 Jun 2017 16:33:36 +0200},
    biburl    = {https://dblp.org/rec/phd/basesearch/Cockx17.bib},
    bibsource = {dblp computer science bibliography, https://dblp.org}
    }
    ```

[^MLTT]:
    ```bibtex
    @incollection{ML84,
    title={Intuitionistic type theory},
    booktitle={Studies in proof theory},
    author={Martin-L\"of, Per},
    publisher={Bibliopolis},
    year={1984}
    }
    
    @incollection{ML98,
    title={An intuitionistic theory of types},
    author={Martin-L\"of, Per},
    booktitle= "Twenty-five years of constructive type theory",
    publisher= "Oxford University Press",
    year    = "1998",
    pages = {127-172}
    }
    ```

[^CoC]:
    ```bibtex
    @article{CoC,
    title = "The calculus of constructions",
    journal = "Information and Computation",
    volume = "76",
    number = "2",
    pages = "95-120",
    year = "1988",
    author = "Coquand, Thierry and Huet, G\'erard",
    }
    ```

[^hofmann-phd]: Martin Hofmann, Extensional concepts in intensional type theory, Ph.D. thesis, University of Edinburgh, (1995), https://ncatlab.org/nlab/files/HofmannExtensionalIntensionalTypeTheory.pdf

[^tt-in-tt]:
    ```bibtex
    @article{tt-in-tt,
    title={Type theory in type theory using quotient inductive types},
    author={Altenkirch, Thorsten and Kaposi, Ambrus},
    journal={ACM SIGPLAN Notices},
    volume={51},
    number={1},
    pages={18--29},
    year={2016},
    publisher={ACM New York, NY, USA}
    }
    ```

[^kovacs-phd]: András Kovács (2022), Type-Theoretic Signatures for Algebraic
Theories and Inductive Types, PhD thesis, Eötvös Loránd University, https://andraskovacs.github.io/pdfs/phdthesis_compact.pdf

[^hottbook]:
    ```bibtex
    @Book{hottbook,
    author =    {The {Univalent Foundations Program}},
    title =     {Homotopy Type Theory: Univalent Foundations of Mathematics},
    publisher = {\url{https://homotopytypetheory.org/book}},
    address =   {Institute for Advanced Study},
    year =      2013}
    ```

[^AMS95]: Altenkirch, Thorsten, Martin Hofmann, and Thomas Streicher. "Categorical reconstruction of a reduction free normalization proof." International Conference on Category Theory and Computer Science. Springer, Berlin, Heidelberg, 1995.
