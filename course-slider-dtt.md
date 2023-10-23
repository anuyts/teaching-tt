## Dependent type theory (DTT)

*Andreas Nuyts*

### 0 Intro

* STLC: Simply typed
* Chapter 23-24: `∀`, `∃`
   * Term variables `x : Bool`
   * Type (operator) variables `X`
* Dependent type systems
   * Types are "first class citizens"
   * Type of types `Set` (as in Agda, `Type` would be more logical)
   * Type variables `X : Set` are special case of term variables

Goal of this chapter:

* background information to help you to **use** DTT

**Not** the goal of this chapter:

* prove metatheorems about DTT (termination, consistency, decidability of typing, ...)
* understand how to implement a proof-assistant

### 1 Motivation

#### 1.1 Programming

* Dependently typed languages are **programming languages**
* Simple types: catch simple errors at compile time (e.g. no bool when number is expected)
* Dependent types: More subtle

##### Lists

Type `List A` in TAPL:

```
nil : List A
cons : A -> List A -> List A
```

Three-element list: `cons a1 (cons a2 (cons a3 nil))`.

Analyzing/using lists:

```
isnil : List A -> Bool
head : List A -> A
tail : List A -> List A
```

Problem: `head nil` and `tail nil` are not defined (stuck terms).

Possible solution:

```
fold : B -> (A -> B -> B) -> List A -> B
fold nilB consB nil = nilB
fold nilB consB (cons a as) = consB a (fold nilB consB as)
```

* `fold` is total
* but maybe we **know** that `xs` is non-empty and we want its `head`/`tail`

##### Vectors

Vectors are lists of given length:

```agda
data Vec (A : Set) : Nat -> Set where
  nil : Vec 0
  cons : {n : Nat} -> A -> Vec A n -> Vec A (suc n)
```

Compute `head`/`tail` when length is nonzero (i.e. successor of something):

```agda
head : {n : Nat} -> Vec A (suc n) -> A
head (cons a as) = a
tail : {n : Nat} -> Vec A (suc n) -> Vec A n
tail (cons a as) = as
```

No clauses for `nil` since `head nil` and `tail nil` are ill-typed.

#### 1.2 Proving

* Dependent type theory is a **constructive logic**.
   * Constructive: a proposition can only be asserted by providing evidence
* Proposition `A` is made up of logical connectives (and, or, not, implication, …).
* The type `Proof A` of evidence needed to assert `A` is defined by induction.

##### Conjunction

`Proof (A ∧ B) = Proof A × Proof B`

```
Γ |– a : Proof A
Γ |– b : Proof B
-------------------------------
Γ |– (a, b) : Proof A × Proof B
               = Proof (A ∧ B)
```

##### Existential quantification

`Proof (∃ (x : A) . P(x)) = Σ (x : A) . Proof (P(x))`

```
Γ |– a : A
Γ |– p : Proof(P(a))
--------------------------------------
Γ |– (a, p) : Σ (x : A) . Proof (P(x))
               = Proof (∃ (x : A) . P(x))
```

Note: Agda notation `Σ[ x ∈ A ] Proof (P(x))`

##### Propositions are types

* Above, we had `Proof : MathProp -> Set`
* Actually, we define
   * `MathProp = Set`
   * ```
     Proof : MathProp -> Set
     Proof A = A
     ```
   * `A ∧ B = A × B` etc.
* So propositions **are** types
* This correspondence is called the **Curry-Howard correspondence**.

##### Example

"If A implies (B or C), then (A and not B) implies C"

can be written as:

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

Property of constructive logic:

If for each `x ∈ X`, there exists some `y ∈ Y` such that `P x y`,

then there is a function `f : X -> Y` such that for each `x ∈ X`, we have `P x (f x)`.

```agda
property : {X Y : Set} {P : X -> Y -> Set} ->
  ((x : X) -> Σ[ y ∈ Y ] P x y) ->
  Σ[ f ∈ (X -> Y) ] ((x : X) -> P x (f x))
property p = ( λ x -> proj₁ (p x) , λ x -> proj₂ (p x) )
```

#### 1.3 Programs requiring evidence

##### Indexing a list

```agda
_!!_ : List A -> Nat -> A
cons a as !! 0 = a
cons a as !! suc n = as !! n
```

* Undefined for empty list
* Undefined when index out of bounds

##### Indexing a vector

* Use length-indexed vector type
* Provide evidence that index is within bounds

```agda
_!!_ : {n : Nat} -> Vec A n -> (Σ[ i ∈ Nat ] (i < n)) -> A
nil !! (i , ())
cons a as !! (0 , _) = a
cons a as !! (suc n , p) = as !! (n , decrement< p)
```

where `decrement< : {m n : Nat} -> (suc m < suc n) -> (m < n)`.

* Absurd clause for the empty list:
   * `i < 0` is absurd, so use absurd pattern `()`
   * no right-hand-side.

#### 1.4 Formalizing programming languages

##### Object/internal language and metalanguage

We can use DTT/Agda as a metatheory for the formalization of *another* language:

* **object/internal language:** the one we want to formalize.
   * e.g. Untyped/typed arithmetic, ULC, STLC, Web assembly, ...
* **metalanguage/metatheory:** DTT / Agda / set theory / ...
* Language confusion:
   * internal types vs metatypes
   * internal terms vs metaterms
   * internal judgements vs metajudgements
   * ...

##### Metatype of internal derivations

Thanks to (meta)type dependency, we can consider a (meta)type of internal derivations,

parametrized by an internal context, term and type:

```agda
IDeriv : ICtx -> ITerm -> IType -> Set
```

Now `IDeriv Γ t T` can be read as

* the metatype of internal derivations
* the metaproposition "The internal judgement `Γ ⊢ t : T` is derivable"
   * evidence (inhabitant) is a derivation tree.

Agda mixfix notation to write `Γ ⊢ t ∈ T` instead of `IDeriv Γ t T`:

```agda
_⊢_∈_ : ICtx -> ITerm -> IType -> Set
_⊢_∈_ = IDeriv
```

##### Inference rules

* Derivation trees are generated by inference rules
* `IDeriv` is a datatype (inductive type)
   * constructors are inference rules
* Proofs by induction on a derivation, are:
   * Agda functions taking argument of type `IDeriv`
   * Proceed by case distinction on the outer inference rule.

### 2 The Lambda-cube

This part

* is not essential to work with DTT
* is included to clarify how DTT relates to other extensions of STLC
   * in particular and `∀` and `∃` (ch 23-24)

DTT arises by extending STLC with 3 features.

* We can extend with any subset of these features -> `2^3 = 8` possibilities
  -> Corners of the Lambda-cube.
* Each feature introduces a new lambda-abstraction rule, creating a new class of functions.

#### 2.0 Simply-typed lambda-calculus (STLC)

STLC has lambda-abstraction for functions sending **terms** to **terms**:

```
Γ, x : A ⊢ b : B
-----------------------
Γ ⊢ λ(x : A).b : A -> B
```

The other abstraction rules have **types/type operators** as input and/or output.

* **Kinds** classify types & type operators.
* `T :: K` (double colon) means `T` has kind `K`.
* Kind of types is called `*`, e.g. `Bool :: *`

#### 2.1 Type operators (TAPL ch 29)

Sending **types/type operators** to **types/type operators**:

```
Γ, X :: K ⊢ T :: K'
-------------------------
Γ ⊢ Λ(X :: K).T : K -> K'
```

The **kind** of the above lambda-abstraction is the function kind `K -> K'`.

##### Example: State monad

A program of type `State S A` is a program that computes a value of type `A`
using a single mutable variable of type `S` but is otherwise pure.

Define:

```
State :: * -> * -> *
State = Λ(S :: *).Λ(A :: *).(S -> S × A)
```

so `State S A = S -> S × A`:

* input: initial state
* output: final state & return value

Derivation tree:

```
                                         -----------------------
                                         S :: *, A :: * ⊢ A :: *
                                                        :
                           -----------------------      :
                           S :: *, A :: * ⊢ S :: *      :
-----------------------    ----------------------------------
S :: *, A :: * ⊢ S :: *        S :: *, A :: * ⊢ S × A :: *
----------------------------------------------------------
S :: *, A :: * ⊢ S -> S × A :: *
-------------------------------------------------
S :: * ⊢ Λ(A :: *).(S -> S × A) :: * -> *
-------------------------------------------------
⊢ Λ(S :: *).Λ(A :: *).(S -> S × A) :: * -> * -> *
```

##### Type operators vs. function types

Subtle difference between `Λ` and `->`:

* `Λ(S :: *)` and `Λ(A :: *)` indicate that `State` *itself* takes two arguments `S` and `A` of kind `*`.
* The function type `S -> ...` indicates that the *elements* of `State S A` take an argument of type `S`.

#### 2.2 Polymorphic functions (ch 23)

Sending **types/type operators** so **terms**:

```
Γ, X :: K ⊢ b : B
-----------------------
Γ ⊢ Λ(X :: K).b : ∀(X :: K).B
```

* Important: type `B` can mention type variable `X`.
* The **type** of the above lambda-abstraction is the **universal type**`∀(X :: K).B`,
  which universally quantifies over the kind `K`.

##### Examples

Polymorphic list operations:

```
nil : ∀(X :: *).List X
cons : ∀(X :: *).X -> List X -> List X
isnil : ∀(X :: *).List X -> Bool
```

Polymorphic identity function:

```
id : ∀(X :: *).X -> X
id = Λ(X :: *).λ(x : X).x
```

##### System names

* STLC + polymorphic functions = System F a.k.a. the polymorphic lambda-calculus (TAPL ch 23)
   * Only kind is `*`
* STLC + polymorphic functions + type operators = System Fω (TAPL ch 30)
   * Other kinds

#### 2.3 Dependent types

Sending **terms** `x` to **types** `P(x)`:

```
Γ, x : A ⊢ T :: K
-----------------------
Γ ⊢ λ(x : A).T :: A -> K
```

The **kind** of a dependent type is a function kind, whose domain is merely a type.

Due to type dependency, the usual term-to-term lambda-abstraction from the STLC can actually create dependent functions:

```
Γ, x : A ⊢ T :: K
Γ, x : A ⊢ t : T
-----------------------
Γ ⊢ λ(x : A).t : Π(x : A).T
```

Agda notations for `Π(x : A).T`:

* `(x : A) -> T`
* `∀(x : A) -> T`
* `∀ x -> T` when the domain `A` can be inferred

When `T` does not depend on `x`, write `A -> T`.

##### Examples

`Vec :: * -> Nat -> *` sends terms `n : Nat` types `Vec A n :: *`.

Could even define `Vec` recursively:

```
Vec :: * -> Nat -> *
Vec A 0 = Unit
Vec A (suc n) = A × Vec A n
```

Note: type argument of `Vec` requires the existence of type operators.

##### System names:

STLC + type dependency is called:

* λΠ-calculus (because we now have Π-types)
* logical framework (LF):
   * `P :: A -> *` can be regarded as a **predicate** on `A`
   * `x` satisfies the predicate if there is a proof (inhabitant) of `P(x)`.

#### 2.4 The universe `Set`

DTT requires:

* type operators
* polymorphic functions
* dependent types

This is called the Calculus of Constructions, one flavour of DTT.

We can now abolish type/kind distinction.

* Rename `*` to `Set`, known as the **universe**.

### 3 Inference rules of DTT

Reminder:

* Goal = provide spec of DTT to help you use Agda
* Goal ≠ metatheoretical study of DTT

We consider MLTT (Martin-Löf type theory), one flavour of DTT.

#### 3.1 Judgement forms

STLC: contexts & types defined by a simple grammar.

DTT:

* Contexts mention types
* Types mention terms, including variables
* -> Scope matters
* -> Typing matters
* -> Need context & type *judgements*

Judgement forms:

* `Γ ctx` - `Γ` is a well-formed context,

* `Γ ⊢ T type` - `T` is a well-formed type in context `Γ`,

* `Γ ⊢ t : T` - `t` is a well-typed term of type `T` in context `Γ`.

Under the Curry-Howard correspondence, the latter two judgements may also be read as:

* `Γ ⊢ T type` - `T` is a well-formed proposition in context `Γ`,

* `Γ ⊢ t : T` - The proposition `T` is true in context `Γ`, as is evident from the well-formed proof `t`.

**Note:** Impossible to assert `T` without providing evidence.

##### Presupposition

* `Γ ⊢ T type` does **not** mean: "`Γ` is a well-formed context **and** `T` is a well-formed type in context `Γ`."

* `Γ ⊢ T type` does **not** mean: "**If** `Γ` is a well-formed context **then** `T` is a well-formed type in context `Γ`."

* `Γ ⊢ T type` means:
  
   * nothing (it is bogus, neither true nor false) if `Γ` is not a well-formed context,
  
   * "`T` is a well-formed type in context `Γ`" if `Γ` is a well-formed context. (Note that the condition that `Γ` be well-formed, is now outside of the quotes: the condition is not part of the meaning of the judgement, but must be satisfied for the judgement to be utterable.)

#### 3.2 Contexts

* Contexts are lists of typed variables
* (Nameless representation of variables) Contexts are lists of types.

Which variables can appear where?

* Read derivation bottom-up
* Start from empty context
* Add variable when moving under binder
   * So order of variables is meaningful!
* Binder should be type-checked in **its** context
   * So each variable's type can depend on all previously bound variables (those to its left).

```
-----
Ø ctx
```

```
Γ ctx (presupposed)
Γ ⊢ T type
------------
Γ, x : T ctx
```

Note: `Γ ctx` will often be omitted as it is implied by utterability of `Γ ⊢ T type`.

#### 3.3 The dependent function type

Output *type* may depend on the input *value*.

Example:

```agda
zeroes : (n : Nat) -> Vec Nat n
zeroes 0 = nil
zeroes (suc n) = cons 0 (zeroes n)
```

##### Formation rule

```
Γ ctx       (presupposed)
Γ ⊢ T1 type (presupposed)
Γ, x : T1 ⊢ T2 type
---------------------
Γ ⊢ Π(x : T1).T2 type
```

e.g. `Vec Nat n` depends on `n`.

Agda notations for `Π(x : A).T`:

* `(x : A) -> T`
* `∀(x : A) -> T`
* `∀ x -> T` when the domain `A` can be inferred

When `T` does not depend on `x`, write `A -> T`.

##### Relation to Lambda-cube

Domain `T1` and codomain `T2` may or may not be `Set` (or built from `Set`),
so the above function type encompasses all features of the Lambda-cube:

* Ordinary non-dependent term-level functions, e.g. `iszero : Nat -> Bool`,
* Polymorphic functions, e.g. `id : (X : Set) -> X -> X`,
* Type operators, e.g. `State : Set -> Set -> Set`,
* Dependent types, e.g. `Vec Bool : Nat -> Set`,
* Dependent term-level functions, e.g. `zeroes : (n : Nat) -> Vec Nat n`.

##### Abstraction rule

The abstraction rule looks quite familiar, of course with adapted type:

```
Γ ctx               (presupposed)
Γ ⊢ T1 type         (presupposed)
Γ, x : T1 ⊢ T2 type (presupposed)
Γ, x : T1 ⊢ t : T2
------------------------------
Γ ⊢ λ(x : T1).t : Π(x : T1).T2
```

Often, we omit the type label on the binder and simply write `λx.t`.

Some possible Agda notations are:

* `λ(x : T1) -> t`

* `λ x -> t` (when `T1` can be inferred)

##### Application rule

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

Agda has a feature called implicit arguments.

* Merely for usability
* Usually absent in theoretical presentations of DTT
* Can omit implicit arguments in abstractions & applications. Agda will infer them.

Syntax:

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

Only works if Agda is able to infer the given arguments.
E.g. if I declare addition of natural numbers with implicit arguments:

```agda
_+_ : {x y : Nat} -> Nat
```

and then write `_+_ : Nat`, leaving the operands implicit, then Agda will have a hard time inferring these.

Conversely, if I define `zeroes` with an implicit argument:

```agda
zeroes : {n : Nat} -> Vec Nat n
```

and then write `zeroes : Vec Nat 3` is required, then Agda will infer that I mean `zeroes {3}`.

Implicit arguments:

* are usable thanks to type dependency
* can be regarded separately from type dependency.

##### Relation to pair, tuple and record types

* Pair types: binary product, indexed by metatheoretic set/type `I = {0, 1}`
* Tuple types: `n`-ary product, indexed by metatheoretic set/type `I = {0, 1, ..., n}`
* Record types: `L`-ary product, indexed by a metatheoretic set/type of field names `I = L`

Constructing a pair/tuple/record:

* Assign to each metatheoretic index `i ∈ I` a term `tᵢ : Tᵢ`.

Projection from a pair/tuple/record:

* Choose a metatheoretic index `i ∈ I` and get `projᵢ t : Tᵢ`.

* Π-type `Π(i : I).T i`: `I`-ary product, indexed by **internal** type `I`.
  
   * Construct `λ(i : I).t i`: assign to each internal index `i : I` a term `t i : T i`
   * Project from `f : Π(i : I).T i`: choose internal index `i : I` and get `f i : T i`.

Some authors confusingly call the Π-type the dependent product type.
A better name would be the "internal-ary" product type because what changes w.r.t. the binary product type `T₁ × T₂` is not dependency of `Tᵢ` on `i`, but the arity.

##### Relation to non-dependent functions

* Calculus: Product of always the same number = a power.
* Type theory: Product of always the same type = non-dependent function type `I -> T`.
  (Called exponential object in category theory)

#### 3.4 The dependent pair type

Pairs whose second component's *type* depends on their first component's *value*.

Example:

```
List A = Σ(n : Nat).Vec A n
```

Three-element list:
`(3, cons a1 (cons a2 (cons a3 nil)) ) : Σ(n : Nat).Vec A n`
where indeed the second component has type `Vec A 3`.

##### Formation rule

```
Γ ctx       (presupposed)
Γ ⊢ T1 type (presupposed)
Γ, x : T1 ⊢ T2 type
---------------------
Γ ⊢ Σ(x : T1).T2 type
```

(Similar to Π-type)

Alternatively denoted `(x : T1) × T2`. When `T2` does not depend on `x`, we simply write `T1 × T2` instead.

Agda notation: `Σ[ x ∈ T1 ] T2` (with that exact usage of whitespace).

##### Introduction rule

First component will be substituted into the type of the second component:

```
Γ ctx               (presupposed)
Γ ⊢ T1 type         (presupposed)
Γ, x : T1 ⊢ T2 type (presupposed)
Γ ⊢ t1 : T1
Γ ⊢ t2 : [x ↦ t1]T2
----------------------------
Γ ⊢ (t1 , t2) : Σ(x : T1).T2
```

##### Projection rules

First projection:

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

* Sum type `T₁ + T₂`, also called coproduct, disjoint union or tagged union.
   * Agda notation: `T₁ ⊎ T₂`.
   * Binary coproduct indexed by metatheoretic set/type `I = {0, 1}`.
* Variant type: coproduct indexed by metatheoretic set/type of labels/tags `I = L`.

Construction:

* Choose a metatheoretic index `i ∈ I` and provide a term `t : Tᵢ`.

Elimination (create function `B -> C` where `B` is sum/variant):

* Case analysis on the tag.

* Create, for every metatheoretic tag `i ∈ I`, a function `fᵢ : Tᵢ -> C`.

* Σ-type `Σ(i : I).T i`: `I`-ary coproduct, indexed by **internal** type `I`.

Construction:

* Choose an internal index `i : I` and provide a term `t : T i`

Elimination `(Σ(i : I).T i) -> C`:

* Case analysis on the tag.
* Create, for every internal tag `i : I`, a function `f i : T i -> C`.
* Wrapped up in a single dependent function `f : Π(i : I).T i -> C`. (Currying)

Some authors confusingly call the Σ-type the dependent sum type.
A better name would be the "internal-ary" sum type because what changes w.r.t. the binary sum type `T₁ + T₂` is not dependency of `Tᵢ` on `i`, but the arity.

##### Relation to non-dependent pair types

* Calculus: Sum of always the same number = a product.
* Type theory: Coproduct of always the same type = non-dependent pair type `I × T`.
  (Called exponential object in category theory)

##### Dependent record types

Generalizations of non-dependent pair type `A × B`

* Σ-type generalizes non-dependent pair type (introduces dependency).
* Record type (`L`-ary).
* Dependent record type (both).

To specify a dependent record type with `n` fields in context `Γ`, we need to provide:

* a metatheoretic *list* of field names `l₁`, …, `lₙ` (not a set; the order is important),

* for each field `lᵢ`, a type `Tᵢ` in context `Γ, x₁ : T₁, ..., xᵢ₋₁ : Tᵢ₋₁`.

Then in order to inhabit that record type, we need to provide:

* for each field `lᵢ`, a term `tᵢ : [x₁ ↦ t₁, ..., xᵢ₋₁ ↦ tᵢ₋₁]Tᵢ`.

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

* Each field's type is allowed to refer to the values of the previous fields.

* When we create an instance, we first have to decide upon the carrier. This carrier will then be substituted into the types of all the following fields.

* Conversely, given a monoid instance `m`, the neutral element `m .mempty` will have type `m .Carrier`.

* Record types can be desugared to nested product types

* Dependent record types can be desugared to nested Σ-types.
  For instance, the `Monoid` type would desugar to `Σ(Carrier : Set).Σ(mempty : Carrier).{!etcetera!}`.

#### 3.5 The universe

Regardless of what variables are in scope, the universe exists:

```
Γ ctx
------------
Γ ⊢ Set type
```

There are introduction rules corresponding to all type formation rules, e.g.:

```
Γ ctx (presupposed)      Γ ctx (presupposed)
Γ ⊢ A type               Γ ⊢ A : Set
Γ ⊢ B type               Γ ⊢ B : Set
-------------------  ~>  -------------------
Γ ⊢ A × B type           Γ ⊢ A × B : Set
```

Then there is a rule asserting that every element of `Set` is, in fact, a type:

```
Γ ctx (presupposed)
Γ ⊢ T : Set
-----------
Γ ⊢ El T type
```

The operation `El` is generally omitted, i.e. we generally write `T` instead of `El T`. In Agda, `El` is always omitted.

#### 3.6 Data types

Agda supports data type declarations. E.g.:

```agda
data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A
```

* data type declarations are usually not considered part of DTT
* rather, they extend the system with additional inference rules:

Formation rule:

```
Γ ctx (presupposed)
Γ ⊢ A type
-----------
Γ ⊢ List A type
```

Constructors:

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

Elimination rule, a.k.a. dependent eliminator (see course notes).

* In Agda, we usually do not use dependent eliminators directly.
* Instead, Agda features an (in practice) much more powerful **pattern matching** system that is (or should be) non-straightforwardly desugarable to applications of dependent eliminators.

### 4 The Curry-Howard correspondence

For now, we refer to the overview sheet.

### 5 Equality

#### 5.1 Motivation

If `t : Vec A (2 + 3)` and we need `? : Vec A 5`, can we use `t`?

More generally, if `t : T1` and we need `? : T2`, which we know is equal, can we use `t`?

Questions:

* What does it mean for types to be equal?
* Types depend on terms, so:
  What does it mean for terms to be equal?

Nice properties to have:

1. Equality should be an **equivalence relation**, i.e. reflexive, symmetric and transitive,

2. Equality should be a **congruence**, i.e. respected by any operation our language provides,

3. If one term **reduces** to another, then they should be regarded as **equal**,

4. If two terms of the same pair/tuple/record type have **equal projections**, then they should be regarded as equal,

5. If two terms `f1` and `f2` of the same function type are **pointwise equal**, i.e. `f1 x` equals `f2 x` where `x` is a fresh variable in the functions' domain, then they should be regarded as equal,

6. If it is **assumed in the context** that two terms are equal, then they should be regarded as equal,

7. More generally, if it can be **proven from the context** that two terms are equal, then they should be regarded as equal.

##### Role of substitution

We can start by remarking that it is hard to have (6) without having (7).
Indeed, if context `Γ` proves `t1 ≡ t2`, i.e. `Γ ⊢ e : t1 ≡ t2` (where `e` is the proof)
then any judgement `Γ, x : t1 ≡ t2 ⊢ J` can be substituted to become `Γ ⊢ [x ↦ e]J`.
Now in the extended context, we have the *assumption*, so according to (6) we expect that `t1` and `t2` will be equal. But it would be problematic if substitution (which can be triggered by function application) were to break equality. So `t1` and `t2` should also be equal in context `Γ`.

##### Decidability of typing

Now property (7) seems a bit strong and in fact it is:
Equality relation generated by (roughly) the above requirements, which we will call **propositional equality**, is undecidable.

> If `t : T1` and we need `? : T2`, which we know is equal, can we use `t`?

Answer: No, not in general, not if you want type-checking to be algorithmic.

However, we do not want to give up on the earlier question:

> If `t : Vec A (2 + 3)` and we need `? : Vec A 5`, can we use `t`?

which does not rely on properties (6) and (7).

* Equality relation generated by properties 1-5 is decidable and even has computable normal forms.

* This relation is called **judgemental** or **definitional equality**.

* Added to the type system in the form of two additional judgement forms:
  
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

1. Equality should be an **equivalence relation**, i.e. reflexive, symmetric and transitive.
   
   ```
   Γ ⊢ T1 = T2 type
   ----------------       ...
   Γ ⊢ T2 = T1 type
   ```

2. Equality should be a **congruence**, i.e. respected by any operation our language provides.
   
   For every inference rule for types/terms, add equality preservation rule, e.g.
   
   ```
   Γ ⊢ a = a' : A
   Γ ⊢ as = as' : List A
   ---------------------
   Γ ⊢ cons a as = cons a' as' : List A
   ```
   
   In particular, counterpart for the `El` rule:
   
   ```
   Γ ⊢ T = T' : Set
   ----------------
   Γ ⊢ El T = El T' type
   ```

3. If one term **reduces** to another, then they should be regarded as **equal**.
   
   For every redex (reducible expression), there is a so-called **β-rule** expressing that the redex (called β-redex) is equal to its reduced form, e.g.
   
   ```
   Γ, x : T1 ⊢ t2 : T2
   Γ ⊢ t1 : T1
   -------------------
   Γ ⊢ (λx.t2) t1 = [x ↦ t1]t2 : [x ↦ t1]T2
   ```

4. If two terms of the same pair/tuple/record type have **equal projections**, then they should be regarded as equal.
   
   For the Σ-type and every user-defined record-type, there is a so-called **η-rule** expressing that the record is equal to its η-expansion, which is the pair/tuple/record of all its projections:
   
   ```
   Γ ⊢ p : Σ(x : T1).T2
   --------------------
   Γ ⊢ p = (fst p , snd p) : Σ(x : T1).T2
   ```
   
   In the standard library, the unit type is defined as a record type with zero fields. The η-law then expresses that any term of that type is equal to `tt`.

5. If two terms `f1` and `f2` of the same function type are **pointwise equal**, i.e. `f1 x` equals `f2 x` where `x` is a fresh variable in the functions' domain, then they should be regarded as equal.
   
   Similarly, there is an **η-rule** for the function type:
   
   ```
   Γ ⊢ f : Π(x : T1).T2
   --------------------
   Γ ⊢ f = λx.(f x) : Π(x : T1).T2
   ```

These 5 collections of rules generate the judgemental equality relation.

If we use a term `t : T1` in a hole `? : T2`, then Agda will check whether the conversion rule from §5.1 applies, i.e. whether `Γ ⊢ T1 = T2 type`.

* If yes, then the usage is accepted.
* If no, then Agda will issue a type error, typically mentioning inequality of corresponding subterms of `T1` and `T2`.

#### 5.3 Propositional equality

* Judgemental equality is a judgement,
* Propositional equality is a proposition, i.e. a type.

Can be declared as indexed data type in Agda:

```agda
data _≡_ {A : Set} (x : A) : (y : A) → Set where
  instance refl : x ≡ x
```

(If you wonder why `x` appears before the colon and `y` appears after it: Variables introduced before the colon are *parameters* of the type family. They are chosen once and remain the same throughout the data type declaration. An example of a parameter is the element type `A` in `Vec A n`. The variables after the colon are *indices* of the type family and can be determined by individual constructors. An example of an index is the length index `n` in `Vec A n`, which is `0` for `nil` and `suc n` for `cons`. For the propositional equality type, the `refl` constructor determines that one hand of the equation must be equal to the other, so at least one hand of the equation must be treated as an index.)

##### Inference rules

Data types extend DTT.

###### Formation rule

```
Γ ⊢ T type
Γ ⊢ t1 : T
Γ ⊢ t2 : T
----------
Γ ⊢ t1 ≡ t2 type
```

###### Introduction rule:

```
Γ ⊢ T type
Γ ⊢ t : T
----------
Γ ⊢ refl : t ≡ t
```

Judgemental equality implies propositional equality. Indeed, assume `Γ ⊢ t1 = t2 : T`:

```
---------------        (assumption)       (presupposed)
Γ ⊢ t1 = t1 : T        Γ ⊢ t1 = t2 : T    Γ ⊢ t1 : T
--------------------------------------    ------------------
Γ ⊢ (t1 ≡ t1) = (t1 ≡ t2) : T             Γ ⊢ refl : t1 ≡ t1
------------------------------------------------------------
Γ ⊢ refl : t1 ≡ t2
```

Alternative explanation:

* Due to the conversion rule, types do not distinguish between judgementally equal terms.
* Thus, types do not speak about syntactic terms, but about terms up to judgemental equality.
* `refl` proves that any term - considered up to judgemental equality - is propositionally equal to itself.
* `t1` and `t2` are the same up to judgemental equality, hence `refl` applies.

###### Elimination rule

Propositional equality should satisfy property (2):

> Equality should be a **congruence**, i.e. respected by any operation our language provides,

This is expressed by the dependent eliminator, called the J-rule (see course notes).

In Agda: use **pattern matching** instead.

##### Behaviour

Remarkably, with these few rules, propositional equality satisfies most of the desired properties:

1. **Reflexivity** is proven by `refl`. **Symmetry and transitivity** are provable by pattern matching.

2. **Congruence** is proven by pattern matching.

3. If one term **reduces** to another, then they are judgementally equal and hence, by the conversion rule, propositionally equal.

4. For **pair, tuple and record** types with a **finite** number of components,
   we can prove that records with equal fields are equal by pattern matching on each of the componentwise equality proofs.
   
   For **tuple and record types** with an **infinite** number of components (e.g. infinite streams), we need to **postulate** this property without proof.

5. For functions, we also need to postulate that pointwise equality implies equality, a property called **function extensionality**:
   
   ```agda
   postulate
     funext : {A : Set} {B : A -> Set}
              {f1 f2 : (x : A) -> B x}
              (p : (x : A) -> f1 x ≡ f2 x)
           -> f1 ≡ f2
   ```
   
   Postulating:
   
    * Postulate an element of a type -> Postulate that a proposition has a proof.
    * Logically: this asserts the proposition.
    * Seen as a program, the postulate has no definition and does not compute.
    * Programs involving postulates can get stuck.

6. If it is **assumed in the context** that two terms are equal, then they should be regarded as equal:
   
   ```
   Γ, w : t1 ≡ t2, Δ ⊢ w : t1 ≡ t2
   ```

7. If it can be **proven from the context** that two terms are equal, then they should be regarded as equal.
   
   For propositional equality, this property is tautological:
   
   ```
   Γ ⊢ p : t1 ≡ t2
   ```

### 6 Normalization

Just like STLC (TAPL ch 12), dependent type theory satisfies a normalization result:

> Closed well-typed terms reduce to values (of the same type) in a finite number of steps.

For programming:

* Programs terminate without errors.

For proving:

* Closed propositional equality proofs `⊢ e : t1 ≡ t2` reduce to `⊢ refl : t1 ≡ t2`, well-typedness of which implies that `t1` and `t2` are actually **judgementally** equal.
* Closed proofs of falsity `⊢ e : ⊥` reduce to a value `⊢ v : ⊥`. Since `⊥` has zero constructors, there are no values of type `⊥`, so there cannot be any closed proofs of falsity. So DTT is **consistent**: we cannot prove falsity without making any assumptions.

#### Termination-checking

List concatenation:

```agda
_++_ : {X : Set} -> List X -> List X -> List X
nil ++ ys = ys
(cons x xs) ++ ys = cons x (xs ++ ys)
```

Definition of `_++_` refers to itself.
This way we can write diverging definitions:

```agda
_+++_ : {X : Set} -> List X -> List X -> List X
xs +++ ys = xs +++ ys
```

Can prove falsity:

```agda
undefined : ⊥
undefined = undefined
```

To keep programs terminating and to keep Agda (reasonably) consistent, there is a **termination checker**.

Approves of a self-referencing program if there is one argument that is always smaller in recursive calls than in the parent call. For `_++_`: first argument. This guarantees termination:

```
              cons 1 (cons 2 (cons 3 (nil)))    ++ cons 4 nil
= cons 1 (            cons 2 (cons 3 (nil))     ++ cons 4 nil   )
= cons 1 (cons 2 (            cons 3 (nil)      ++ cons 4 nil   ))
= cons 1 (cons 2 (cons 3 (            nil       ++ cons 4 nil   )))
= cons 1 (cons 2 (cons 3 (cons 4 nil)))
```

### 7 Other concepts and further reading

(See course notes)

### Bibliography

(See course notes)
