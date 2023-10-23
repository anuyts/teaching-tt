## Dependent type theory (DTT)

*Andreas Nuyts*

### 0 Intro
* STLC: Simply typed
* Chapter 23-24: ∀, ∃
  * Term variables `x : Bool`
  * Type (operator) variables `X`
* Dependent type systems
  * Types are "first class citizens"
  * Type of types `Set` (as in Agda, `Type` would be more logical)
  * Type variables `X : Set` are special case of term variables

Goal of this chapter:
* background information to help you to **use** DTT

**Not** the goal of this chapter:
* prove metatheorems about DTT (termination, consistency, decidability of type-checking, ...)
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
