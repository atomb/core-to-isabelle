# What is Halicore?
Halicore is a set of interactive tools for proving properties about GHC Haskell programs. By ''GHC Haskell'', we mean Haskell plus the set of Haskell language extensions supported by the GHC compiler.

TODO: Example: Property that list-append is associative (maybe as a !QuickCheck rule or GHC rewrite).

The GHC compiler allows users to add custom rewrite rules. These rules are applied by the compiler itself, so it is important that they are correct! So another important goal for Halicore is to allow us to verify Haskell rewrite rules.

# What Halicore is not
Since many of the properties that Haskell programmers are interested in are undecidable, Halicore does not try to fully automate the proofs. Instead, we rely on Isabelle's powerful framework for checking proofs that the user constructs. Isabelle also has a wide variety of proof tactics for automatically proving subgoals for particular classes of properties, such as Boolean algebra, linear arithmetic, etc.

# Approach
One of our goals is to be able to reason about Haskell programs "as they occur", rather than requiring them to be rewritten to accommodate the theorem prover. This allows Halicore to be applied to a wider range of existing Haskell code, and avoids the temptation of proving properties over a "simplified" version of the Haskell program.

We also want to be able to reason as abstractly as possible about our code, and so the theorem prover we are using is Isabelle/HOLCF. HOLCF provides a robust library for reasoning about domain theory, including complete partial orders, domain equations, and general recursive functions. These features allow us to reason equationally about Haskell programs that contain lazy data structures, higher order functions, and partial termination.

Halicore uses GHC to translate a Haskell module into a small, explicitly-typed intermediate language called [External Core](http://www.haskell.org/ghc/docs/latest/core.pdf). The External Core program is then translated into a series of Isabelle/HOLCF definitions that correspond to a denotational semantics of the program.

The user then writes the program's desired correctness properties directly in HOLCF, making use of the automatically-generated program definitions.

Halicore is a tool to supplement to normal development; not a new way of writing code.  We emphasize a "pay as you go" and "only pay for what you use" model.  Here is an example of how I use Halicore:

 * I develop a library or application
 * I write QC properties, hUnit tests, develop and debug the code
 * My code is somewhat stable, but I'd really like more assurance
 * I translate my existing tests into theorems that I'd like to prove
 * I spend time proving the most important ones or easiest ones
 * Now I release claims about medium assurance based on my Haskell-Verifier proofs

## Why Isabelle/HOLCF?
We could have picked Coq/Agda/Epigram/Twelf/etc as our theorem prover, but we intentionally went with Isabelle.  We picked it for the ability to use HOLCF.  Using HOLCF we can reason about laziness and bottom in our Haskell programs.  The standard definition tools for Isabelle/HOL assume a language that is total, making it a poor match for Haskell.

## Why External Core?
 * External core is a much simpler language than Haskell, so it is easier to write a HOLCF translator for it.
 * It is the external format of the internal language of the GHC compiler, so we can support the full range of GHC language extensions.
 * New language extensions continue to be added to GHC, but the core language changes much less frequently.
 * We are leveraging the GHC front-end itself for our translation. If we were to directly translate Haskell source code we would have to duplicate much of the front-end functionality.
 * Disadvantage: Core haskell is lower-level language than Haskell, so translated definitions will be significantly larger than their original Haskell source code. However, care is taken to preserve the original source names, so our hope is that users will still be able to reason effectively about the translated code.

## How do we formalize GHC Haskell types?
Not all Haskell types can be represented directly as Isabelle types. Instead, we will model each Haskell type as a HOLCF ''deflation'' (i.e. a predicate defined by a particular kind of continuous function) that ranges over a universe of untyped Haskell values. Similarly, each type constructor will be represented as a continuous function (deflation transformer).

# Roadmap
## Basic shallow embedding
 * Change kinds to be abstract, so we can change their underlying implementations.
 * Make a synonym for "cont" in rules like V_lam_apply in case other models have other constraints on bodies.
 * Better syntax for type- and value-applications.
 * Define the deflation type for Maybe.map.
 * Prove that Maybe.map satisfies its declared deflation type.
 * Define case-like match syntax.
 * Introduce abstract type for matches.

## Prototype release
 * Shallow embedding of external core into HOLCF.
   * Coercions will be only trivially modeled. This should be fine since the original programs are already type-correct.
 * Example: self-application of identity function (simple lambda-calculus)
 * Example: Functor law for Maybe monad (datatype definitions, case analysis)
 * Example: Proof of associativity of list-append (induction over datatypes)
 * Example: Monad laws for ErrorT monad transformer (requires reasoning about abstract datatype invariants (the error value is never bottom)).
 * Simple translator from external core into shallow embedding.
 * Collection of example Haskell sources, their shallow embeddings, and associated correctness proofs.

## Initial release
 * Rewrite rule translator.
 * [Optional]: Automatically translate QuickCheck properties.

## Questions
 * How to easily figure out when a datatype constructor argument is strict (see isa/examples/StrictPair.hs)?
 * Should the deflation for strict datatypes exclude "unreachable" lazy values? Is it ever the case that "internal" functions generated by GHC have a non-strict datatype type?
