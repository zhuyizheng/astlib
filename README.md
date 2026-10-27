# Astlib: Axiomatic Set Theory Library

Documentation at https://zhuyizheng.github.io/astlib/docs/

A lean4 library of tools in modern axiomatic set theory. The first few targets are:

1. Gödel's constructible universe with Jensen's fine-structural hierarchy
2. The forcing toolbox (need to translate from the lean3-repo [flypitch](https://github.com/flypitch/flypitch)  and enhance)
3. The large cardinal hierarchy
4. Determinacy principles and descriptive set theory

We need to build infrastructure that enables us to work with models of fragments of ZFC. Already formalized:

1. **Syntax and definability.** The Lévy hierarchy of formulas (`Δ₀`, `Σₖ`, `Πₖ`, definable) for
   classes, multiclasses and class functions, with instances so that the complexity of classes
   written in lambda notation is found by `infer_instance`.
2. **Rudimentary and primitive recursive functions.** Rudimentary terms and the rudimentary basis
   in fine structure, closure of models of `KP` under rudimentary functions, primitive recursive
   terms, recursion on ordinals, and the `Σ₁` definability of primitive recursive functions.
3. **Axiom systems and their models.** `KP₀`, `KP`, `KPInf`, `ZF`, and `ZF` with choice (`ZFC`),
   countable choice (`ZFCC`) and dependent choice (`ZFDC`). Models of `ZF` satisfy collection,
   comprehension and replacement for definable relations, are closed under power sets and satisfy
   `∈`-induction. Under choice on a set `a`, definable relations are uniformized on `a`; this
   holds for all sets in `ZFC`, and for `ω` and all countable sets in `ZFCC`.
4. **Basic set operations.** Pairs, unions, products, relations, functions (injections,
   surjections, bijections, composition, inverses, restriction, images), power sets and the sets
   `funSet`, `injSet`, `surjSet`, `bijSet` of functions, and transitive closure.
5. **Orders and recursion.** Strict linear orders, strict well-founded relations and strict
   well-orders, well-founded induction and recursion, and the Mostowski collapse.
6. **Ordinals.** The order on ordinals, `ω` and induction and recursion on `ω`, ordinal addition
   and multiplication, order types of sets of ordinals, and Gödel's pairing function as a
   primitive recursive order isomorphism from Gödel's order on pairs of ordinals onto the
   ordinals, together with its iteration coding finite sequences of ordinals.
7. **Cardinals.** Cardinals, cardinality, successor cardinals and the alephs; finite sets and
   finite sequences; countable sets, including:
   - countable unions of countable sets are countable under countable choice;
   - the finite sequences and finite subsets of a countable set are countable (in `ZF`).
8. **Cofinality.** Cofinal maps, cofinality and regular ordinals:
   - `ω` is regular (in `KP`);
   - successor cardinals of infinite ordinals are regular (in `ZFC`);
   - `ℵ₁` is regular under countable choice alone.
