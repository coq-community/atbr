# ATBR

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]
[![DOI][doi-shield]][doi-link]

[travis-shield]: https://travis-ci.com/coq-community/atbr.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/atbr/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby

[doi-shield]: https://zenodo.org/badge/DOI/10.2168/LMCS-8(1:16)2012.svg
[doi-link]: https://doi.org/10.2168/LMCS-8(1:16)2012

This library provides algebraic tools for working with binary relations.
The main tactic provided is a reflexive tactic for solving (in)equations
in an arbitrary Kleene algebra. The decision procedure goes through
standard finite automata constructions.

Note that the initial authors consider this library to be superseded
by the Relation Algebra library, which is based on derivatives
rather than automata: https://github.com/damien-pous/relation-algebra


More details about the project can be found in the paper
[Deciding Kleene Algebras in Coq](https://arxiv.org/abs/1105.4537).

## Meta

- Author(s):
  - Thomas Braibant (initial)
  - Damien Pous (initial)
- Coq-community maintainer(s):
  - Tej Chajed ([**@tchajed**](https://github.com/tchajed))
- License: [GNU Lesser General Public License v3.0 or later](LICENSE)
- Compatible Coq versions: 8.9 (use the corresponding branch or release for other Coq versions)
- Compatible OCaml versions: all versions supported by Coq
- Additional Coq dependencies: none

## Building and installation instructions

The easiest way to install the latest released version of ATBR
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-atbr
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/atbr
cd atbr
make   # or make -j <number-of-cores-on-your-machine>
make install
```

After installation, the included modules are available under
the `ATBR` namespace.


## Documentation

Here is a succinct description of each file.
The user can also refer to files `Examples.v` and `ChurchRosser.v`.

### Library files

| Filename      | Description
| --------      | -----------
| ATBR          | Export all relevant modules, except those related to matrices
| ATBR_Matrices | Export all relevant modules, including those related to matrices


#### Algebraic hierarchy

| Filename            | Description
| --------            | -----------
| Classes             | Definitions of algebraic classes of the development
| Graph               | Lemmas and hints about the base class (carrier with equality)
| Monoid              | Monoids, free monoids, finite iterations over a monoid, various tactics
| SemiLattice         | Semilattices, tactics: normalise, reflexivity, rewrite
| SemiRing            | Idempotent semirings, tactics: normalise, reflexivity, rewrite
| KleeneAlgebra       | Kleene algebras, basic properties
| Converse            | Structures with converse (semirings and Kleene Algebras)
| Functors            | Functors between the various algebraic structures
| StrictKleeneAlgebra | Class of Strict Kleene algebras (without 0), and extension of the decision procedure

#### Models

| Filename           | Description
| --------           | -----------
| Model_Relations    | Kleene Algebra of (heterogeneous) binary relations
| Model_StdRelations | Kleene Algebra of standard (homogeneous) binary relations
| Model_Languages    | Kleene Algebra of languages
| Model_RegExp       | Kleene Algebra of regular expressions (syntactic free model), typed reification
| Model_MinMax       | (min,+) Kleene Algebra (matrices on this algebra give weighted graphs)

#### Matrices

| Filename        | Description
| --------        | -----------
| MxGraph         | Matrices without operations; blocks definitions
| MxSemiLattice   | Semilattices of matrices
| MxSemiRing      | Semiring of matrices
| MxKleeneAlgebra | Kleene algebra of matrices (definition of the star operation)
| MxFunctors      | Extension of functors to matrices


#### Decision procedure for KA

| Filename            | Description
| --------            | -----------
| DKA_Definitions     | Base definitions for the decision procedure for KA (automata types, notations, ...)
| DKA_StateSetSets    | Properties about sets of sets
| DKA_CheckLabels     | Algorithm to check whether two regex have the same set of labels
| DKA_Construction    | Construction algorithm, and proof of correctness
| DKA_Epsilon         | Removal of epsilon transitions, proof of correctness
| DKA_Determinisation | Determinisation algorithm, proof of correctness
| DKA_Merge           | Union of DFAs, proof of correctness
| DKA_DFA_Language    | Language recognised by a DFA, equivalence with the evaluation of the DFA
| DKA_DFA_Equiv       | Equivalence check for DFAs, proof of correctness
| DecideKleeneAlgebra | Kozen's initiality proof, kleene_reflexivity tactic

#### Other tools

| Filename       | Description
| --------       | -----------
| StrictStarForm | Conversion of regular expressions into strict star form, kleene_ssf tactic
| Equivalence	   | Tactic for solving equivalences by transitivity

#### Examples

| Filename            | Description
| --------            | -----------
| Examples            | Small tutorial file, that goes through our set of tactics
| ChurchRosser        | Simple usages of kleene_reflexivity to prove commutation properties
| ChurchRosser_Points | Comparison between a standard CR proof and algebraic ones

#### Misc.

| Filename     | Description
| --------     | -----------
| Common       | Shared simple tactics and definitions
| BoolView     | View mechanism for Boolean computations
| Numbers      | NUM interface, to abstract over the representation of numbers, sets, and maps
| Utils_WF     | Utilities about well-founded relations; partial fixpoint operators (powerfix)
| DisjointSets | Efficient implementation of a disjoint sets data structure
| Force        | Functional memoisation (in case one needs efficient matrix computations)
| Reification  | Reified syntax for the various algebraic structures

#### Finite sets and maps

| Filename         | Description
| --------         | -----------
| MyFSets          | Efficient ordered datatypes constructions (for FSets functors)
| MyFSetProperties | Handler for FSet properties
| MyFMapProperties | Handler for FMap properties

#### OCaml modules

| Filename         | Description
| --------         | -----------
| `reification.ml` | reification for the reflexive tactics

### Tactics

#### Reflexive tactics

| Tactic                 | Description
| ------                 | -----------
| `semiring_reflexivity` | solve an (in)equation on the idempotent semiring (*,+,1,0)
| `semiring_normalize`   | simplify an (in)equation on the idempotent semiring (*,+,1,0)
| `semiring_clean`       | simplify 0 and 1
| `semiring_cleanassoc`  | simplify 0 and 1, normalize the parentheses
| `kleene_reflexivity`   | solve an (in)equation in Kleene Algebras
| `ckleene_reflexivity`  | solve an (in)equation in Kleene Algebras with converse
| `skleene_reflexivity`  | solve an (in)equation in Strict Kleene Algebras (without 0)
| `kleene_clean_zero`    | remove zeros in a KA expression
| `kleene_ssf`           | put KA expressions into strict star form

#### Rewriting tactics

| Tactic             | Description
| ------             | -----------
| `ac_rewrite H`     | rewrite a closed equality modulo (AC) of (+)
| `monoid_rewrite H` | rewrite a closed equality modulo (A) of (*)

#### Other tactics

| Tactic          | Description
| ------          | -----------
| `converse_down` | push converses down to terms leaves
| `switch`        | add converses to the goal and push them down to terms leaves

## Acknowledgements

The initial authors would like to thank Guilhem Moulin and Sebastien Briais,
who participated to a preliminary version of this project. They are also grateful
to Assia Mahboubi, Matthieu Sozeau, Bruno Barras, and Hugo Herbelin for highly
stimulating discussions, as well as numerous hints for solving various problems.

