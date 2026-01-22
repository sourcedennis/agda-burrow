# Burrow: Weak Memory Proof Framework

Burrow is a proof framework for axiomatic weak memory mapping proofs implemented in [Agda](https://agda.readthedocs.io/).

## Installing

Burrow uses the [Agda standard library](https://github.com/agda/agda-stdlib) (v.1.7.3) and the binary relation library [Dodo](https://github.com/sourcedennis/agda-dodo), which must be separately installed.

## Code Navigation

> **Example.** For an example proof, see the [proof of an x86-to-Arm mapping](https://github.com/sourcedennis/armed-proofs/blob/main/src/Main.agda)

* `Burrow.Primitives` contains primitives from axiomatic weak memory (e.g., events, labels, locations, architectures)
* `Burrow.Execution` contains the general definition of an execution for a given architecture
* `Burrow.WellFormed` contains well-formedness axioms for an execution (e.g., each Read reads-from exactly one Write)
* `Burrow.Framework` contains Burrow's general proof framework, used when proving both mappings between models and when proving an optimization on a single model.
* `Burrow.Framework.Mapping` contains Burrow's opinionated framework to prove mappings between models (but not optimizations)
* `Burrow.Template.Arch` is a template useful when defining the weak memory model of an architecture
* `Burrow.Template.Mapping` is a template useful when proving a mapping between models.

## References

The Burrow proof framework was developed while writing the weak memory mapping proofs for the binary translators Lasagne and Risotto. While proving their respective x86-to-Arm mappings and optimizations we identified generalizations in their proof structure, which we captured as abstractions and primitives in Burrow.

* [Lasagne: A Static Binary Translator for Weak Memory Model Architectures](https://doi.org/10.1145/3519939.3523719) ([proofs](https://github.com/binary-translation/lasagne-proofs))
* [Risotto: A Dynamic Binary Translator for Weak Memory Model Architectures](https://doi.org/10.1145/3567955.3567962) ([proofs](https://github.com/binary-translation/risotto-proofs))
* [Arancini: A Hybrid Binary Translator for Weak Memory Model Architectures](https://doi.org/10.1145/3779212.3790127) ([proofs](https://github.com/sourcedennis/arancini-proofs))

## License

BSD-3