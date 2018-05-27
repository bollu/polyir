PolyIR
======

This is a reference implementation for the semantics of SCoPs. This implementation
abstracts over the concrete implementation of polyhedral libraries that are used.
Implementations must adhere to the spec laid out by the `POLYHEDRA`. Here, every
operation is allowed to fail (all operations return `option`). But if an
operation succeeds, we expect the result to be correct.


We pick such a model for the library to account for libraries such as VPL, which
use a theorem-proved oracle to verify correctness certificates. The APIs of
such a library will always return an optional value (in the case of VPL, an `imp`
value), which may or may not be correct. By structuring our expected API in this
"fail-allowed" way, we can interface with libraries that use oracles.

On the other hand, if someone _does_ implement a fully verified library for
polyhedral manipulations, then to plug with our API, they can simply wrap
their results with `Some(...)` and call it a day, because all of their results
will be correct.

The goals of this project are as follows:

0. Provide a reference notion of the formal semantics of `SCoPs` as used by
   Polly, PLUTO, etc. To the best of our knowledge, no such formalization exists
   within a theorem prover.

1.  Prove the main theorem one requires to transform SCoPs: if the new schedule
    does not violate the dependence polyhedra, then the new schedule preserves semantics.
    Obviously, to formalise this, we need a notion of "schedule", "dependence polyhedra", etc.

2. Explore if it is possible to have a way to embed an untrusted optimiser (say, ISL) into this
   framework, once we have the "main theorem" at hand.

3. Prove equivalence between a simple language with loopy strucures (called `Poly`) to the `SCoP` model
   of computation. We will show preservation of environment and memory between `Poly` and `SCoP`.
   This way, any compiler formalisation project of interest can show equivalence to `Poly` 
   and get polyhedral compilation "for free". Currently, there are only bigstep semantics to `Poly`,
   but we shall also provide smallstep, for `CompCert` style forward semantics preservation proofs.



Status:
- [x] Implement the `Poly` and `ScoP` models and an interpreter for them
- [ ] Formalise Schedules.
- [ ] Formalise dependences.
- [ ] Formalise the notion of a Schedule preserving dependences.
- [ ] Prove that if a Schedule preserves Dependences, the Schedule preserves semantics
- [ ] Show equivalence between `ScoP` and `Poly`
- [ ] Implement smallstep semantics for `Poly`
- [ ] Embed into `CompCert` / `VELLVM` / ...

