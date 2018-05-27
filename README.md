PolyIR
======

This is a reference implementation for the semantics of SCoPs. This implementation
abstracts over the concrete implementation of polyhedral libraries that are used.
Implementations must adhere to the spec laid out by the `POLYHEDRA`. Here, every
operation is allowed to fail (all operations return `option`). But if an
operation succeeds, we expect the result to be correct.

The goals are as follows:

1.  Prove the main theorem one requires to transform SCoPs: if the new schedule
    does not violate the dependence polyhedra, then the new schedule preserves semantics.
    Obviously, to formalise this, we need a notion of "schedule", "dependence polyhedra", etc.

2. Prove equivalence between a simple language with loopy strucures (called `Poly`) to the `SCoP` model
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

