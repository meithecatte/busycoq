# BusyCoq

Verified implementations of [Busy Beaver deciders][decider]. The computation
is split into two parts:

 - First, an untrusted decider, written in Rust, tries to decide whether
   each machine halts. When it succeeds, it generates a *certificate*.
 - Then, a *verifier*, proven correct in Coq and extracted to OCaml,
   checks each certificate and makes sure that it is correct.
   A Coq theorem guarantees that if the verifier accepts a certificate, then
   the corresponding machine doesn't halt.

[decider]: https://bbchallenge.org/method#deciders

## Implemented deciders

 - Cyclers

## Running the deciders

Place the [seed database][seed] at `seed.dat` in the root of the repository.
Make sure you have Rust, Coq and OCaml installed. Then,

```bash
cd decide
cargo run --release
cd ../verify
make
./verify
```

A binary file listing the database indices of all successfully decided machines
will be generated at `decided.dat`.

[seed]: https://bbchallenge.org/method#download
