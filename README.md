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
 - Translated Cyclers
 - Backwards Reasoning
 - Bouncers

## Individual machines

Apart from deciders, the repository includes manual proofs for some machines
considered hard to decide automatically. At the moment, these include:

 - [Skelet #34](https://www.sligocki.com/2023/02/02/skelet-34.html)
 - [Skelet #35](https://www.sligocki.com/2023/02/05/shift-overflow.html)
 - [Skelet #1](https://www.sligocki.com/2023/03/13/skelet-1-infinite.html)
    (due to the nature of the proof, the final computation is done by an
    extracted OCaml program)

## Running the deciders

Place the [seed database][seed] at `seed.dat` in the root of the repository.
Make sure you have Rust, Coq and OCaml installed. Then,

```bash
cd decide
cargo build --release
time target/release/beaver decide ../seed.dat ../certs.dat
cd ../verify
make
./verify
```

A binary file listing the database indices of all successfully decided machines
will be generated at `decided.dat`.

[seed]: https://bbchallenge.org/method#download

## Results

```
Cyclers:
  11229238 Decided
         0 OutOfSpace
   3092791 OutOfTime
         0 Halted
  74342035 NotApplicable
Translated Cyclers:
  73860624 Decided
         0 OutOfSpace
    481411 OutOfTime
         0 Halted
   3092791 NotApplicable
Backwards Reasoning:
   2035576 Decided
    979028 OutOfSpace
    559598 OutOfTime
Bouncers:
   1406024 Decided
     23438 OutOfSpace
    109164 OutOfTime
         0 Halted

real	12m12.126s
user	143m12.813s
sys	0m8.300s
```

With high limits for the Translated Cyclers decider:

```
chikara:~/dev/busycoq/decide$ \time target/release/decide
Cyclers:
  11229238 Decided
         0 OutOfSpace
   3092791 OutOfTime
         0 Halted
  74342035 NotApplicable
Translated Cyclers:
  73861173 Decided
    138452 OutOfSpace
    342410 OutOfTime
         0 Halted
   3092791 NotApplicable
10784.09user 136.66system 15:12.51elapsed 1196%CPU (0avgtext+0avgdata 10180maxresident)k
0inputs+2794536outputs (0major+2590minor)pagefaults 0swaps
chikara:~/dev/busycoq/verify$ \time ./verify
79.89user 0.41system 1:20.32elapsed 99%CPU (0avgtext+0avgdata 124288maxresident)k
0inputs+664776outputs (0major+30600minor)pagefaults 0swaps
```
