# Machine-checked Security Proofs for IKEv2

This directory contains the EasyCrypt development of our research. It
models the components of IKEv2 that the analysis uses, states the security
notions of our research as games, and verifies the reductions between them. No proof obligation is
discharged with `admit`.

## Running the Proofs
The proof requires EasyCrypt r2025.03 ([codebase](https://github.com/EasyCrypt/easycrypt)) or later with an SMT backend configured (Alt-Ergo and Z3 are the ones used here). If `easycrypt` is not on the PATH the script falls back to `~/.opam/easycrypt/bin/easycrypt`. To facilitate the assessing process, you can simply use our script to run all:
```
./check.sh
```
The script locates EasyCrypt through `opam` (switch `easycrypt` by default, or
`EASYCRYPT_SWITCH`), refuses to run if any file contains `admit`, prints the
assumptions that the development carries, removes cached results so that every
file is checked from scratch, compiles them in dependency order, and reports the
outcome. It was developed against EasyCrypt `r2025.03` with Alt-Ergo 2.6.0 and
Z3 4.15.4, where a full run takes about twenty seconds.

## Files and Contents

| File | Content |
| --- | --- |
| `IKEv2Core.ec` | Blocks, the negotiated pseudorandom function, the pseudorandom function game, the segment keyed swap game of Definition 2, the split key game of Definition 1 in its oracle and single challenge forms, and the equivalence between them. |
| `Expansion.ec` | The chained expansion of RFC 7296 and the counter mode expansion of the single pass schedule, each proved pseudorandom under a uniform key, with no collision term. |
| `Segment.ec` | Segment profiles, injectivity of insertion at a fixed profile, the segmentation results, and the two query attack that shows that the key length of a profile cannot be left free, whose advantage is computed exactly. |
| `Compression.ec` | The Davies-Meyer compression function over a 256-bit chaining value, the related key games for a family of permutations and for a family of functions, the reduction of related key pseudorandomness of the compression function to related key security of the block cipher, and the passage from the permutation family to the function family, which is proved through an up to bad argument and a failure event bound rather than assumed. The file then builds the Merkle-Damgard cascade and HMAC, and reduces the inner step of segment keyed swap security of HMAC to the related key game. |
| `Cascade.ec` | The key schedule of RFC 7296 and RFC 9370, the loop splitting result that isolates the round absorbing a secret, the pseudorandomness of the cascade tail by induction on the number of rounds, and split key security of the schedule at the initial and at the later key exchanges. |
| `Ppk.ec` | The preshared key mixing of RFC 8784 and its split key security at both indices. |
| `Spks.ec` | The single pass key schedule, its split key security at a later key exchange with a bound that does not grow with the number of rounds, and its split key security at the initial key exchange through a two profile segment game. |
| `Optimality.ec` | The cost model of a two layer schedule, the lower bounds on invocations and on compression calls, and the fact that the single pass schedule attains both. |
| `Qrom.ec` | The quantum random oracle model in the monolithic form of EasyPQC, where the whole function is sampled at initialization, together with the result that lazy sampling and monolithic sampling are indistinguishable. |
| `Kem.ec` | The key encapsulation mechanism whose key is derived by the oracle, the proof that the real key and a programmed key are identically distributed, the transfer of the game from lazy to monolithic sampling, and the chosen plaintext bound. |
| `Acce.ec` | Parties, sessions and the six oracles including the harvest oracle, the message flow of `IKE_SA_INIT`, the intermediate exchanges and `IKE_AUTH` as a state machine, partnering and freshness, the birthday bound on nonce collisions proved with a failure event argument, the guessing step for the tested session proved with plug and pray, the invariance of the message flow under a change of schedule, and the composition of the game sequence into the channel bound. |
| `Instantiate.ec` | The negotiated suite of our research, the derived block counts, the segment profiles of both schedules, and the concrete compression count. |

## Modeling Choices

The negotiated pseudorandom function is an abstract operator `F` on a key of
blocks and a message that carries an integer label together with a block list.
The label separates the derivation steps, so the inputs of one expansion are
distinct by construction and the pseudorandomness of `Fplus` and of the counter
mode expansion holds with no birthday term.

Chaining keys are read with `skd`, which returns exactly one block, so the key
length of a segment profile is fixed. Insertion is `ins x z y = x ++ (z ++ y)`,
and `Segment.ec` proves that it is injective when the three lengths are fixed.

The ideal related key permutation game of `Compression.ec` keeps a fresh answer
outside the images already used for the same related key while fewer than `q`
answers have been given, which is what a `q`-query adversary can observe, and
this is what makes the family of permutations well defined without a bound on
the size of the block space.

The quantum random oracle follows the discipline of EasyPQC as the oracle is
sampled once as a whole function through `dfun`, and no proof reprograms it
lazily, so the relational steps stay inside the fragment that lifts to quantum
adversaries. `Kem.ec` uses the transfer result of `Qrom.ec` to move the actual
chosen plaintext game from the lazy oracle to the monolithic one. Classical
primitives use the ordinary EasyCrypt games.

## Assumptions

The development carries two kinds of assumption, and `check.sh` prints both.

Distribution and length parameters are declared with `as` clauses, for instance
`gt0_olen` for the length of a key block.

Security hypotheses are section axioms quantified over all adversaries, so they
are statements about the primitives and not about the games of our research. They
are `prf_bound` for the negotiated pseudorandom function, `seg_bound` and
`seg2_bound` for segment keyed swap security, `o2h_bound` and `find_bound` for
the two quantum steps of the chosen plaintext proof, which the pqRHL extension
of EasyPQC would be needed to discharge, `A_ll` and `A_qbound` for losslessness
and for the query budget of an adversary, `qq_small` for the smallness of the
query budget against the block space, and `padk_coll` together with
`keys_distinct` for the two colliding keys that the attack of `Segment.ec` uses.

The three steps of the channel proof that replace the shared secret, the key
block and the channel keys are given as hypotheses of the composition lemma in
`Acce.ec`, so the shape of the bound of our research is derived and the two
counting steps of that bound, the nonce collision term and the session guessing
factor, are proved.
