# Post-Quantum Cryptographic Analysis of IKEv2

This repository contains our measurement code for
our research on *Post-Quantum Cryptographic Analysis of IKEv2*. It implements the IKEv2
key schedule of RFC 7296 and RFC 9370, the single pass key schedule `SPKS`
introduced in our work, thirteen key derivation and key encapsulation
combiners ported to the IKEv2 pseudorandom function interface, and a complete
post-quantum IKEv2 handshake with real ML-KEM, FrodoKEM, X25519, AES-GCM and ML-DSA
operations. 

## Files and Contents

```
ikev2pq/
  params.py      IKEv2 cipher suites, transform sizes and derived key lengths
  prf.py         IKEv2 prf and prf+ (RFC 7296), counter-mode expansion,
                 compression call accounting
  combiners.py   RFC 9370 cascade, SPKS, and the published combiners
  costs.py       analytic time and space expressions for every schedule
  kex.py         X25519, ML-KEM and FrodoKEM behind one KEM interface, ML-DSA
  protocol.py    IKEv2 handshake with IKE_SA_INIT, IKE_INTERMEDIATE and IKE_AUTH
experiments/
  verify.py                self tests of the implementation and the cost model
  bench_combiners.py       
  bench_handshake.py       
  bench_kem_transform.py   
  make_figures.py          
  make_tables.py           
  run_all.py               runs all of the above in order
results/   measurement data in JSON (generated)
figures/   EPS figures 
```


## Third-party Components
* liboqs — <https://github.com/open-quantum-safe/liboqs>
* liboqs-python — <https://github.com/open-quantum-safe/liboqs-python>
* kyber-py — <https://github.com/GiacomoPope/kyber-py>
* pyca/cryptography — <https://github.com/pyca/cryptography>


## Requirements
Python 3.10 or later and the packages listed in `requirements.txt`:
```
pip install -r requirements.txt
```
`liboqs-python` provides ML-KEM, FrodoKEM and ML-DSA and builds or downloads
`liboqs` on first import; `cryptography` provides X25519 and AES-GCM; `kyber-py`
is the reference implementation of ML-KEM used for the comparison of the two
decapsulation variants; `matplotlib` and `numpy` are used only for the figures.

## Running the Results
```
python experiments/verify.py
python experiments/run_all.py
```
`verify.py` checks that the HMAC implementation agrees with the standard library
for all key and message lengths, that `prf+` matches RFC 7296, that the analytic
cost expressions of our research agree with the instrumented compression counts for
all cipher suites and all numbers of additional key exchanges, that the two peers
of a handshake derive the same key material, and that the constants quoted in our work reproduce. `run_all.py` writes the measurement data to `results/`, the figures to `figures/`
and the LaTeX table bodies to `tables/`. The repetition counts are controlled by
the environment variables `REPS`, `ROUNDS`, `RUNS` and `WARMUP`; the defaults are
the ones used for the numbers in our research. A full run takes about fifteen minutes
on a laptop.

Individual experiments can be run on their own, for example
```
python experiments/bench_combiners.py gcm256-sha256
python experiments/bench_handshake.py
python experiments/bench_kem_transform.py
```
The first argument of `bench_combiners.py` selects a cipher suite among
`gcm256-sha256`, `cbc256-sha256` and `gcm256-sha384`.

## The Two Key Schedules
The deployed schedule of RFC 9370 extracts a seed from the initial shared secret,
expands it into the seven IKEv2 keys, and then repeats an extraction and a full
expansion for each additional key exchange:
```
SKEYSEED(0) = prf(Ni | Nr, ss_0)
K(0)        = prf+(SKEYSEED(0), Ni | Nr | SPIi | SPIr)
SKEYSEED(m) = prf(SK_d(m-1), ss_m | Ni | Nr)
K(m)        = prf+(SKEYSEED(m), Ni | Nr | SPIi | SPIr)
```
`SPKS` keeps the messages of RFC 9242 and RFC 9370 unchanged, derives the block
that protects the intermediate exchanges once, and performs a single extraction
and a single expansion after the last round, keyed with the `IntAuth` chain that
RFC 9242 already computes:
```
sigma_0 = prf(Ni | Nr, ss_0 | SPIi | SPIr)
K(0)    = expand(sigma_0, "IKEv2 SP0")            (protection keys only)
theta   = IntAuth_i(n) | IntAuth_r(n)
sigma   = prf(theta, ss_0 | ss_1 | ... | ss_n)
K       = expand(sigma, "IKEv2 SP")
```
With HMAC-SHA-256, AES-GCM-16-256 and 32-byte nonces this costs 53 compression
calls for up to three additional key exchanges and at most 55 for the seven that
RFC 9370 allows, against `35n + 34` for the cascade.

