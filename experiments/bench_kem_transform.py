import json
import os
import statistics
import sys
import time
from hashlib import sha3_512

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from kyber_py.ml_kem import ML_KEM_512, ML_KEM_768, ML_KEM_1024

try:
    import oqs

    HAVE_OQS = True
except Exception:
    HAVE_OQS = False

RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")

SCHEMES = {
    "ML-KEM-512": ML_KEM_512,
    "ML-KEM-768": ML_KEM_768,
    "ML-KEM-1024": ML_KEM_1024,
}


def decaps_cca(scheme, dk, c):
    return scheme.decaps(dk, c)


def decaps_cpa(scheme, dk, c):
    dk_pke = dk[0 : 384 * scheme.k]
    h = dk[768 * scheme.k + 32 : 768 * scheme.k + 64]
    m = scheme._k_pke_decrypt(dk_pke, c)
    return sha3_512(m + h).digest()[:32]


def bench(fn, reps):
    fn()
    samples = []
    for _ in range(9):
        t0 = time.perf_counter_ns()
        for _ in range(reps):
            fn()
        samples.append((time.perf_counter_ns() - t0) / reps / 1000.0)
    return min(samples), statistics.median(samples)


def main():
    os.makedirs(RESULTS, exist_ok=True)
    reps = int(os.environ.get("REPS", "40"))
    rows = []
    for name, scheme in SCHEMES.items():
        ek, dk = scheme.keygen()
        key, c = scheme.encaps(ek)
        assert decaps_cca(scheme, dk, c) == key
        assert decaps_cpa(scheme, dk, c) == key
        cca_min, cca_med = bench(lambda: decaps_cca(scheme, dk, c), reps)
        cpa_min, cpa_med = bench(lambda: decaps_cpa(scheme, dk, c), reps)
        row = {
            "scheme": name,
            "decaps_cca_us": cca_min,
            "decaps_cpa_us": cpa_min,
            "speedup": cca_min / cpa_min,
        }
        if HAVE_OQS:
            with oqs.KeyEncapsulation(name) as k:
                pk = k.generate_keypair()
                ct, _ = k.encap_secret(pk)
                o_min, _ = bench(lambda: k.decap_secret(ct), max(reps, 2000))
                e_min, _ = bench(lambda: k.encap_secret(pk), max(reps, 2000))
            row["liboqs_decaps_us"] = o_min
            row["liboqs_encaps_us"] = e_min
        rows.append(row)
        print(
            f"{name:12s} cca={cca_min:9.1f}us cpa={cpa_min:9.1f}us "
            f"speedup={row['speedup']:.2f}x"
            + (f" liboqs_decaps={row.get('liboqs_decaps_us', 0):.1f}us" if HAVE_OQS else "")
        )
    out = os.path.join(RESULTS, "kem_transform.json")
    with open(out, "w") as f:
        json.dump(rows, f, indent=1)
    print("wrote", out)


if __name__ == "__main__":
    main()
