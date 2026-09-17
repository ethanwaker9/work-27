import json
import os
import statistics
import sys
import time
import tracemalloc

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ikev2pq.combiners import Context, DEFERRED_COMBINERS, rfc9370, spks_stage0, stage0_protection
from ikev2pq.costs import COST_TABLE, spks_stage0_cost, stage0_full, stage0_partial
from ikev2pq.params import KEM_SIZES, SUITES, Suite
from ikev2pq.prf import CostCounter, Prf

RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")

LADDER = [
    "x25519",
    "ml-kem-768",
    "frodokem-640-aes",
    "ml-kem-1024",
    "ml-kem-512",
    "frodokem-976-aes",
    "ecp256",
    "ml-kem-768",
]

METHOD_ORDER = [
    "RFC 9370",
    "Concat",
    "Concat-CT",
    "CatKDF",
    "ChainExt",
    "GHP-XorROM",
    "GHP-XorPRF",
    "GHP-XorPRF-opt",
    "XtM",
    "dualPRF",
    "Nested-N",
    "KeyCombine",
    "X-Wing",
    "SPKS",
]


def make_inputs(n_add, suite: Suite):
    kems = LADDER[: n_add + 1]
    ss_lens = [KEM_SIZES[k]["ss"] for k in kems]
    ct_lens = [KEM_SIZES[k]["ct"] for k in kems]
    pk_lens = [KEM_SIZES[k]["pk"] for k in kems]
    secrets = [os.urandom(x) for x in ss_lens]
    ctx = Context(
        ni=os.urandom(suite.nonce_len),
        nr=os.urandom(suite.nonce_len),
        spii=os.urandom(suite.spi_len),
        spir=os.urandom(suite.spi_len),
        cts=[os.urandom(x) for x in ct_lens],
        pks=[os.urandom(x) for x in pk_lens],
        theta=os.urandom(2 * suite.out),
    )
    return kems, secrets, ctx, ss_lens, ct_lens, pk_lens


def run_once(method, secrets, ctx, suite, prf):
    if method == "RFC 9370":
        km, _ = rfc9370(secrets, ctx, suite, prf)
        return km
    if method == "SPKS":
        spks_stage0(secrets[0], ctx, suite, prf)
    else:
        stage0_protection(secrets[0], ctx, suite, prf)
    return DEFERRED_COMBINERS[method](secrets, ctx, suite, prf)


def timed_all(methods, secrets, ctx, suite, reps, rounds):
    prf = Prf(suite.prf_hash, None)
    acc = {m: [] for m in methods}
    for m in methods:
        for _ in range(reps // 2 + 1):
            run_once(m, secrets, ctx, suite, prf)
    for _ in range(rounds):
        for m in methods:
            t0 = time.perf_counter_ns()
            for _ in range(reps):
                run_once(m, secrets, ctx, suite, prf)
            acc[m].append((time.perf_counter_ns() - t0) / reps / 1000.0)
    return {m: (min(v), statistics.median(v)) for m, v in acc.items()}


def peak_memory(method, secrets, ctx, suite):
    prf = Prf(suite.prf_hash, None)
    run_once(method, secrets, ctx, suite, prf)
    tracemalloc.start()
    base = tracemalloc.get_traced_memory()[0]
    run_once(method, secrets, ctx, suite, prf)
    peak = tracemalloc.get_traced_memory()[1]
    tracemalloc.stop()
    return peak - base


def main():
    os.makedirs(RESULTS, exist_ok=True)
    suite_key = sys.argv[1] if len(sys.argv) > 1 else "gcm256-sha256"
    suite = SUITES[suite_key]
    reps = int(os.environ.get("REPS", "300"))
    rows = []
    rounds = int(os.environ.get("ROUNDS", "25"))
    for n_add in range(1, 8):
        kems, secrets, ctx, ss_lens, ct_lens, pk_lens = make_inputs(n_add, suite)
        times = timed_all(METHOD_ORDER, secrets, ctx, suite, reps, rounds)
        for method in METHOD_ORDER:
            counter = CostCounter()
            prf = Prf(suite.prf_hash, counter)
            run_once(method, secrets, ctx, suite, prf)
            snap = counter.snapshot()
            model = COST_TABLE[method](suite, ss_lens, ct_lens, pk_lens)
            if method == "RFC 9370":
                base = stage0_full(suite, ss_lens[0])
            elif method == "SPKS":
                base = spks_stage0_cost(suite, ss_lens[0])
            else:
                base = stage0_partial(suite, ss_lens[0])
            tmin, tmed = times[method]
            mem = peak_memory(method, secrets, ctx, suite)
            rows.append(
                {
                    "suite": suite_key,
                    "n_add": n_add,
                    "method": method,
                    "kems": kems,
                    "measured_compressions": snap["compressions"],
                    "model_compressions": model["comp"],
                    "core_compressions": model["comp"] - base,
                    "stage0_compressions": base,
                    "prf_calls": snap["prf_calls"],
                    "hashed_bytes": snap["hashed_bytes"],
                    "depth": model["depth"],
                    "keymat_bytes": model["keymat"],
                    "peak_model_bytes": model["peak"],
                    "peak_measured_bytes": mem,
                    "time_min_us": tmin,
                    "time_med_us": tmed,
                }
            )
            print(
                f"n={n_add} {method:16s} comp={snap['compressions']:6d} "
                f"model={model['comp']:6d} t={tmin:9.3f}us mem={mem:7d}"
            )
    out = os.path.join(RESULTS, f"combiners_{suite_key}.json")
    with open(out, "w") as f:
        json.dump(rows, f, indent=1)
    print("wrote", out)


if __name__ == "__main__":
    main()
