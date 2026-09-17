import json
import os
import statistics
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ikev2pq.params import SUITES
from ikev2pq.protocol import Ikev2Handshake

RESULTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "results")

PROFILES = [
    ["x25519", "ml-kem-768"],
    ["x25519", "ml-kem-768", "frodokem-640-aes"],
    ["x25519", "ml-kem-768", "frodokem-640-aes", "ml-kem-1024"],
    ["x25519", "ml-kem-512", "ml-kem-768", "ml-kem-1024", "frodokem-640-aes"],
]


def measure(kems, suite, runs, warmup):
    hs = {m: Ikev2Handshake(kems, suite=suite, method=m) for m in ("rfc9370", "spks")}
    acc = {m: [] for m in hs}
    for m in hs:
        for _ in range(warmup):
            hs[m].run()
    for _ in range(runs):
        for m in hs:
            acc[m].append(hs[m].run())
    out = {}
    for m, xs in acc.items():
        out[m] = {
            "method": m,
            "profile": "+".join(kems),
            "n_add": len(kems) - 1,
            "messages": xs[0].messages,
            "round_trips": xs[0].round_trips,
            "wire_bytes": xs[0].wire_bytes,
            "ks_compressions": xs[0].ks_compressions,
            "ia_compressions": xs[0].ia_compressions,
            "ks_prf_calls": xs[0].ks_prf_calls,
            "live_key_bytes": xs[0].live_key_bytes,
            "init_time_ms": min(a.init_time for a in xs) * 1e3,
            "resp_time_ms": min(a.resp_time for a in xs) * 1e3,
            "total_time_ms": min(a.init_time + a.resp_time for a in xs) * 1e3,
            "ks_time_us": min(a.ks_time for a in xs) * 1e6,
        }
    return out


def main():
    os.makedirs(RESULTS, exist_ok=True)
    suite = SUITES[sys.argv[1] if len(sys.argv) > 1 else "gcm256-sha256"]
    runs = int(os.environ.get("RUNS", "60"))
    warmup = int(os.environ.get("WARMUP", "15"))
    rows = []
    for kems in PROFILES:
        got = measure(kems, suite, runs, warmup)
        for method in ["rfc9370", "spks"]:
            r = got[method]
            rows.append(r)
            print(
                f"{r['profile']:52s} {method:8s} rt={r['round_trips']} "
                f"bytes={r['wire_bytes']:6d} ks={r['ks_time_us']:8.2f}us "
                f"comp={r['ks_compressions']:4d} tot={r['total_time_ms']:7.3f}ms "
                f"live={r['live_key_bytes']}"
            )
    out = os.path.join(RESULTS, "handshake.json")
    with open(out, "w") as f:
        json.dump(rows, f, indent=1)
    print("wrote", out)


if __name__ == "__main__":
    main()
