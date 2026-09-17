import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.dirname(HERE)

STEPS = [
    ("combiner cost and timing", ["bench_combiners.py"]),
    ("full handshake", ["bench_handshake.py"]),
    ("ephemeral KEM decapsulation", ["bench_kem_transform.py"]),
    ("figures", ["make_figures.py"]),
    ("tables", ["make_tables.py"]),
]


def main():
    env = dict(os.environ)
    env.setdefault("REPS", "2500")
    env.setdefault("ROUNDS", "15")
    env.setdefault("RUNS", "250")
    env.setdefault("WARMUP", "40")
    for name, args in STEPS:
        print(f"[run_all] {name}")
        r = subprocess.run([sys.executable, os.path.join(HERE, *args)], cwd=BASE, env=env)
        if r.returncode != 0:
            print(f"[run_all] step failed: {name}")
            return r.returncode
    print("[run_all] results in", os.path.join(BASE, "results"))
    print("[run_all] figures in", os.path.join(BASE, "figures"))
    print("[run_all] tables in", os.path.join(BASE, "tables"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
