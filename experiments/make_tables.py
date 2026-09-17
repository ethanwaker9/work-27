import json
import os
import sys

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(BASE, "results")
TABLES = os.path.join(BASE, "tables")

ORDER = [
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

CITE = {
    "RFC 9370": "\\cite{rfc9370}",
    "Concat": "\\cite{sp80056c,petcher2023}",
    "Concat-CT": "\\cite{petcher2023}",
    "CatKDF": "\\cite{etsi103744,backendal2025kdf}",
    "ChainExt": "\\cite{etsi103744,rfc8784}",
    "GHP-XorROM": "\\cite{giacon2018}",
    "GHP-XorPRF": "\\cite{giacon2018}",
    "GHP-XorPRF-opt": "\\cite{giacon2018}",
    "XtM": "\\cite{bindel2019}",
    "dualPRF": "\\cite{bindel2019}",
    "Nested-N": "\\cite{bindel2019}",
    "KeyCombine": "\\cite{aviram2022}",
    "X-Wing": "\\cite{xwing2024}",
    "SPKS": "this work",
}

BINDS = {
    "RFC 9370": "no",
    "Concat": "no",
    "Concat-CT": "yes",
    "CatKDF": "yes",
    "ChainExt": "yes",
    "GHP-XorROM": "yes",
    "GHP-XorPRF": "yes",
    "GHP-XorPRF-opt": "yes",
    "XtM": "yes",
    "dualPRF": "yes",
    "Nested-N": "yes",
    "KeyCombine": "no",
    "X-Wing": "partial",
    "SPKS": "yes",
}


def load(name):
    with open(os.path.join(RESULTS, name)) as f:
        return json.load(f)


def pick(rows, method, n):
    for r in rows:
        if r["method"] == method and r["n_add"] == n:
            return r
    raise KeyError(method)


def bold_min(values, fmt):
    m = min(values)
    return [("\\textbf{" + fmt(v) + "}") if v == m else fmt(v) for v in values]


def tab_main(rows):
    ns = [1, 3]
    cols = {}
    for m in ORDER:
        r1 = pick(rows, m, 1)
        r3 = pick(rows, m, 3)
        cols[m] = (r1, r3)
    comp1 = bold_min([cols[m][0]["model_compressions"] for m in ORDER], lambda v: f"{v}")
    comp3 = bold_min([cols[m][1]["model_compressions"] for m in ORDER], lambda v: f"{v}")
    depth3 = bold_min([cols[m][1]["depth"] for m in ORDER], lambda v: f"{v}")
    mkey3 = bold_min([cols[m][1]["keymat_bytes"] for m in ORDER], lambda v: f"{v}")
    mem1 = bold_min([cols[m][0]["peak_measured_bytes"] for m in ORDER], lambda v: f"{v}")
    mem3 = bold_min([cols[m][1]["peak_measured_bytes"] for m in ORDER], lambda v: f"{v}")
    t1 = bold_min([round(cols[m][0]["time_min_us"], 2) for m in ORDER], lambda v: f"{v:.2f}")
    t3 = bold_min([round(cols[m][1]["time_min_us"], 2) for m in ORDER], lambda v: f"{v:.2f}")
    lines = []
    for i, m in enumerate(ORDER):
        name = "\\textbf{SPKS (ours)}" if m == "SPKS" else m
        lines.append(
            " & ".join(
                [
                    name,
                    CITE[m],
                    BINDS[m],
                    comp1[i],
                    comp3[i],
                    depth3[i],
                    mkey3[i],
                    mem1[i],
                    mem3[i],
                    t1[i],
                    t3[i],
                ]
            )
            + " \\\\"
        )
    return "\n".join(lines)


def tab_scaling(rows):
    lines = []
    for m in ORDER:
        vals = [pick(rows, m, n)["model_compressions"] for n in range(1, 8)]
        name = "\\textbf{SPKS (ours)}" if m == "SPKS" else m
        cells = bold_min(vals, lambda v: f"{v}") if False else [f"{v}" for v in vals]
        lines.append(name + " & " + " & ".join(cells) + " \\\\")
    return "\n".join(lines)


def tab_handshake(rows):
    lines = []
    by = {}
    for r in rows:
        by.setdefault(r["n_add"], {})[r["method"]] = r
    for n in sorted(by):
        a = by[n]["rfc9370"]
        b = by[n]["spks"]
        lines.append(
            " & ".join(
                [
                    str(n),
                    str(a["round_trips"]),
                    f"{a['wire_bytes'] / 1024:.1f}",
                    f"{a['ks_compressions']}",
                    f"\\textbf{{{b['ks_compressions']}}}",
                    f"{a['ks_time_us']:.1f}",
                    f"\\textbf{{{b['ks_time_us']:.1f}}}",
                    f"{a['live_key_bytes']}",
                    f"\\textbf{{{b['live_key_bytes']}}}",
                    f"{a['total_time_ms']:.3f}",
                    f"\\textbf{{{b['total_time_ms']:.3f}}}",
                ]
            )
            + " \\\\"
        )
    return "\n".join(lines)


def tab_kem(rows):
    lines = []
    for r in rows:
        lines.append(
            " & ".join(
                [
                    r["scheme"],
                    f"{r['decaps_cca_us'] / 1000:.2f}",
                    f"\\textbf{{{r['decaps_cpa_us'] / 1000:.2f}}}",
                    f"{r['speedup']:.2f}",
                    f"{r.get('liboqs_encaps_us', 0):.1f}",
                    f"{r.get('liboqs_decaps_us', 0):.1f}",
                ]
            )
            + " \\\\"
        )
    return "\n".join(lines)


def tab_suites():
    names = {
        "gcm256-sha256": "GCM-256 / SHA-256",
        "cbc256-sha256": "CBC-256 + HMAC / SHA-256",
        "gcm256-sha384": "GCM-256 / SHA-384",
    }
    lines = []
    for key, label in names.items():
        d = load(f"combiners_{key}.json")
        sp = {r["n_add"]: r for r in d if r["method"] == "SPKS"}
        rf = {r["n_add"]: r for r in d if r["method"] == "RFC 9370"}
        tr, mr = [], []
        for n in range(1, 8):
            rows = [r for r in d if r["n_add"] == n and r["method"] != "SPKS"]
            tr += [r["time_min_us"] / sp[n]["time_min_us"] for r in rows]
            mr += [r["peak_measured_bytes"] / sp[n]["peak_measured_bytes"] for r in rows]
        lines.append(
            " & ".join(
                [
                    label,
                    f"{rf[1]['model_compressions']}--{rf[7]['model_compressions']}",
                    f"\\textbf{{{sp[1]['model_compressions']}--{sp[7]['model_compressions']}}}",
                    f"{rf[3]['depth']}",
                    f"\\textbf{{{sp[3]['depth']}}}",
                    f"{rf[3]['keymat_bytes']}",
                    f"\\textbf{{{sp[3]['keymat_bytes']}}}",
                    f"{min(tr):.2f}--{max(tr):.1f}",
                    f"{min(mr):.2f}--{max(mr):.0f}",
                ]
            )
            + " \\\\"
        )
    return "\n".join(lines)


def main():
    os.makedirs(TABLES, exist_ok=True)
    comb = load("combiners_gcm256-sha256.json")
    out = {
        "tab_main.tex": tab_main(comb),
        "tab_scaling.tex": tab_scaling(comb),
        "tab_handshake.tex": tab_handshake(load("handshake.json")),
        "tab_kem.tex": tab_kem(load("kem_transform.json")),
        "tab_suites.tex": tab_suites(),
    }
    for k, v in out.items():
        with open(os.path.join(TABLES, k), "w") as f:
            f.write(v + "\n\\bottomrule\n\\end{tabular}%")
        print("---", k)
        print(v)


if __name__ == "__main__":
    main()
