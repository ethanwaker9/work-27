import json
import os
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import LogLocator, LogFormatterSciNotation, NullFormatter

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RESULTS = os.path.join(BASE, "results")
FIGS = os.path.join(BASE, "figures")

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.serif": ["Times New Roman", "DejaVu Serif"],
        "font.size": 7,
        "axes.labelsize": 7.5,
        "axes.titlesize": 7.5,
        "legend.fontsize": 5.8,
        "xtick.labelsize": 6.5,
        "ytick.labelsize": 6.5,
        "lines.linewidth": 1.0,
        "lines.markersize": 3.0,
        "axes.grid": True,
        "grid.alpha": 1.0,
        "grid.color": "#cfcfcf",
        "grid.linewidth": 0.4,
        "figure.dpi": 200,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.015,
    }
)

SHOW = [
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

STYLE = {
    "RFC 9370": ("o", "-", "#111111"),
    "Concat": ("s", "--", "#1f77b4"),
    "Concat-CT": ("^", "--", "#ff7f0e"),
    "CatKDF": ("v", "--", "#2ca02c"),
    "ChainExt": ("<", "--", "#d62728"),
    "GHP-XorROM": (">", ":", "#9467bd"),
    "GHP-XorPRF": ("P", ":", "#8c564b"),
    "GHP-XorPRF-opt": ("X", ":", "#e377c2"),
    "XtM": ("D", "-.", "#7f7f7f"),
    "dualPRF": ("p", "-.", "#bcbd22"),
    "Nested-N": ("h", "-.", "#17becf"),
    "KeyCombine": ("*", "-.", "#aec7e8"),
    "X-Wing": ("d", "--", "#c49c94"),
    "SPKS": ("o", "-", "#b30000"),
}


def load(name):
    with open(os.path.join(RESULTS, name)) as f:
        return json.load(f)


def series(rows, method, key):
    xs, ys = [], []
    for r in rows:
        if r["method"] == method:
            xs.append(r["n_add"])
            ys.append(r[key])
    return xs, ys


def draw(ax, rows, key, ylabel, logy=True):
    for m in SHOW:
        mk, ls, c = STYLE[m]
        xs, ys = series(rows, m, key)
        lw = 1.7 if m == "SPKS" else (1.2 if m == "RFC 9370" else 0.85)
        ax.plot(xs, ys, marker=mk, linestyle=ls, color=c, label=m, linewidth=lw,
                markersize=3.6 if m in ("SPKS", "RFC 9370") else 2.6)
    if logy:
        ax.set_yscale("log")
        ax.yaxis.set_major_locator(LogLocator(base=10.0, numticks=12))
        ax.yaxis.set_minor_locator(LogLocator(base=10.0, subs=(2.0, 5.0), numticks=24))
        ax.yaxis.set_minor_formatter(LogFormatterSciNotation(labelOnlyBase=False,
                                                             minor_thresholds=(4, 0.6)))
        ax.tick_params(axis="y", which="minor", labelsize=5.2)
    ax.set_xlabel("number of additional key exchanges $n$")
    ax.set_ylabel(ylabel)
    ax.set_xticks(range(1, 8))
    ax.margins(x=0.03)


def fig_cost(rows):
    fig, axes = plt.subplots(1, 2, figsize=(7.0, 1.95))
    draw(axes[0], rows, "model_compressions", "compression calls $T_{\\mathrm{cf}}$")
    draw(axes[1], rows, "time_min_us", "key-schedule time ($\\mu$s)")
    fig.tight_layout(rect=(0, 0, 1, 0.845))
    h, l = axes[0].get_legend_handles_labels()
    fig.legend(h, l, loc="upper center", ncol=7, frameon=False,
               bbox_to_anchor=(0.5, 1.015), handlelength=2.1, columnspacing=1.0)
    fig.savefig(os.path.join(FIGS, "fig_cost.eps"), format="eps")
    plt.close(fig)


def fig_space(rows):
    fig, axes = plt.subplots(1, 3, figsize=(7.0, 1.85))
    draw(axes[0], rows, "peak_measured_bytes", "peak working memory (B)")
    draw(axes[1], rows, "keymat_bytes", "key material $M_{\\mathrm{key}}$ (B)", logy=False)
    draw(axes[2], rows, "hashed_bytes", "PRF input bytes")
    fig.tight_layout(rect=(0, 0, 1, 0.835))
    h, l = axes[0].get_legend_handles_labels()
    fig.legend(h, l, loc="upper center", ncol=7, frameon=False,
               bbox_to_anchor=(0.5, 1.02), handlelength=2.1, columnspacing=1.0)
    fig.savefig(os.path.join(FIGS, "fig_space.eps"), format="eps")
    plt.close(fig)


def fig_bars(hs, kem):
    labels = []
    ks9370, ksspks, tot9370, totspks = [], [], [], []
    for r in hs:
        if r["method"] == "rfc9370":
            labels.append(str(r["n_add"]))
            ks9370.append(r["ks_time_us"])
            tot9370.append(r["total_time_ms"])
        else:
            ksspks.append(r["ks_time_us"])
            totspks.append(r["total_time_ms"])
    fig, axes = plt.subplots(1, 3, figsize=(7.0, 1.72))
    x = range(len(labels))
    w = 0.36
    for ax, a, b, ylab in (
        (axes[0], ks9370, ksspks, "key-schedule time ($\\mu$s)"),
        (axes[1], tot9370, totspks, "handshake CPU time (ms)"),
    ):
        ax.bar([i - w / 2 for i in x], a, w, label="RFC 9370", color="#4c72b0",
               edgecolor="black", linewidth=0.4)
        ax.bar([i + w / 2 for i in x], b, w, label="SPKS", color="#b30000",
               edgecolor="black", linewidth=0.4)
        ax.set_ylabel(ylab)
        ax.set_xticks(list(x))
        ax.set_xticklabels(labels)
        ax.set_xlabel("additional key exchanges $n$")
        ax.legend(frameon=False, loc="upper left")
        ax.grid(axis="x", visible=False)
        ax.set_ylim(0, max(a) * 1.32)
    names = [r["scheme"].replace("ML-KEM-", "") for r in kem]
    cca = [r["decaps_cca_us"] / 1000.0 for r in kem]
    cpa = [r["decaps_cpa_us"] / 1000.0 for r in kem]
    xk = range(len(names))
    axes[2].bar([i - w / 2 for i in xk], cca, w, label="IND-CCA", color="#4c72b0",
                edgecolor="black", linewidth=0.4)
    axes[2].bar([i + w / 2 for i in xk], cpa, w, label="IND-CPA", color="#b30000",
                edgecolor="black", linewidth=0.4)
    for i, (a, b) in enumerate(zip(cca, cpa)):
        axes[2].text(i + w / 2, b, f"{a / b:.2f}$\\times$", ha="center", va="bottom",
                     fontsize=5.6)
    axes[2].set_xticks(list(xk))
    axes[2].set_xticklabels(names)
    axes[2].set_xlabel("ML-KEM parameter set")
    axes[2].set_ylabel("decapsulation (ms)")
    axes[2].set_ylim(0, max(cca) * 1.32)
    axes[2].legend(frameon=False, loc="upper left")
    axes[2].grid(axis="x", visible=False)
    fig.tight_layout()
    fig.savefig(os.path.join(FIGS, "fig_bars.eps"), format="eps")
    plt.close(fig)


def main():
    os.makedirs(FIGS, exist_ok=True)
    rows = load("combiners_gcm256-sha256.json")
    fig_cost(rows)
    fig_space(rows)
    fig_bars(load("handshake.json"), load("kem_transform.json"))
    print("figures written to", FIGS)


if __name__ == "__main__":
    main()
