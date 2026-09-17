import hashlib
from dataclasses import dataclass, field
from typing import List

from .params import Suite
from .prf import Prf, CostCounter, sha3_256, shake256


@dataclass
class Context:
    ni: bytes
    nr: bytes
    spii: bytes
    spir: bytes
    cts: List[bytes] = field(default_factory=list)
    pks: List[bytes] = field(default_factory=list)
    theta: bytes = b""

    @property
    def salt(self) -> bytes:
        return self.ni + self.nr

    @property
    def seed(self) -> bytes:
        return self.ni + self.nr + self.spii + self.spir

    @property
    def ctvec(self) -> bytes:
        return b"".join(self.cts)


LABEL = b"IKEv2 SP"
LABEL0 = b"IKEv2 SP0"


def _split_keys(km: bytes, suite: Suite):
    off = 0
    out = {}
    for name in ["sk_d", "sk_ai", "sk_ar", "sk_ei", "sk_er", "sk_pi", "sk_pr"]:
        n = getattr(suite, name)
        out[name] = km[off : off + n]
        off += n
    return out


def rfc9370(secrets, ctx: Context, suite: Suite, prf: Prf):
    skeyseed = prf(ctx.salt, secrets[0])
    km = prf.plus(skeyseed, ctx.seed, suite.keymat_len)
    generations = [km]
    for j in range(1, len(secrets)):
        sk_d = km[: suite.sk_d]
        skeyseed = prf(sk_d, secrets[j] + ctx.ni + ctx.nr)
        km = prf.plus(skeyseed, ctx.seed, suite.keymat_len)
        generations.append(km)
    return km, generations


def stage0_protection(ss0: bytes, ctx: Context, suite: Suite, prf: Prf):
    skeyseed = prf(ctx.salt, ss0)
    return prf.plus(skeyseed, ctx.seed, suite.protect_len)


def concat_kdf(secrets, ctx: Context, suite: Suite, prf: Prf):
    z = b"".join(secrets)
    skeyseed = prf(ctx.salt, z)
    return prf.plus(skeyseed, ctx.seed, suite.keymat_len)


def concat_kdf_bound(secrets, ctx: Context, suite: Suite, prf: Prf):
    z = b"".join(secrets)
    skeyseed = prf(ctx.salt, z)
    return prf.plus(skeyseed, ctx.seed + ctx.ctvec, suite.keymat_len)


def catkdf(secrets, ctx: Context, suite: Suite, prf: Prf):
    z = b"".join(secrets)
    skeyseed = prf(ctx.salt, z + ctx.ctvec + b"".join(ctx.pks))
    return prf.plus(skeyseed, ctx.seed, suite.keymat_len)


def chained_extract(secrets, ctx: Context, suite: Suite, prf: Prf):
    sigma = prf(ctx.salt, secrets[0])
    for j in range(1, len(secrets)):
        sigma = prf(sigma, secrets[j])
    return prf.plus(sigma, ctx.seed + ctx.ctvec, suite.keymat_len)


def ghp_xor_prf(secrets, ctx: Context, suite: Suite, prf: Prf):
    c = ctx.ctvec
    acc = bytes(prf.out)
    for s in secrets:
        t = prf(s, c)
        acc = bytes(a ^ b for a, b in zip(acc, t))
    return prf.plus(acc, ctx.seed, suite.keymat_len)


def ghp_xor_prf_opt(secrets, ctx: Context, suite: Suite, prf: Prf):
    acc = bytes(prf.out)
    for i, s in enumerate(secrets):
        c = b"".join(ctx.cts[:i] + ctx.cts[i + 1 :])
        t = prf(s, c)
        acc = bytes(a ^ b for a, b in zip(acc, t))
    return prf.plus(acc, ctx.seed, suite.keymat_len)


def ghp_xor_rom(secrets, ctx: Context, suite: Suite, prf: Prf):
    m = min(len(s) for s in secrets)
    acc = bytes(m)
    for s in secrets:
        acc = bytes(a ^ b for a, b in zip(acc, s[:m]))
    k = prf(acc, ctx.ctvec)
    return prf.plus(k, ctx.seed, suite.keymat_len)


def bindel_xtm(secrets, ctx: Context, suite: Suite, prf: Prf):
    half = min(len(s) for s in secrets) // 2
    kl = bytes(half)
    kr = bytes(half)
    for s in secrets:
        kl = bytes(a ^ b for a, b in zip(kl, s[:half]))
        kr = bytes(a ^ b for a, b in zip(kr, s[half : 2 * half]))
    tag = prf(kr, ctx.ctvec)
    return prf.plus(kl + tag, ctx.seed, suite.keymat_len)


def bindel_dualprf(secrets, ctx: Context, suite: Suite, prf: Prf):
    sigma = secrets[0]
    for j in range(1, len(secrets)):
        sigma = prf(secrets[j], sigma)
    k = prf(sigma, ctx.ctvec)
    return prf.plus(k, ctx.seed, suite.keymat_len)


def bindel_nested(secrets, ctx: Context, suite: Suite, prf: Prf):
    sigma = prf(secrets[0], LABEL)
    for j in range(1, len(secrets)):
        sigma = prf(secrets[j], sigma)
    k = prf(sigma, ctx.ctvec)
    return prf.plus(k, ctx.seed, suite.keymat_len)


def aviram_keycombine(secrets, ctx: Context, suite: Suite, prf: Prf):
    exp = 3
    blocks = [bytes([i]) * suite.block for i in range(exp)]
    ks = []
    us = []
    for s in secrets:
        ks.append(prf(ctx.salt, s))
        u = b""
        for b in blocks:
            if prf.counter is not None:
                prf.counter.compressions += 2
                prf.counter.prf_calls += 1
                prf.counter.hashed_bytes += len(s)
            u += hashlib.sha256(b + s).digest()
        us.append(u)
    acc = bytes(prf.out)
    for i in range(len(secrets)):
        data = bytes([i]) + b"".join(us[j] for j in range(len(secrets)) if j != i)
        t = prf(ks[i], data)
        acc = bytes(a ^ b for a, b in zip(acc, t))
    if prf.counter is not None:
        prf.counter.compressions += 1
        prf.counter.prf_calls += 1
    k = hashlib.sha256(acc).digest()
    return prf.plus(k, ctx.seed, suite.keymat_len)


def xwing_native(secrets, ctx: Context, suite: Suite, prf: Prf):
    data = b"\\.//^\\" + b"".join(secrets) + ctx.cts[0] + ctx.pks[0]
    k = sha3_256(data, prf.counter)
    return shake256(k + ctx.seed, suite.keymat_len, prf.counter)


def xwing_ikev2(secrets, ctx: Context, suite: Suite, prf: Prf):
    data = b"\\.//^\\" + b"".join(secrets) + ctx.cts[0] + ctx.pks[0]
    k = prf(ctx.salt, data)
    return prf.plus(k, ctx.seed, suite.keymat_len)


def spks_stage0(ss0: bytes, ctx: Context, suite: Suite, prf: Prf):
    sigma0 = prf(ctx.salt, ss0 + ctx.spii + ctx.spir)
    return prf.expand(sigma0, LABEL0, suite.protect_len)


def spks(secrets, ctx: Context, suite: Suite, prf: Prf):
    sigma = prf(ctx.theta, b"".join(secrets))
    return prf.expand(sigma, LABEL, suite.keymat_len)


DEFERRED_COMBINERS = {
    "Concat": concat_kdf,
    "Concat-CT": concat_kdf_bound,
    "CatKDF": catkdf,
    "ChainExt": chained_extract,
    "GHP-XorPRF": ghp_xor_prf,
    "GHP-XorPRF-opt": ghp_xor_prf_opt,
    "GHP-XorROM": ghp_xor_rom,
    "XtM": bindel_xtm,
    "dualPRF": bindel_dualprf,
    "Nested-N": bindel_nested,
    "KeyCombine": aviram_keycombine,
    "X-Wing": xwing_ikev2,
    "SPKS": spks,
}
