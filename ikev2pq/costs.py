from .params import HASH_PARAMS, Suite
from .prf import hmac_compressions, md_blocks


def _hc(k, m, h):
    return hmac_compressions(k, m, h)


def prf_plus_cost(key_len, seed_len, out_len, suite: Suite):
    h = suite.prf_hash
    o = suite.out
    n = -(-out_len // o)
    total = 0
    for i in range(1, n + 1):
        m = (0 if i == 1 else o) + seed_len + 1
        total += _hc(key_len, m, h)
    return total


def expand_ctr_cost(key_len, label_len, out_len, suite: Suite):
    h = suite.prf_hash
    o = suite.out
    n = -(-out_len // o)
    return n * _hc(key_len, label_len + 1, h)


def stage0_full(suite: Suite, ss0):
    h = suite.prf_hash
    return _hc(2 * suite.nonce_len, ss0, h) + prf_plus_cost(
        suite.out, suite.context_len, suite.keymat_len, suite
    )


def stage0_partial(suite: Suite, ss0):
    h = suite.prf_hash
    return _hc(2 * suite.nonce_len, ss0, h) + prf_plus_cost(
        suite.out, suite.context_len, suite.protect_len, suite
    )


def cost_rfc9370(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    total = stage0_full(suite, ss_lens[0])
    depth = 1 + -(-suite.keymat_len // suite.out)
    for j in range(1, len(ss_lens)):
        total += _hc(suite.out, ss_lens[j] + 2 * suite.nonce_len, h)
        total += prf_plus_cost(suite.out, suite.context_len, suite.keymat_len, suite)
        depth += 1 + -(-suite.keymat_len // suite.out)
    keymat = len(ss_lens) * (suite.out + suite.keymat_len)
    peak = 2 * suite.keymat_len + 2 * suite.out
    return {"comp": total, "depth": depth, "keymat": keymat, "peak": peak}


def _deferred(suite: Suite, ss_lens, core_comp, core_depth, core_peak, expand_comp=None,
              expand_depth=None):
    total = stage0_partial(suite, ss_lens[0]) + core_comp
    if expand_comp is None:
        expand_comp = prf_plus_cost(suite.out, suite.context_len, suite.keymat_len, suite)
        expand_depth = -(-suite.keymat_len // suite.out)
    total += expand_comp
    depth = 1 + -(-suite.protect_len // suite.out) + core_depth + expand_depth
    keymat = suite.out + suite.protect_len + suite.out + suite.keymat_len
    peak = suite.protect_len + suite.keymat_len + 2 * suite.out + core_peak
    return {"comp": total, "depth": depth, "keymat": keymat, "peak": peak}


def cost_concat(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    c = _hc(2 * suite.nonce_len, sum(ss_lens), h)
    return _deferred(suite, ss_lens, c, 1, sum(ss_lens))


def cost_concat_ct(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    c = _hc(2 * suite.nonce_len, sum(ss_lens), h)
    e = prf_plus_cost(suite.out, suite.context_len + sum(ct_lens), suite.keymat_len, suite)
    return _deferred(suite, ss_lens, c, 1, sum(ss_lens) + sum(ct_lens), e,
                     -(-suite.keymat_len // suite.out))


def cost_catkdf(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    c = _hc(2 * suite.nonce_len, sum(ss_lens) + sum(ct_lens) + sum(pk_lens), h)
    return _deferred(suite, ss_lens, c, 1, sum(ss_lens) + sum(ct_lens) + sum(pk_lens))


def cost_chainext(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    c = _hc(2 * suite.nonce_len, ss_lens[0], h)
    for j in range(1, len(ss_lens)):
        c += _hc(suite.out, ss_lens[j], h)
    e = prf_plus_cost(suite.out, suite.context_len + sum(ct_lens), suite.keymat_len, suite)
    return _deferred(suite, ss_lens, c, len(ss_lens), sum(ct_lens), e,
                     -(-suite.keymat_len // suite.out))


def cost_ghp_xor(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    C = sum(ct_lens)
    c = sum(_hc(s, C, h) for s in ss_lens)
    return _deferred(suite, ss_lens, c, 1, C + sum(ss_lens))


def cost_ghp_xor_opt(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    C = sum(ct_lens)
    c = sum(_hc(ss_lens[i], C - ct_lens[i], h) for i in range(len(ss_lens)))
    return _deferred(suite, ss_lens, c, 1, C + sum(ss_lens))


def cost_ghp_rom(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    C = sum(ct_lens)
    c = _hc(min(ss_lens), C, h)
    return _deferred(suite, ss_lens, c, 1, C + sum(ss_lens))


def cost_xtm(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    C = sum(ct_lens)
    half = min(ss_lens) // 2
    c = _hc(half, C, h)
    e = prf_plus_cost(half + suite.out, suite.context_len, suite.keymat_len, suite)
    return _deferred(suite, ss_lens, c, 1, C + sum(ss_lens), e,
                     -(-suite.keymat_len // suite.out))


def cost_dualprf(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    C = sum(ct_lens)
    c = 0
    cur = ss_lens[0]
    for j in range(1, len(ss_lens)):
        c += _hc(ss_lens[j], cur, h)
        cur = suite.out
    c += _hc(cur, C, h)
    return _deferred(suite, ss_lens, c, len(ss_lens), C + sum(ss_lens))


def cost_nested(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    C = sum(ct_lens)
    c = _hc(ss_lens[0], label_len, h)
    cur = suite.out
    for j in range(1, len(ss_lens)):
        c += _hc(ss_lens[j], cur, h)
        cur = suite.out
    c += _hc(cur, C, h)
    return _deferred(suite, ss_lens, c, len(ss_lens) + 1, C + sum(ss_lens))


def cost_keycombine(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    n = len(ss_lens)
    exp = 3
    c = sum(_hc(2 * suite.nonce_len, s, h) for s in ss_lens)
    c += sum(exp * md_blocks(suite.block + s, suite.block, suite.len_field) for s in ss_lens)
    u = exp * 32
    c += n * _hc(suite.out, 1 + (n - 1) * u, h)
    c += md_blocks(suite.out, suite.block, suite.len_field)
    return _deferred(suite, ss_lens, c, 3, n * u + sum(ss_lens))


def cost_xwing(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    c = _hc(2 * suite.nonce_len, 6 + sum(ss_lens) + ct_lens[0] + pk_lens[0], h)
    return _deferred(suite, ss_lens, c, 1, sum(ss_lens) + ct_lens[0] + pk_lens[0])


def spks_stage0_cost(suite: Suite, ss0, label_len=9):
    h = suite.prf_hash
    return _hc(2 * suite.nonce_len, ss0 + 2 * suite.spi_len, h) + expand_ctr_cost(
        suite.out, label_len, suite.protect_len, suite
    )


def cost_spks(suite: Suite, ss_lens, ct_lens, pk_lens, label_len=8):
    h = suite.prf_hash
    base = spks_stage0_cost(suite, ss_lens[0])
    core = _hc(2 * suite.out, sum(ss_lens), h) + expand_ctr_cost(
        suite.out, label_len, suite.keymat_len, suite
    )
    return {
        "comp": base + core,
        "depth": 2 + 2,
        "keymat": 2 * suite.out + suite.protect_len + suite.keymat_len,
        "peak": suite.protect_len + suite.keymat_len + 2 * suite.out + sum(ss_lens),
    }


COST_TABLE = {
    "RFC 9370": cost_rfc9370,
    "Concat": cost_concat,
    "Concat-CT": cost_concat_ct,
    "CatKDF": cost_catkdf,
    "ChainExt": cost_chainext,
    "GHP-XorPRF": cost_ghp_xor,
    "GHP-XorPRF-opt": cost_ghp_xor_opt,
    "GHP-XorROM": cost_ghp_rom,
    "XtM": cost_xtm,
    "dualPRF": cost_dualprf,
    "Nested-N": cost_nested,
    "KeyCombine": cost_keycombine,
    "X-Wing": cost_xwing,
    "SPKS": cost_spks,
}
