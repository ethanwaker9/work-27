import hashlib
import hmac as _hmac

from .params import HASH_PARAMS


IPAD = {b: int.from_bytes(b"\x36" * b, "big") for b in (64, 128)}
OPAD = {b: int.from_bytes(b"\x5c" * b, "big") for b in (64, 128)}


class CostCounter:
    def __init__(self):
        self.compressions = 0
        self.prf_calls = 0
        self.hashed_bytes = 0
        self.keymat_bytes = 0
        self.depth = 0

    def reset(self):
        self.__init__()

    def snapshot(self):
        return {
            "compressions": self.compressions,
            "prf_calls": self.prf_calls,
            "hashed_bytes": self.hashed_bytes,
            "keymat_bytes": self.keymat_bytes,
            "depth": self.depth,
        }


def md_blocks(msg_len: int, block: int, len_field: int) -> int:
    return -(-(msg_len + 1 + len_field) // block)


def hmac_compressions(key_len: int, msg_len: int, hash_name: str) -> int:
    p = HASH_PARAMS[hash_name]
    b, o, lf = p["block"], p["out"], p["len_field"]
    pre = md_blocks(key_len, b, lf) if key_len > b else 0
    inner = md_blocks(b + msg_len, b, lf)
    outer = md_blocks(b + o, b, lf)
    return pre + inner + outer


def sponge_calls(msg_len: int, rate: int = 136) -> int:
    return max(1, -(-(msg_len + 1) // rate))


class Prf:
    def __init__(self, hash_name: str = "sha256", counter: CostCounter = None):
        self.hash_name = hash_name
        self.counter = counter
        self.out = HASH_PARAMS[hash_name]["out"]
        self.block = HASH_PARAMS[hash_name]["block"]
        self._cache = {}

    def _states(self, key: bytes):
        st = self._cache.get(key)
        if st is None:
            k = key if len(key) <= self.block else hashlib.new(self.hash_name, key).digest()
            k = k + b"\x00" * (self.block - len(k))
            ki = int.from_bytes(k, "big")
            inner = hashlib.new(self.hash_name, (ki ^ IPAD[self.block]).to_bytes(self.block, "big"))
            outer = hashlib.new(self.hash_name, (ki ^ OPAD[self.block]).to_bytes(self.block, "big"))
            st = (inner, outer)
            if len(self._cache) >= 256:
                self._cache.clear()
            self._cache[key] = st
        return st

    def _account(self, key_len: int, msg_len: int, depth: int = 1):
        if self.counter is not None:
            self.counter.compressions += hmac_compressions(key_len, msg_len, self.hash_name)
            self.counter.prf_calls += 1
            self.counter.hashed_bytes += msg_len
            self.counter.depth += depth

    def __call__(self, key: bytes, data: bytes, depth: int = 1) -> bytes:
        self._account(len(key), len(data), depth)
        inner, outer = self._states(key)
        i = inner.copy()
        i.update(data)
        o = outer.copy()
        o.update(i.digest())
        return o.digest()

    def plus(self, key: bytes, seed: bytes, length: int) -> bytes:
        n = -(-length // self.out)
        parts = []
        prev = b""
        for i in range(1, n + 1):
            prev = self(key, prev + seed + bytes((i,)))
            parts.append(prev)
        if self.counter is not None:
            self.counter.keymat_bytes += length
        return b"".join(parts)[:length]

    def expand(self, key: bytes, label: bytes, length: int) -> bytes:
        n = -(-length // self.out)
        parts = [self(key, label + bytes((i,))) for i in range(1, n + 1)]
        if self.counter is not None:
            self.counter.keymat_bytes += length
            self.counter.depth -= n - 1
        return b"".join(parts)[:length]


def sha3_256(data: bytes, counter: CostCounter = None) -> bytes:
    if counter is not None:
        counter.compressions += sponge_calls(len(data) + 1, 136) + 1
        counter.prf_calls += 1
        counter.hashed_bytes += len(data)
        counter.depth += 1
    return hashlib.sha3_256(data).digest()


def shake256(data: bytes, length: int, counter: CostCounter = None) -> bytes:
    if counter is not None:
        counter.compressions += sponge_calls(len(data) + 1, 136) + max(1, -(-length // 136))
        counter.prf_calls += 1
        counter.hashed_bytes += len(data)
        counter.keymat_bytes += length
        counter.depth += 1
    return hashlib.shake_256(data).digest(length)
