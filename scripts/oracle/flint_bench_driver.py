#!/usr/bin/env python3
"""Shared python-flint persistent-subprocess bench driver for Hex.

Loops on stdin, one JSON request per line; emits one JSON reply per
request on stdout. Imports `flint` once at startup and reuses the
loaded module for every subsequent call, so the only per-call cost
is JSON encode/decode and the FLINT operation itself.

Per `SPEC/benchmarking.md` (post-#3657) §"External comparators"
§"Process call": this driver is the persistent-subprocess shape
required when per-call overhead is non-negligible. The bench harness
spawns the driver once per `lake exe hexfoo_bench run` invocation,
holds its stdin / stdout handles in an `IO.Ref` (see
`Hex/BenchOracle/Flint.lean`), and reuses the file descriptors
across every measured call in that bench process. One process
startup is amortised across all comparator calls in the run.

## Framing

One request per line on stdin. Each request is a single JSON object
followed by `\\n`. Each reply is a single JSON object followed by
`\\n`. The driver flushes stdout after every reply so the consumer
sees the answer immediately. EOF on stdin terminates the driver.

Request shape::

    {"family": "<family>", "op": "<op>", ...family-specific fields}

Reply shape on success::

    {"ok": true, "result": <family-specific value>}

Reply shape on failure (malformed request, unknown family/op,
FLINT error, etc.)::

    {"ok": false, "error": "<message>"}

A malformed request is *never* fatal — the driver writes an error
frame and continues the loop.

## Comparator families and operations

Each family corresponds to a python-flint type. New consumers
register here when their per-library wiring HO lands (HO-21..HO-26).
The dispatch table below names every operation supported as of this
driver landing; consumer HOs may extend it.

### `fmpz_poly` (integer polynomial Z[x])

Request fields: ``a``, ``b`` are coefficient lists ascending in
degree (the same convention `Hex.DensePoly` uses in
`scripts/oracle/poly_flint.py`).

* ``add`` — returns ``a + b`` as a coefficient list.
* ``sub`` — returns ``a - b`` as a coefficient list.
* ``mul`` — returns ``a * b`` as a coefficient list.
* ``divmod`` — returns ``[q_coeffs, r_coeffs]`` with ``q * b + r = a``,
  ``deg r < deg b``. Raises ``"divisor is zero"`` if ``b`` is the
  zero polynomial. Note FLINT's ``fmpz_poly`` ``divmod`` succeeds
  only when integer quotient/remainder is well-defined; failures
  surface as the driver error frame.
* ``gcd`` — returns ``gcd(a, b)`` as a coefficient list (FLINT's
  primitive-part normal form). The trivial-zero case returns
  ``[]``.
* ``derivative`` — returns the formal derivative of ``a`` as a
  coefficient list.
* ``compose`` — returns ``a(b)`` as a coefficient list (Horner-style
  composition under the python-flint ``__call__``).
* ``content`` — returns the integer GCD of the coefficients of ``a``
  (FLINT's signed normalisation; zero polynomial returns ``0``).
* ``primitive_part`` — returns ``a // content(a)`` as a coefficient
  list (FLINT's primitive-part normal form). The zero polynomial
  returns ``[]``.

### `nmod_poly` (F_p[x] for prime p that fits in a word)

Request fields: ``p`` (modulus), ``a``, ``b`` (coefficient lists).

* ``add``, ``mul``, ``divmod``, ``gcd`` — same shape as `fmpz_poly`,
  result coefficients reduced modulo ``p``.
* ``is_irreducible`` — returns the boolean: is ``a`` irreducible in
  ``F_p[x]``? Computed via ``flint.nmod_poly.factor()``: ``a`` is
  irreducible iff the factorisation has exactly one factor with
  multiplicity 1 of the same degree as ``a``.
* ``factor_distinct_deg`` — returns the distinct-degree
  factorisation as ``[[d, group_coeffs], ...]``, where each
  ``group_coeffs`` is the product of all degree-``d`` monic
  irreducible factors of ``a`` (the standard ``g_d = gcd(f_d,
  x^(p^d) - x)`` schema, see `scripts/oracle/berlekamp_flint.py`
  for the conformance-mode equivalent).

### `fmpz_mat` (integer matrix)

Request fields: ``rows`` (list of list of int).

* ``det`` — returns the determinant as an integer. Computed via
  ``flint.fmpz_mat(rows).det()`` (FLINT's multimodular-CRT
  determinant).

### `fq_default` (finite field F_q = F_p[x] / m(x))

Request fields: ``p`` (prime), ``modulus`` (coefficient list of the
defining polynomial ``m(x)`` in ascending degree), ``a``, ``b``
(reduced operands as coefficient lists).

* ``add`` — returns ``(a + b) mod m`` as a coefficient list
  (ascending, trimmed of trailing zeros).
* ``sub`` — returns ``(a - b) mod m`` as a coefficient list.
* ``neg`` — returns ``(-a) mod m`` as a coefficient list.
* ``mul`` — returns ``(a * b) mod m`` as a coefficient list.
* ``reduce`` — interpret ``a`` as an unreduced polynomial (not
  required to satisfy ``deg a < deg m``) and return ``a mod m`` as
  a coefficient list.
* ``inv`` — returns ``a^-1`` as a coefficient list.
* ``div`` — returns ``a / b`` as a coefficient list.
* ``pow`` — returns ``a^exponent`` as a coefficient list. The
  exponent may be negative when ``a`` is nonzero.

### `nmod_poly_hensel` (Hensel-lift kernels over Z_{p^k}[x])

Request fields: ``p`` (prime), ``k`` (current exponent, so the input
factorisation is mod ``p^k``), ``f`` (target polynomial coeffs over
Z), ``g``, ``h`` (factor pair coeffs at level ``p^k``), and for the
lift call optionally ``s``, ``t`` (Bezout coefficients satisfying
``s*g + t*h ≡ 1 (mod p)``).

* ``lift_once`` — single Zassenhaus quadratic step: lifts the
  factorisation ``f ≡ g*h (mod p^k)`` to ``f ≡ G*H (mod p^{2k})``.
  Returns ``{"G": [...], "H": [...]}`` (coefficient lists over Z,
  reduced into the centred range ``(-p^{2k}/2, p^{2k}/2]`` for
  stability).
* ``lift`` — iterate ``lift_once`` until the modulus exceeds
  ``2 * Mignotte_bound(f)`` (caller supplies ``target_k`` to fix
  the iteration count instead). Returns the final ``{"G", "H",
  "k"}``.

Hensel lift is implemented in python via `fmpz_poly` arithmetic
because python-flint does not expose
`nmod_poly_hensel_lift_*` C entry points directly; the algorithmic
schema is the textbook Newton-style quadratic lift. HO-24 owns
the Hensel-family wiring on the Lean side and may extend the
operation set here as its bench targets require.

## Per-call overhead

The driver imports ``flint`` once at startup; per-call cost in the
steady state is JSON decode + dispatch + python-flint call + JSON
encode. Measured per-call overhead is recorded in each consuming
library's headline report (one figure per library is enough since
the driver shape is identical across consumers); see HO-21..HO-26
for the per-library write-ups. The shared smoke test
``python3 scripts/oracle/flint_bench_driver.py < smoke.txt`` is
documented at the bottom of this file.

## Stdlib only, plus python-flint

Like the other ``scripts/oracle/*.py`` drivers, this script depends
only on the python stdlib and ``python-flint``. The ``flint``
import is local-to-startup (not lazy) so the first request does
not pay an import cost.
"""
from __future__ import annotations

import json
import sys
import traceback
from typing import Any, Callable

# Import flint at startup so the first request does not pay the
# `import flint` cost. The CI workflow installs python-flint at the
# top of `conformance.yml`; if it is unavailable the driver still
# starts but every request that needs flint will reply with an
# error frame.
try:
    import flint  # type: ignore[import-not-found]
    _flint_import_error: str | None = None
except Exception as exc:  # pragma: no cover - defensive
    flint = None  # type: ignore[assignment]
    _flint_import_error = f"python-flint not available: {exc!r}"


def _trim_zeros(coeffs: list[int]) -> list[int]:
    """Drop trailing zeros to match Lean's normalised
    coefficient-list representation."""
    out = [int(c) for c in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return out


def _require_flint() -> None:
    if flint is None:
        raise RuntimeError(_flint_import_error or "python-flint unavailable")


# ---------------------------------------------------------------------
# `fmpz_poly` (Z[x])
# ---------------------------------------------------------------------


def _fmpz_poly(coeffs: list[int]):
    return flint.fmpz_poly([int(c) for c in coeffs])  # type: ignore[union-attr]


def _fmpz_poly_coeffs(p) -> list[int]:
    return _trim_zeros([int(c) for c in p.coeffs()])


def _fmpz_poly_add(req: dict[str, Any]) -> list[int]:
    return _fmpz_poly_coeffs(_fmpz_poly(req["a"]) + _fmpz_poly(req["b"]))


def _fmpz_poly_sub(req: dict[str, Any]) -> list[int]:
    return _fmpz_poly_coeffs(_fmpz_poly(req["a"]) - _fmpz_poly(req["b"]))


def _fmpz_poly_mul(req: dict[str, Any]) -> list[int]:
    return _fmpz_poly_coeffs(_fmpz_poly(req["a"]) * _fmpz_poly(req["b"]))


def _fmpz_poly_divmod(req: dict[str, Any]) -> list[list[int]]:
    a = _fmpz_poly(req["a"])
    b = _fmpz_poly(req["b"])
    if b.degree() < 0:
        raise ValueError("divisor is zero")
    q, r = divmod(a, b)
    return [_fmpz_poly_coeffs(q), _fmpz_poly_coeffs(r)]


def _fmpz_poly_gcd(req: dict[str, Any]) -> list[int]:
    a = _fmpz_poly(req["a"])
    b = _fmpz_poly(req["b"])
    return _fmpz_poly_coeffs(a.gcd(b))


def _fmpz_poly_derivative(req: dict[str, Any]) -> list[int]:
    return _fmpz_poly_coeffs(_fmpz_poly(req["a"]).derivative())


def _fmpz_poly_compose(req: dict[str, Any]) -> list[int]:
    a = _fmpz_poly(req["a"])
    b = _fmpz_poly(req["b"])
    return _fmpz_poly_coeffs(a(b))


def _fmpz_poly_content(req: dict[str, Any]) -> int:
    return int(_fmpz_poly(req["a"]).content())


def _fmpz_poly_primitive_part(req: dict[str, Any]) -> list[int]:
    a = _fmpz_poly(req["a"])
    if a.degree() < 0:
        return []
    c = int(a.content())
    if c == 0:
        return []
    return _fmpz_poly_coeffs(a // flint.fmpz_poly([c]))  # type: ignore[union-attr]


_FMPZ_POLY_OPS: dict[str, Callable[[dict[str, Any]], Any]] = {
    "add": _fmpz_poly_add,
    "sub": _fmpz_poly_sub,
    "mul": _fmpz_poly_mul,
    "divmod": _fmpz_poly_divmod,
    "gcd": _fmpz_poly_gcd,
    "derivative": _fmpz_poly_derivative,
    "compose": _fmpz_poly_compose,
    "content": _fmpz_poly_content,
    "primitive_part": _fmpz_poly_primitive_part,
}


# ---------------------------------------------------------------------
# `nmod_poly` (F_p[x])
# ---------------------------------------------------------------------


def _nmod_poly(coeffs: list[int], p: int):
    return flint.nmod_poly([int(c) for c in coeffs], int(p))  # type: ignore[union-attr]


def _nmod_poly_coeffs(p) -> list[int]:
    return _trim_zeros([int(c) for c in p.coeffs()])


def _nmod_poly_add(req: dict[str, Any]) -> list[int]:
    p = int(req["p"])
    return _nmod_poly_coeffs(_nmod_poly(req["a"], p) + _nmod_poly(req["b"], p))


def _nmod_poly_mul(req: dict[str, Any]) -> list[int]:
    p = int(req["p"])
    return _nmod_poly_coeffs(_nmod_poly(req["a"], p) * _nmod_poly(req["b"], p))


def _nmod_poly_divmod(req: dict[str, Any]) -> list[list[int]]:
    p = int(req["p"])
    a = _nmod_poly(req["a"], p)
    b = _nmod_poly(req["b"], p)
    if b.degree() < 0:
        raise ValueError("divisor is zero")
    q, r = divmod(a, b)
    return [_nmod_poly_coeffs(q), _nmod_poly_coeffs(r)]


def _nmod_poly_gcd(req: dict[str, Any]) -> list[int]:
    p = int(req["p"])
    return _nmod_poly_coeffs(_nmod_poly(req["a"], p).gcd(_nmod_poly(req["b"], p)))


def _nmod_poly_is_irreducible(req: dict[str, Any]) -> bool:
    p = int(req["p"])
    a = _nmod_poly(req["a"], p)
    if a.degree() <= 0:
        return False
    _, factors = a.factor()
    if len(factors) != 1:
        return False
    factor, multiplicity = factors[0]
    return int(multiplicity) == 1 and factor.degree() == a.degree()


def _nmod_poly_factor_distinct_deg(req: dict[str, Any]) -> list[list]:
    """Distinct-degree factorisation of a non-zero ``nmod_poly``.

    Returns ``[[d, group_coeffs], ...]`` with one entry per non-trivial
    distinct-degree component. ``group_coeffs`` is the product of all
    monic degree-``d`` irreducible factors of ``a``, as a coefficient
    list. Implemented via the textbook schema ``g_d = gcd(f_d,
    x^(p^d) - x)`` followed by repeated division.
    """
    p = int(req["p"])
    a = _nmod_poly(req["a"], p)
    if a.degree() <= 0:
        return []
    # Make `cur` monic so the returned groups are monic.
    lc = int(a.leading_coefficient())
    if lc != 1:
        inv = pow(lc, -1, p)
        a = a * _nmod_poly([inv], p)
    cur = a
    x = _nmod_poly([0, 1], p)
    h = x
    out: list[list] = []
    d = 1
    while cur.degree() >= 2 * d:
        h = h.pow_mod(p, cur)
        g = cur.gcd(h - x)
        if g.degree() > 0:
            out.append([d, _nmod_poly_coeffs(g)])
            q, _ = divmod(cur, g)
            cur = q
        d += 1
    if cur.degree() > 0:
        out.append([cur.degree(), _nmod_poly_coeffs(cur)])
    return out


_NMOD_POLY_OPS: dict[str, Callable[[dict[str, Any]], Any]] = {
    "add": _nmod_poly_add,
    "mul": _nmod_poly_mul,
    "divmod": _nmod_poly_divmod,
    "gcd": _nmod_poly_gcd,
    "is_irreducible": _nmod_poly_is_irreducible,
    "factor_distinct_deg": _nmod_poly_factor_distinct_deg,
}


# ---------------------------------------------------------------------
# `fmpz_mat` (integer matrix)
# ---------------------------------------------------------------------


def _fmpz_mat_det(req: dict[str, Any]) -> int:
    rows = req["rows"]
    m = flint.fmpz_mat([[int(c) for c in r] for r in rows])  # type: ignore[union-attr]
    return int(m.det())


_FMPZ_MAT_OPS: dict[str, Callable[[dict[str, Any]], Any]] = {
    "det": _fmpz_mat_det,
}


# ---------------------------------------------------------------------
# `fq_default` (F_p[x] / m(x))
# ---------------------------------------------------------------------


def _fq_default_ctx(p: int, modulus_coeffs: list[int]):
    poly_ctx = flint.fmpz_mod_poly_ctx(int(p))  # type: ignore[union-attr]
    modulus = poly_ctx([int(c) for c in modulus_coeffs])
    return flint.fq_default_ctx(modulus=modulus)  # type: ignore[union-attr]


def _fq_default_element_coeffs(elem) -> list[int]:
    return _trim_zeros([int(c) for c in elem.polynomial().coeffs()])


def _fq_default_add(req: dict[str, Any]) -> list[int]:
    ctx = _fq_default_ctx(int(req["p"]), req["modulus"])
    return _fq_default_element_coeffs(ctx(req["a"]) + ctx(req["b"]))


def _fq_default_sub(req: dict[str, Any]) -> list[int]:
    ctx = _fq_default_ctx(int(req["p"]), req["modulus"])
    return _fq_default_element_coeffs(ctx(req["a"]) - ctx(req["b"]))


def _fq_default_neg(req: dict[str, Any]) -> list[int]:
    ctx = _fq_default_ctx(int(req["p"]), req["modulus"])
    return _fq_default_element_coeffs(-ctx(req["a"]))


def _fq_default_mul(req: dict[str, Any]) -> list[int]:
    ctx = _fq_default_ctx(int(req["p"]), req["modulus"])
    return _fq_default_element_coeffs(ctx(req["a"]) * ctx(req["b"]))


def _fq_default_reduce(req: dict[str, Any]) -> list[int]:
    ctx = _fq_default_ctx(int(req["p"]), req["modulus"])
    return _fq_default_element_coeffs(ctx(req["a"]))


def _fq_default_inv(req: dict[str, Any]) -> list[int]:
    ctx = _fq_default_ctx(int(req["p"]), req["modulus"])
    return _fq_default_element_coeffs(ctx(req["a"]) ** (-1))


def _fq_default_div(req: dict[str, Any]) -> list[int]:
    ctx = _fq_default_ctx(int(req["p"]), req["modulus"])
    return _fq_default_element_coeffs(ctx(req["a"]) / ctx(req["b"]))


def _fq_default_pow(req: dict[str, Any]) -> list[int]:
    ctx = _fq_default_ctx(int(req["p"]), req["modulus"])
    return _fq_default_element_coeffs(ctx(req["a"]) ** int(req["exponent"]))


_FQ_DEFAULT_OPS: dict[str, Callable[[dict[str, Any]], Any]] = {
    "add": _fq_default_add,
    "sub": _fq_default_sub,
    "neg": _fq_default_neg,
    "mul": _fq_default_mul,
    "reduce": _fq_default_reduce,
    "inv": _fq_default_inv,
    "div": _fq_default_div,
    "pow": _fq_default_pow,
}


# ---------------------------------------------------------------------
# `nmod_poly_hensel` (Hensel-lift kernels over Z_{p^k}[x])
# ---------------------------------------------------------------------


def _center_mod(c: int, modulus: int) -> int:
    """Reduce ``c`` into the centred range ``(-modulus/2, modulus/2]``."""
    r = c % modulus
    if r > modulus // 2:
        r -= modulus
    return r


def _fmpz_poly_center_mod(p, modulus: int) -> list[int]:
    return _trim_zeros([_center_mod(int(c), modulus) for c in p.coeffs()])


def _fmpz_poly_reduce_mod_pk(p, modulus: int):
    """Return ``p mod modulus`` as an ``fmpz_poly`` in centred
    representatives (so subsequent arithmetic stays small)."""
    return flint.fmpz_poly(  # type: ignore[union-attr]
        [_center_mod(int(c), modulus) for c in p.coeffs()]
    )


def _bezout_mod_p(g, h, p: int) -> tuple[Any, Any]:
    """Bezout coefficients ``s, t`` with ``s*g + t*h ≡ 1 (mod p)``.

    ``g, h`` are passed as ``fmpz_poly``; returned ``s, t`` are
    ``fmpz_poly`` in centred mod-p representatives. Raises if
    ``gcd(g, h) ≠ 1`` over ``F_p[x]``.
    """
    gp = _nmod_poly([int(c) for c in g.coeffs()], p)
    hp = _nmod_poly([int(c) for c in h.coeffs()], p)
    d, sp, tp = gp.xgcd(hp)
    if d != _nmod_poly([1], p):
        raise ValueError("Bezout precondition failed: gcd(g, h) ≠ 1 mod p")
    s = flint.fmpz_poly(  # type: ignore[union-attr]
        [_center_mod(int(c), p) for c in sp.coeffs()]
    )
    t = flint.fmpz_poly(  # type: ignore[union-attr]
        [_center_mod(int(c), p) for c in tp.coeffs()]
    )
    return s, t


def _hensel_step(f, g, h, s, t, p_k: int) -> tuple[Any, Any, Any, Any]:
    """One Zassenhaus quadratic lift step.

    Given the invariant
        ``f ≡ g*h (mod p_k)``, ``s*g + t*h ≡ 1 (mod p_k)``,
    returns ``(G, H, S, T)`` satisfying
        ``f ≡ G*H (mod p_k^2)``, ``S*G + T*H ≡ 1 (mod p_k^2)``,
    with ``G ≡ g``, ``H ≡ h``, ``S ≡ s``, ``T ≡ t`` (all mod p_k).
    """
    p_k2 = p_k * p_k
    # Factor lift
    e = f - g * h
    er = _fmpz_poly_reduce_mod_pk(e, p_k2)
    q, r = divmod(s * er, h)
    # Reduce intermediates aggressively so coefficients stay bounded.
    G = _fmpz_poly_reduce_mod_pk(g + t * er + q * g, p_k2)
    H = _fmpz_poly_reduce_mod_pk(h + r, p_k2)
    # Bezout lift
    b = s * G + t * H - flint.fmpz_poly([1])  # type: ignore[union-attr]
    br = _fmpz_poly_reduce_mod_pk(b, p_k2)
    qb, rb = divmod(s * br, H)
    S = _fmpz_poly_reduce_mod_pk(s - rb, p_k2)
    T = _fmpz_poly_reduce_mod_pk(t - t * br - qb * G, p_k2)
    return G, H, S, T


def _hensel_lift_once(req: dict[str, Any]) -> dict[str, list[int]]:
    p = int(req["p"])
    k = int(req["k"])
    f = _fmpz_poly(req["f"])
    g = _fmpz_poly(req["g"])
    h = _fmpz_poly(req["h"])
    p_k = p ** k
    if "s" in req and "t" in req:
        s = _fmpz_poly(req["s"])
        t = _fmpz_poly(req["t"])
    else:
        s, t = _bezout_mod_p(g, h, p)
    G, H, _, _ = _hensel_step(f, g, h, s, t, p_k)
    return {"G": _fmpz_poly_center_mod(G, p_k * p_k),
            "H": _fmpz_poly_center_mod(H, p_k * p_k)}


def _hensel_lift(req: dict[str, Any]) -> dict[str, Any]:
    """Iterate ``_hensel_step`` until ``target_k`` is reached.

    Each iteration doubles the exponent (Newton-style quadratic
    convergence), so the iteration count is ``ceil(log2(target_k /
    k))``.
    """
    p = int(req["p"])
    k = int(req["k"])
    target_k = int(req["target_k"])
    if target_k < k:
        raise ValueError(f"target_k ({target_k}) must be ≥ k ({k})")
    f = _fmpz_poly(req["f"])
    g = _fmpz_poly(req["g"])
    h = _fmpz_poly(req["h"])
    if "s" in req and "t" in req:
        s = _fmpz_poly(req["s"])
        t = _fmpz_poly(req["t"])
    else:
        s, t = _bezout_mod_p(g, h, p)
    cur_k = k
    while cur_k < target_k:
        p_k = p ** cur_k
        g, h, s, t = _hensel_step(f, g, h, s, t, p_k)
        cur_k = min(2 * cur_k, target_k)
    final_mod = p ** cur_k
    return {
        "G": _fmpz_poly_center_mod(g, final_mod),
        "H": _fmpz_poly_center_mod(h, final_mod),
        "k": cur_k,
    }


_NMOD_POLY_HENSEL_OPS: dict[str, Callable[[dict[str, Any]], Any]] = {
    "lift_once": _hensel_lift_once,
    "lift": _hensel_lift,
}


# ---------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------


_FAMILIES: dict[str, dict[str, Callable[[dict[str, Any]], Any]]] = {
    "fmpz_poly": _FMPZ_POLY_OPS,
    "nmod_poly": _NMOD_POLY_OPS,
    "fmpz_mat": _FMPZ_MAT_OPS,
    "fq_default": _FQ_DEFAULT_OPS,
    "nmod_poly_hensel": _NMOD_POLY_HENSEL_OPS,
}


def _dispatch(req: dict[str, Any]) -> Any:
    family = req.get("family")
    op = req.get("op")
    if not isinstance(family, str):
        raise ValueError("request missing string 'family' field")
    if not isinstance(op, str):
        raise ValueError("request missing string 'op' field")
    ops = _FAMILIES.get(family)
    if ops is None:
        raise ValueError(f"unknown family {family!r}; known: {sorted(_FAMILIES)}")
    handler = ops.get(op)
    if handler is None:
        raise ValueError(
            f"unknown op {op!r} for family {family!r}; known: {sorted(ops)}"
        )
    _require_flint()
    return handler(req)


def _serve(stdin, stdout) -> None:
    for raw in stdin:
        line = raw.rstrip("\n")
        if not line:
            # Allow blank-line sentinel as a no-op for tooling that
            # injects newlines. Don't emit a reply for these (the
            # consumer is not expecting one).
            continue
        try:
            req = json.loads(line)
            if not isinstance(req, dict):
                raise ValueError(f"top-level JSON must be an object, got {type(req).__name__}")
            result = _dispatch(req)
            reply: dict[str, Any] = {"ok": True, "result": result}
        except Exception as exc:
            # Include the exception type for debuggability without
            # spilling the traceback into the protocol stream.
            reply = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}
        try:
            stdout.write(json.dumps(reply, separators=(",", ":")) + "\n")
            stdout.flush()
        except BrokenPipeError:  # pragma: no cover - consumer hung up
            return


# Smoke-test invocation::
#
#   printf '%s\n' \\
#       '{"family":"fmpz_poly","op":"mul","a":[1,2,3],"b":[4,5]}' \\
#       '{"family":"nmod_poly","op":"is_irreducible","p":7,"a":[1,1,1]}' \\
#       '{"family":"fmpz_mat","op":"det","rows":[[1,2],[3,4]]}' \\
#       | python3 scripts/oracle/flint_bench_driver.py
#
# Expected replies (one per request, in order)::
#
#   {"ok":true,"result":[4,13,22,15]}
#   {"ok":true,"result":true}
#   {"ok":true,"result":-2}
#
# Malformed requests are echoed back as `{"ok":false,"error":"..."}`
# and never terminate the driver.


def main() -> int:
    _serve(sys.stdin, sys.stdout)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:  # pragma: no cover
        sys.exit(130)
    except BrokenPipeError:  # pragma: no cover
        sys.exit(0)
    except Exception:  # pragma: no cover - defensive
        traceback.print_exc()
        sys.exit(1)
