#!/usr/bin/env python3
"""Exact carrier oracle and persistent benchmark service for matrix libraries.

Each library owns a disjoint record kind in HANDLERS. A Bareiss record contains carrier,
arity, p, n, rows and the complete canonical result. Rational coefficients are
reduced [numerator, positive denominator] pairs; dense polynomials use ascending
coefficient arrays (zero is []); sparse terms are [exponents, coefficient] pairs
in increasing grevlex order. Modular coefficients are in [0, p).

The bareiss_carrier arm uses python-flint for scalars and SymPy Berkowitz
for polynomials. The det arm retains the determinant stream's Codec and
DomainMatrix.det (Bareiss in pinned SymPy), independently of Hex Leibniz.
The charpoly_carrier arm uses DomainMatrix.det on fresh tI-A. All three
compare exact canonical coefficients without a simplifier. --serve retains
the characteristic-polynomial persistent protocol (op=noop returns []).
Pass a JSONL path or read stdin. --server accepts the same records without the
result field and returns one {ok, result} reply per line. The overhead kind is
a trivial request for measuring persistent framing/dispatch overhead.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from functools import lru_cache

from flint import __version__ as flint_version, fmpq, fmpq_mat, nmod_mat
from sympy import __version__ as sympy_version, GF, QQ, ZZ, Matrix, Poly, Rational, symbols, isprime
from sympy.polys.matrices import DomainMatrix

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from common import FixtureError, assert_equal, read_fixtures


def integer(x):
    if type(x) is not int:
        raise ValueError(f"expected integer, got {x!r}")
    return x


def grevlex(exponents):
    return (sum(exponents), *(-e for e in reversed(exponents)))


class Carrier:
    """Decode and encode exactly one canonical coefficient domain."""

    def __init__(self, record):
        self.name = record["carrier"]
        if self.name not in {"rat", "mod", "dense_rat", "dense_mod", "zpoly", "mv_int", "mv_rat"}:
            raise ValueError(f"unknown carrier {self.name!r}")
        self.modular = self.name in {"mod", "dense_mod"}
        self.rational = self.name in {"rat", "dense_rat", "mv_rat"}
        self.scalar = self.name in {"rat", "mod"}
        self.dense = self.name in {"dense_rat", "dense_mod", "zpoly"}
        self.p = integer(record["p"])
        self.arity = integer(record["arity"])
        if self.arity != (0 if self.scalar else 1 if self.dense else self.arity) or self.arity < 0:
            raise ValueError("wrong carrier arity")
        if not self.scalar and self.arity == 0:
            raise ValueError("polynomial carrier requires variables")
        if self.modular:
            from sympy import isprime
            if not 2 <= self.p < 2**31 or not isprime(self.p):
                raise ValueError("modulus must be prime and below 2^31")
        self.domain = GF(self.p, symmetric=False) if self.modular else QQ if self.rational else ZZ
        self.xs = symbols(f"x0:{self.arity}")

    def coefficient(self, value):
        if self.rational:
            if not isinstance(value, list) or len(value) != 2:
                raise ValueError("rational must be [numerator, denominator]")
            num, den = map(integer, value)
            if den <= 0 or math.gcd(num, den) != 1:
                raise ValueError("noncanonical rational")
            return Rational(num, den)
        value = integer(value)
        if self.modular and not 0 <= value < self.p:
            raise ValueError("noncanonical residue")
        return value

    def encode_coefficient(self, value):
        if self.rational:
            q = Rational(value)
            return [int(q.p), int(q.q)]
        return int(value) % self.p if self.modular else int(value)

    def decode(self, value):
        if self.scalar:
            return self.coefficient(value)
        if not isinstance(value, list):
            raise ValueError("polynomial must be an array")
        if self.dense:
            coeffs = [self.coefficient(c) for c in value]
            if coeffs and coeffs[-1] == 0:
                raise ValueError("trailing zero in dense polynomial")
            terms = {(i,): c for i, c in enumerate(coeffs) if c != 0}
        else:
            terms = {}
            previous = None
            for term in value:
                if not isinstance(term, list) or len(term) != 2:
                    raise ValueError("sparse term must be [exponents, coefficient]")
                exponents, coefficient = term
                if not isinstance(exponents, list) or len(exponents) != self.arity:
                    raise ValueError("wrong exponent-vector arity")
                exponents = tuple(map(integer, exponents))
                if min(exponents) < 0:
                    raise ValueError("negative exponent")
                key = grevlex(exponents)
                if previous is not None and key <= previous:
                    raise ValueError("terms must be unique and in increasing grevlex order")
                previous = key
                c = self.coefficient(coefficient)
                if c == 0:
                    raise ValueError("zero sparse coefficient")
                terms[exponents] = c
        return Poly.from_dict(terms, self.xs, domain=self.domain).as_expr()

    def encode(self, value):
        if self.scalar:
            return self.encode_coefficient(value)
        poly = Poly(value, *self.xs, domain=self.domain)
        if poly.is_zero:
            return []
        if self.dense:
            return [self.encode_coefficient(poly.nth(i)) for i in range(poly.degree() + 1)]
        return [[list(exps), self.encode_coefficient(c)]
                for exps, c in sorted(poly.terms(), key=lambda t: grevlex(t[0]))]


def bareiss(record):
    carrier = Carrier(record)
    n = integer(record["n"])
    rows = record["rows"]
    if n < 0 or not isinstance(rows, list) or len(rows) != n or any(
            not isinstance(row, list) or len(row) != n for row in rows):
        raise ValueError("expected square matrix matching n")
    entries = [carrier.decode(c) for row in rows for c in row]
    if carrier.name == "rat":
        result = fmpq_mat(n, n, [fmpq(int(q.p), int(q.q)) for q in entries]).det()
        return [int(result.numerator), int(result.denominator)]
    if carrier.name == "mod":
        return int(nmod_mat(n, n, entries, carrier.p).det())
    return carrier.encode(Matrix(n, n, entries).det(method="berkowitz"))


@lru_cache(None)
def context(carrier, base, arity, modulus):
    if base == "ZZ" and modulus == 0:
        ground = ZZ
    elif base == "QQ" and modulus == 0:
        ground = QQ
    elif base == "GF" and isprime(modulus) and modulus < 2**31:
        ground = GF(modulus, symmetric=False)
    else:
        raise ValueError(f"unsupported base domain: {base}/{modulus}")
    if carrier == "ratfn" and base == "QQ" and arity == 1:
        domain = ground.frac_field("x")
        ring = domain.field.ring
    elif carrier == "dense" and arity == 1:
        domain = ground.poly_ring("x")
        ring = domain.ring
    elif carrier == "mv" and arity in (2, 3) and base in ("ZZ", "QQ"):
        domain = ground.poly_ring(*(f"x{i}" for i in range(arity)))
        ring = domain.ring
    else:
        raise ValueError(f"unsupported carrier: {carrier}/{base}/{arity}")
    return ground, domain, ring


class Codec:
    def __init__(self, record):
        self.carrier = record["carrier"]
        self.base = record["base"]
        self.arity = record["arity"]
        self.modulus = record["modulus"]
        self.ground, self.domain, self.ring = context(
            self.carrier, self.base, self.arity, self.modulus)

    def scalar(self, value):
        if self.base == "QQ":
            if not isinstance(value, list) or len(value) != 2 or any(type(x) is not int for x in value):
                raise ValueError("rational coefficient must be an integer numerator/denominator pair")
            if value[1] <= 0:
                raise ValueError("rational denominator must be positive")
            result = self.ground(*value)
        else:
            if type(value) is not int:
                raise ValueError("coefficient must be an integer")
            result = self.ground(value)
        if self.encode_scalar(result) != value:
            raise ValueError("noncanonical scalar")
        return result

    def encode_scalar(self, value):
        if self.base == "QQ":
            return [int(value.numerator), int(value.denominator)]
        return int(value) % self.modulus if self.base == "GF" else int(value)

    def poly(self, values):
        if not isinstance(values, list):
            raise ValueError("polynomial must be an array")
        if self.carrier == "mv":
            terms = {}
            for exponents, coeff in values:
                if len(exponents) != self.arity or any(type(e) is not int or e < 0 for e in exponents):
                    raise ValueError("invalid exponent vector")
                if tuple(exponents) in terms:
                    raise ValueError("duplicate monomial")
                terms[tuple(exponents)] = self.scalar(coeff)
        else:
            terms = {(i,): self.scalar(c) for i, c in enumerate(values)}
        result = self.ring.from_dict(terms)
        if self.encode_poly(result) != values:
            raise ValueError("noncanonical polynomial (zero terms, trailing zeros, or term order)")
        return result

    def encode_poly(self, poly):
        if self.carrier == "mv":
            # Ascending grevlex: total degree, then reversed negative exponents.
            terms = sorted(poly.items(), key=lambda t: (sum(t[0]), tuple(-e for e in reversed(t[0]))))
            return [[list(m), self.encode_scalar(c)] for m, c in terms if c]
        return [self.encode_scalar(poly.get((i,), self.ground.zero))
                for i in range(int(poly.degree()) + 1)] if poly else []

    def decode(self, value):
        if self.carrier != "ratfn":
            return self.poly(value)
        if set(value) != {"num", "den"}:
            raise ValueError("fraction requires num and den")
        num, den = self.poly(value["num"]), self.poly(value["den"])
        if not den:
            raise ValueError("zero fraction denominator")
        result = self.domain.field.new(num, den)
        if self.encode(result) != value:
            raise ValueError("fraction is not reduced with monic denominator")
        return result

    def encode(self, value):
        if self.carrier != "ratfn":
            return self.encode_poly(value)
        leading = value.denom.LC
        return {"num": self.encode_poly(value.numer.quo_ground(leading)),
                "den": self.encode_poly(value.denom.quo_ground(leading))}


def prepare(record):
    codec = Codec(record)
    n, rows = record["n"], record["matrix"]
    if type(n) is not int or n < 0 or len(rows) != n or any(len(row) != n for row in rows):
        raise ValueError("matrix shape does not match dimension")
    matrix = DomainMatrix([[codec.decode(x) for x in row] for row in rows], (n, n), codec.domain)
    return codec, matrix


def determinant(record):
    codec, matrix = prepare(record)
    return codec.encode(matrix_det(matrix.to_list(), codec.domain))


def carrier_domain(record):
    from sympy import GF, QQ, ZZ
    carrier = record["carrier"]
    if carrier not in {"dense_int", "dense_rat", "dense_mod", "mv_int", "mv_rat", "rat_fn"}:
        raise ValueError(f"unknown carrier {carrier}")
    scalar = (GF(record["modulus"], symmetric=False) if carrier == "dense_mod"
              else QQ if carrier.endswith("rat") or carrier == "rat_fn" else ZZ)
    variables = tuple(f"x{i}" for i in range(record["arity"])) if carrier.startswith("mv_") else ("x",)
    return scalar, (scalar.frac_field(*variables) if carrier == "rat_fn"
                    else scalar.poly_ring(*variables))


def scalar_decode(value, domain):
    return domain(*value) if isinstance(value, list) else domain(value)


def scalar_encode(value, domain):
    if domain.is_QQ:
        return [int(domain.numer(value)), int(domain.denom(value))]
    return int(value) % int(domain.mod) if domain.is_FF else int(value)


def dense_decode(value, domain):
    return domain.ring.from_dict({(i,): scalar_decode(c, domain.domain)
                                 for i, c in enumerate(value) if c != 0})


def dense_encode(value, domain):
    degree = int(value.degree()) if value else -1
    return [scalar_encode(value.get((i,), domain.domain.zero), domain.domain)
            for i in range(degree + 1)]


def decode(value, record, scalar, domain):
    carrier = record["carrier"]
    if carrier == "rat_fn":
        ring = scalar.poly_ring("x")
        numerator = dense_decode(value["num"], ring)
        denominator = dense_decode(value["den"], ring)
        if not denominator:
            raise ValueError("zero denominator")
        return domain(numerator) / domain(denominator)
    if carrier.startswith("mv_"):
        return domain.ring.from_dict({tuple(m): scalar_decode(c, scalar) for m, c in value})
    return dense_decode(value, domain)


def encode(value, record, scalar, domain):
    carrier = record["carrier"]
    if carrier == "rat_fn":
        ring = scalar.poly_ring("x")
        leading = value.denom.LC
        return {"num": dense_encode(value.numer / leading, ring),
                "den": dense_encode(value.denom / leading, ring)}
    if carrier.startswith("mv_"):
        def grevlex(term):
            m, _ = term
            return (sum(m), tuple(-e for e in reversed(m)))
        return [[list(m), scalar_encode(c, scalar)] for m, c in sorted(value.items(), key=grevlex)]
    return dense_encode(value, domain)


def matrix_det(rows, domain):
    """Dense DomainMatrix on a polynomial domain selects ddm_idet (Bareiss)."""
    from sympy.polys.matrices import DomainMatrix
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError("matrix must be square")
    return DomainMatrix(rows, (n, n), domain).det()


def charpoly(record):
    if record.get("schema") != 1 or record.get("kind") != "charpoly_carrier":
        raise ValueError("unsupported record kind or schema")
    if not isinstance(record.get("carrier"), str) or record["carrier"] not in {"dense_int", "dense_rat", "dense_mod", "mv_int", "mv_rat", "rat_fn"}:
        raise FixtureError("invalid coefficient carrier")
    arity = record.get("arity")
    if type(arity) is not int or arity < 1:
        raise FixtureError("carrier arity must be positive")
    if not record["carrier"].startswith("mv_") and arity != 1:
        raise FixtureError("univariate carrier must have arity one")
    modulus = record.get("modulus")
    if record["carrier"] == "dense_mod" and (type(modulus) is not int or modulus < 2):
        raise FixtureError("invalid carrier modulus")
    scalar, carrier = carrier_domain(record)
    rows = record["rows"]
    n = record["n"]
    if len(rows) != n or any(len(row) != n for row in rows):
        raise ValueError("matrix dimensions disagree")
    decoded = [[decode(c, record, scalar, carrier) for c in row] for row in rows]
    # Reject noncanonical inputs as well as noncanonical outputs.
    if [[encode(c, record, scalar, carrier) for c in row] for row in decoded] != rows:
        raise ValueError("noncanonical carrier input")
    domain = carrier.poly_ring("t")
    t = domain.gens[0]
    polynomial = matrix_det([[ (t if i == j else domain.zero) - domain(c)
                               for j, c in enumerate(row)] for i, row in enumerate(decoded)], domain)
    return [encode(polynomial.get((i,), carrier.zero), record, scalar, carrier)
            for i in range(n + 1)]


# Each library uses an independent algorithm and a disjoint record kind.
HANDLERS = {"det": determinant, "bareiss_carrier": bareiss, "charpoly_carrier": charpoly}


def dispatch(record):
    return HANDLERS[record["kind"]](record)


def evaluate(record):
    kind = record.get("kind")
    handler = HANDLERS.get(kind) if isinstance(kind, str) else None
    if handler is None:
        raise FixtureError(f"unsupported matrix carrier kind: {record.get('kind')!r}")
    return handler(record)


def serve():
    # Import once, before accepting timed requests.
    import sympy  # noqa: F401
    for line in sys.stdin:
        try:
            request = json.loads(line)
            result = [] if request.get("op") == "noop" else evaluate(request)
            reply = {"ok": True, "result": result}
        except Exception as exc:
            reply = {"ok": False, "error": str(exc)}
        print(json.dumps(reply, separators=(",", ":")), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", nargs="?", type=Path)
    parser.add_argument("--server", action="store_true")
    parser.add_argument("--serve", action="store_true")
    parser.add_argument("--failure-dir", type=Path)
    args = parser.parse_args()
    if args.serve:
        serve()
        return
    if args.server:
        stream = args.path.open() if args.path else sys.stdin
        try:
            for line in stream:
                try:
                    record = json.loads(line)
                    result = 0 if record["kind"] == "overhead" else dispatch(record)
                    reply = {"ok": True, "result": result}
                except Exception as exc:
                    reply = {"ok": False, "error": str(exc)}
                print(json.dumps(reply, separators=(",", ":")), flush=True)
        finally:
            if args.path:
                stream.close()
        return
    count = 0
    ids = set()
    for record in read_fixtures(args.path):
        key = tuple(record.get(k) for k in ("kind", "carrier", "base", "arity", "modulus", "case"))
        if key in ids:
            raise ValueError(f"duplicate fixture id: {key}")
        ids.add(key)
        result = dispatch(record)
        # Python equality alone accepts booleans as integers: validate the
        # complete claimed answer before comparing canonical coefficients.
        if record["kind"] == "det":
            expected = record["determinant"]
            Codec(record).decode(expected)
            library = "HexDeterminant"
        elif record["kind"] == "charpoly_carrier":
            expected = record["value"]
            scalar, domain = carrier_domain(record)
            canonical = [encode(decode(c, record, scalar, domain), record, scalar, domain)
                         for c in expected]
            # JSON comparison distinguishes booleans from integer coefficients.
            if json.dumps(canonical, sort_keys=True) != json.dumps(expected, sort_keys=True):
                raise ValueError("noncanonical characteristic-polynomial coefficient")
            library = record["lib"]
        else:
            expected = record["result"]
            Carrier(record).decode(expected)
            library = record["lib"]
        assert_equal(expected, result,
                     library=library, case_id=record["case"],
                     kind=record["kind"], input_record=record,
                     oracle_name="FLINT/SymPy exact matrix carriers",
                     oracle_version=f"flint {flint_version}; sympy {sympy_version}",
                     profile="core", seed=0, failure_dir=args.failure_dir)
        count += 1
    if not count:
        raise ValueError("empty fixture stream")
    print(f"OK: {count} exact matrix carrier records")


if __name__ == "__main__":
    main()
