"""Small test-only FLINT qqbar binding, including algebraic-coefficient roots.

python-flint 0.9.0 exposes scalar qqbar contexts through ``flint.types._gr``
but does not expose polynomial roots. This adapter uses the public C entry
points in that wheel's FLINT 3.6.0 library, without accessing Python object
internals. The three ctypes records follow the pinned ``gr_types.h`` and
``fmpz_types.h`` layouts:
https://github.com/flintlib/flint/blob/v3.6.0/src/gr_types.h

Every status is checked. A context manager owns all elements and clears them
before their contexts, including when a root operation raises an exception.
This is an oracle helper, never a dependency of the Lean libraries.
"""
from __future__ import annotations

import ctypes as C
from pathlib import Path
from fractions import Fraction
from typing import Any


class Unavailable(RuntimeError):
    """The pinned oracle or its required C capability is unavailable."""


class _Context(C.Structure):
    _fields_ = [
        ("data", C.c_byte * (6 * C.sizeof(C.c_ulong))),
        ("kind", C.c_ulong), ("element_size", C.c_long),
        ("methods", C.c_void_p), ("limit", C.c_ulong),
    ]


class _Vector(C.Structure):
    # Generic vectors, polynomials, and fmpz vectors have this layout.
    _fields_ = [("data", C.c_void_p), ("allocated", C.c_long), ("length", C.c_long)]


class QQBar:
    """Owned exact values in the wheel's real and complex qqbar contexts."""

    def __init__(self) -> None:
        try:
            import flint
        except ImportError as exc:
            raise Unavailable("python-flint 0.9.0 is required") from exc
        if (flint.__version__, flint.__FLINT_VERSION__) != ("0.9.0", "3.6.0"):
            raise Unavailable("supported oracle is python-flint 0.9.0 / FLINT 3.6.0")
        if C.sizeof(C.c_long) != 8 or C.sizeof(C.c_void_p) != 8:
            raise Unavailable("qqbar adapter requires the pinned 64-bit LP64 wheel ABI")
        directory = Path(flint.__file__).resolve().parent.parent / "python_flint.libs"
        libraries = list(directory.glob("libflint*.so*"))
        if len(libraries) != 1:
            raise Unavailable("cannot locate the pinned wheel's unique FLINT shared library")
        self.lib = C.CDLL(str(libraries[0]))
        self.owned: list[tuple[int, _Context]] = []
        self.contexts: list[_Context] = []
        self.closed = False
        ptr, integer, signed = C.c_void_p, C.c_int, C.c_long
        signatures: dict[str, tuple[Any, list[Any]]] = {
            "gr_ctx_init_real_qqbar": (None, [ptr]),
            "gr_ctx_init_complex_qqbar": (None, [ptr]),
            "gr_ctx_init_fmpz": (None, [ptr]), "gr_ctx_clear": (None, [ptr]),
            "gr_heap_init": (ptr, [ptr]), "gr_heap_clear": (None, [ptr, ptr]),
            "gr_set_str": (integer, [ptr, C.c_char_p, ptr]),
            "gr_set": (integer, [ptr, ptr, ptr]),
            "gr_set_other": (integer, [ptr, ptr, ptr, ptr]),
            "gr_cmp": (integer, [ptr, ptr, ptr, ptr]),
            "gr_poly_init": (None, [ptr, ptr]), "gr_poly_clear": (None, [ptr, ptr]),
            "gr_poly_set_coeff_scalar": (integer, [ptr, signed, ptr, ptr]),
            "gr_poly_roots": (integer, [ptr, ptr, ptr, integer, ptr]),
            "gr_poly_roots_other": (integer, [ptr, ptr, ptr, ptr, integer, ptr]),
            "gr_vec_init": (None, [ptr, signed, ptr]), "gr_vec_clear": (None, [ptr, ptr]),
            "fmpz_vec_init": (None, [ptr, signed]), "fmpz_vec_clear": (None, [ptr]),
            "fmpz_get_si": (signed, [ptr]), "qqbar_is_rational": (integer, [ptr]),
        }
        for name in ("neg", "inv", "sqrt", "floor", "ceil", "abs", "re", "im"):
            signatures[f"gr_{name}"] = (integer, [ptr, ptr, ptr])
        for name in ("add", "sub", "mul", "div"):
            signatures[f"gr_{name}"] = (integer, [ptr, ptr, ptr, ptr])
        try:
            for name, (result, args) in signatures.items():
                func = getattr(self.lib, name)
                func.restype, func.argtypes = result, args
        except AttributeError as exc:
            raise Unavailable(f"missing FLINT capability: {exc}") from exc
        for name in ("real_qqbar", "complex_qqbar", "fmpz"):
            ctx = _Context()
            getattr(self.lib, f"gr_ctx_init_{name}")(C.byref(ctx))
            self.contexts.append(ctx)
        self.real, self.complex, self.integer = self.contexts

    @staticmethod
    def check(status: int, operation: str) -> None:
        if status != 0:
            raise ArithmeticError(f"FLINT {operation} returned status {status}")

    def __enter__(self) -> QQBar:
        return self

    def __exit__(self, *_: Any) -> None:
        self.close()

    def close(self) -> None:
        if not self.closed:
            for value, ctx in reversed(self.owned):
                self.lib.gr_heap_clear(value, C.byref(ctx))
            for ctx in reversed(self.contexts):
                self.lib.gr_ctx_clear(C.byref(ctx))
            self.closed = True

    def allocate(self, ctx: _Context | None = None) -> int:
        ctx = self.real if ctx is None else ctx
        value = self.lib.gr_heap_init(C.byref(ctx))
        if not value:
            raise MemoryError("FLINT element allocation failed")
        self.owned.append((value, ctx))
        return value

    def number(self, value: str | int | Fraction, ctx: _Context | None = None) -> int:
        ctx = self.real if ctx is None else ctx
        result = self.allocate(ctx)
        self.check(self.lib.gr_set_str(result, str(value).encode("ascii"), C.byref(ctx)), "set_str")
        return result

    def unary(self, operation: str, value: int, ctx: _Context | None = None) -> int:
        ctx = self.real if ctx is None else ctx
        result = self.allocate(ctx)
        self.check(getattr(self.lib, f"gr_{operation}")(result, value, C.byref(ctx)), operation)
        return result

    def binary(self, operation: str, left: int, right: int) -> int:
        result = self.allocate()
        self.check(getattr(self.lib, f"gr_{operation}")(result, left, right, C.byref(self.real)), operation)
        return result

    def compare(self, left: int, right: int, ctx: _Context | None = None) -> int:
        ctx = self.real if ctx is None else ctx
        result = C.c_int()
        self.check(self.lib.gr_cmp(C.byref(result), left, right, C.byref(ctx)), "cmp")
        return result.value

    def to_real(self, value: int) -> int | None:
        result = self.allocate()
        status = self.lib.gr_set_other(result, value, C.byref(self.complex), C.byref(self.real))
        if status == 1:  # GR_DOMAIN: the complex value is nonreal.
            return None
        self.check(status, "complex-to-real conversion")
        return result

    def roots(self, coefficients: list[int], *, integer: bool = False,
              complex_output: bool = False) -> list[tuple[int, int]]:
        """Solve a polynomial of owned coefficient values; retain multiplicities.

        Integer coefficients use roots_other with an fmpz coefficient context.
        General real algebraic coefficients use gr_poly_roots directly.
        The zero polynomial is handled by the caller's universal-set convention.
        """
        output = self.complex if complex_output else self.real
        source = self.integer if integer else output
        poly, roots, mult = _Vector(), _Vector(), _Vector()
        self.lib.gr_poly_init(C.byref(poly), C.byref(source))
        self.lib.gr_vec_init(C.byref(roots), 0, C.byref(output))
        self.lib.fmpz_vec_init(C.byref(mult), 0)
        try:
            for index, value in enumerate(coefficients):
                self.check(self.lib.gr_poly_set_coeff_scalar(
                    C.byref(poly), index, value, C.byref(source)), "set_coeff")
            if integer:
                status = self.lib.gr_poly_roots_other(C.byref(roots), C.byref(mult),
                    C.byref(poly), C.byref(source), 0, C.byref(output))
            else:
                status = self.lib.gr_poly_roots(C.byref(roots), C.byref(mult),
                    C.byref(poly), 0, C.byref(output))
            self.check(status, "polynomial roots")
            if roots.length != mult.length:
                raise ArithmeticError("FLINT returned inconsistent root multiplicities")
            result = []
            for index in range(roots.length):
                value = self.allocate(output)
                self.check(self.lib.gr_set(value, roots.data + index * output.element_size,
                                          C.byref(output)), "copy root")
                multiplicity = self.lib.fmpz_get_si(mult.data + index * C.sizeof(C.c_long))
                if multiplicity <= 0:
                    raise ArithmeticError("FLINT returned a nonpositive multiplicity")
                result.append((value, multiplicity))
            return result
        finally:
            self.lib.gr_vec_clear(C.byref(roots), C.byref(output))
            self.lib.fmpz_vec_clear(C.byref(mult))
            self.lib.gr_poly_clear(C.byref(poly), C.byref(source))
