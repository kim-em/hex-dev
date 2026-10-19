#!/usr/bin/env python3
"""Independent qqbar checks for real fixed-field signs, reading the CI stream."""
import json
import sys
from sign_det_common_fields import check_scalar_data, Unavailable
from scripts.oracle.common import OracleMismatch

if __name__ == "__main__":
    try:
        raise SystemExit(check_scalar_data(json.load(sys.stdin)))
    except (OracleMismatch, Unavailable, OSError, ImportError, ValueError, KeyError, TypeError) as exc:
        print(f"FAIL HexSignDet field-sign oracle: {exc}", file=sys.stderr)
        raise SystemExit(1)
