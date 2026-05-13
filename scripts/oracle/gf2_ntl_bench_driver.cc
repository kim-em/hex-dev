// Persistent NTL GF2X bench-comparator driver for HexGF2.
//
// Reads one request per line from stdin, writes one reply per line to stdout.
// Spawned once per `lake exe hexgf2_bench run` invocation by
// `HexGF2/Bench.lean` and reused across all comparator calls in that process,
// per `SPEC/benchmarking.md` §"External comparators — Process call".
//
// Request grammar (one per line):
//   add  <hex_lhs> <hex_rhs>
//   mul  <hex_lhs> <hex_rhs>
//   div  <hex_lhs> <hex_rhs>
//   rem  <hex_lhs> <hex_rhs>
//   gcd  <hex_lhs> <hex_rhs>
//   shl  <hex_lhs> <decimal_shift>
//   shr  <hex_lhs> <decimal_shift>
//   ping
//
// Each <hex_*> is the polynomial's normalized byte representation (the same
// little-endian byte sequence as `BytesFromGF2X` produces), uppercase hex,
// `0` for the zero polynomial. The reply is exactly 16 lowercase hex digits:
// the `mixWord`-fold checksum of the result's normalized UInt64 word array,
// matching `Hex.GF2Bench.checksumPoly` in `HexGF2/Bench.lean`.
//
// `ping` exists for the per-call overhead measurement: it returns the
// checksum `0` after parsing the request, so wallclock-per-`ping` measures
// the round-trip protocol cost.
//
// Build via `scripts/oracle/setup_gf2_ntl_driver.sh`, which detects NTL and
// caches a release-mode binary under
// `$XDG_CACHE_HOME/hex/oracle/gf2_ntl_bench_driver`.

#include <NTL/GF2X.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

using NTL::GF2X;

namespace {

constexpr uint64_t kMixMult = 0x9E3779B97F4A7C15ULL;
constexpr uint64_t kMixAdd  = 0xBF58476D1CE4E5B9ULL;

inline uint64_t mix_word(uint64_t acc, uint64_t x) {
  return acc * kMixMult + x + kMixAdd;
}

int hex_value(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

// Parse a hex byte string into a packed byte buffer in little-endian order.
// Empty / "0" input produces an empty buffer (representing the zero polynomial).
// Reads byte-by-byte from least-significant byte first: hex pair `aabb` means
// byte 0 = 0xAA, byte 1 = 0xBB. The hex string therefore lists bytes in the
// same order they appear in memory after `BytesFromGF2X`.
bool parse_hex_bytes(const std::string &hex, std::vector<unsigned char> &out) {
  out.clear();
  if (hex.empty() || hex == "0") {
    return true;
  }
  if ((hex.size() % 2) != 0) {
    return false;
  }
  out.reserve(hex.size() / 2);
  for (std::size_t i = 0; i < hex.size(); i += 2) {
    int hi = hex_value(hex[i]);
    int lo = hex_value(hex[i + 1]);
    if (hi < 0 || lo < 0) return false;
    out.push_back(static_cast<unsigned char>((hi << 4) | lo));
  }
  return true;
}

GF2X build_gf2x(const std::vector<unsigned char> &bytes) {
  GF2X x;
  if (bytes.empty()) {
    NTL::clear(x);
    return x;
  }
  NTL::GF2XFromBytes(x, bytes.data(), static_cast<long>(bytes.size()));
  return x;
}

// Convert `result` to packed UInt64 words (little-endian byte order, trailing
// zero words trimmed) and apply the Lean-side `mixWord` fold starting from
// `acc = 0`. This matches `Hex.GF2Bench.checksumPoly` over the result's
// normalized words.
uint64_t checksum_gf2x(const GF2X &result) {
  long degree = NTL::deg(result);
  if (degree < 0) {
    return 0;  // zero polynomial -> empty word array -> fold of 0
  }
  long num_bytes = degree / 8 + 1;
  // Pad to 8-byte boundary so we can copy whole UInt64 words.
  long word_count = (num_bytes + 7) / 8;
  std::vector<unsigned char> buf(static_cast<std::size_t>(word_count) * 8, 0);
  NTL::BytesFromGF2X(buf.data(), result, num_bytes);
  // Trim trailing zero words to match `normalizeWords`.
  while (word_count > 0) {
    uint64_t word = 0;
    std::memcpy(&word, buf.data() + (word_count - 1) * 8, sizeof(uint64_t));
    if (word != 0) break;
    --word_count;
  }
  uint64_t acc = 0;
  for (long i = 0; i < word_count; ++i) {
    uint64_t word = 0;
    std::memcpy(&word, buf.data() + i * 8, sizeof(uint64_t));
    acc = mix_word(acc, word);
  }
  return acc;
}

void emit_checksum(uint64_t checksum) {
  // Always exactly 16 lowercase hex digits + newline. Reuse a small buffer.
  char out[18];
  std::snprintf(out, sizeof(out), "%016llx\n",
                static_cast<unsigned long long>(checksum));
  std::fwrite(out, 1, 17, stdout);
  std::fflush(stdout);
}

void emit_error(const char *message) {
  std::fprintf(stderr, "gf2_ntl_bench_driver: %s\n", message);
  std::fputs("ERROR\n", stdout);
  std::fflush(stdout);
}

bool handle_request(const std::string &line) {
  std::istringstream in(line);
  std::string op;
  if (!(in >> op)) {
    emit_error("empty request");
    return true;
  }
  if (op == "ping") {
    emit_checksum(0);
    return true;
  }
  std::string lhs_hex;
  if (!(in >> lhs_hex)) {
    emit_error("missing lhs operand");
    return true;
  }
  std::vector<unsigned char> lhs_bytes;
  if (!parse_hex_bytes(lhs_hex, lhs_bytes)) {
    emit_error("malformed lhs hex");
    return true;
  }
  GF2X lhs = build_gf2x(lhs_bytes);
  GF2X result;
  if (op == "add" || op == "mul" || op == "div" || op == "rem" || op == "gcd") {
    std::string rhs_hex;
    if (!(in >> rhs_hex)) {
      emit_error("missing rhs operand");
      return true;
    }
    std::vector<unsigned char> rhs_bytes;
    if (!parse_hex_bytes(rhs_hex, rhs_bytes)) {
      emit_error("malformed rhs hex");
      return true;
    }
    GF2X rhs = build_gf2x(rhs_bytes);
    if (op == "add") {
      NTL::add(result, lhs, rhs);
    } else if (op == "mul") {
      NTL::mul(result, lhs, rhs);
    } else if (op == "div") {
      // Hex `runDivChecksum` computes the schoolbook quotient. NTL's `div`
      // requires divisibility on exact `GF2X`; use `DivRem` and discard
      // the remainder so non-divisible inputs return the same quotient
      // Hex reports.
      GF2X tmp_rem;
      NTL::DivRem(result, tmp_rem, lhs, rhs);
    } else if (op == "rem") {
      NTL::rem(result, lhs, rhs);
    } else {
      NTL::GCD(result, lhs, rhs);
    }
  } else if (op == "shl" || op == "shr") {
    long shift = 0;
    if (!(in >> shift)) {
      emit_error("missing shift amount");
      return true;
    }
    if (shift < 0) {
      emit_error("negative shift");
      return true;
    }
    if (op == "shl") {
      NTL::LeftShift(result, lhs, shift);
    } else {
      NTL::RightShift(result, lhs, shift);
    }
  } else if (op == "quit") {
    return false;
  } else {
    emit_error("unknown op");
    return true;
  }
  emit_checksum(checksum_gf2x(result));
  return true;
}

}  // namespace

int main() {
  std::ios::sync_with_stdio(false);
  std::cin.tie(nullptr);
  std::string line;
  while (std::getline(std::cin, line)) {
    if (!handle_request(line)) break;
  }
  return 0;
}
