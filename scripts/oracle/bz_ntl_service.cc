// Persistent NTL warm factorization driver for the cross-system benchmark suite.
//
// Reads one request per line from stdin, writes one reply per line to stdout,
// speaking the suite line protocol (identical to the verified Isabelle
// comparator `scripts/oracle/bz-isabelle/Main.hs` and the hex
// `hexbz_factor_service`):
//
//   request:  {"coeffs":[c0,c1,...]}   (integer coeffs, ascending degree)
//   reply:    {"ok":true,"result":{"scalar":s,
//                "factors":[{"coeffs":[...],"multiplicity":m},...]}}
//             {"ok":false,"error":"..."}   on a malformed request
//
// Factors integer polynomials with NTL's `ZZXFactoring` (`factor`): the C++
// arbitrary-precision counterpart to FLINT in the comparison. Coefficients can
// be hundreds of digits (Swinnerton-Dyer, F_630), so both parsing and printing
// go through NTL `ZZ` decimal I/O; no fixed-width integer path is used.
//
// Build via `scripts/oracle/setup_bz_ntl_driver.sh`, which detects NTL and
// caches a release-mode binary under the oracle cache.

#include <NTL/ZZX.h>
#include <NTL/ZZXFactoring.h>
#include <NTL/pair_ZZX_long.h>

#include <cctype>
#include <iostream>
#include <sstream>
#include <string>

using NTL::ZZ;
using NTL::ZZX;
using NTL::vec_pair_ZZX_long;

namespace {

// Extract the integer array following the `"coeffs"` key. Returns false if no
// well-formed `"coeffs":[ ... ]` array is present.
bool parse_coeffs(const std::string &line, ZZX &out) {
  const std::string key = "\"coeffs\"";
  std::size_t k = line.find(key);
  if (k == std::string::npos) return false;
  std::size_t open = line.find('[', k);
  if (open == std::string::npos) return false;
  std::size_t close = line.find(']', open);
  if (close == std::string::npos) return false;
  std::string payload = line.substr(open + 1, close - open - 1);

  NTL::clear(out);
  long index = 0;
  std::string token;
  std::stringstream ss(payload);
  while (std::getline(ss, token, ',')) {
    // Trim surrounding whitespace.
    std::size_t a = token.find_first_not_of(" \t\r\n");
    std::size_t b = token.find_last_not_of(" \t\r\n");
    if (a == std::string::npos) continue;  // tolerate a trailing empty split
    std::string digits = token.substr(a, b - a + 1);
    ZZ value;
    std::istringstream vs(digits);
    vs >> value;
    if (vs.fail()) return false;
    NTL::SetCoeff(out, index, value);
    ++index;
  }
  return true;
}

void print_coeffs(std::ostream &os, const ZZX &f) {
  os << '[';
  long d = NTL::deg(f);
  if (d < 0) {
    os << '0';  // the zero polynomial, degree -1: emit a single 0 coefficient
  } else {
    for (long i = 0; i <= d; ++i) {
      if (i) os << ',';
      os << NTL::coeff(f, i);
    }
  }
  os << ']';
}

void handle_line(const std::string &line, std::ostream &os) {
  ZZX f;
  if (!parse_coeffs(line, f)) {
    os << "{\"ok\":false,\"error\":\"expected JSON object with integer array "
          "field coeffs\"}\n";
    return;
  }
  ZZ content;
  vec_pair_ZZX_long factors;
  NTL::factor(content, factors, f);

  os << "{\"ok\":true,\"result\":{\"scalar\":" << content << ",\"factors\":[";
  for (long i = 0; i < factors.length(); ++i) {
    if (i) os << ',';
    os << "{\"coeffs\":";
    print_coeffs(os, factors[i].a);
    os << ",\"multiplicity\":" << factors[i].b << '}';
  }
  os << "]}}\n";
}

}  // namespace

int main() {
  std::ios::sync_with_stdio(false);
  std::cin.tie(nullptr);
  std::string line;
  while (std::getline(std::cin, line)) {
    // Skip blank keep-alive lines.
    std::size_t a = line.find_first_not_of(" \t\r\n");
    if (a == std::string::npos) continue;
    handle_line(line, std::cout);
    std::cout.flush();
  }
  return 0;
}
