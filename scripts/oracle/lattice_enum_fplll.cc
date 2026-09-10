// Informational fplll 5.5.0 comparator; no Hex runtime FFI is introduced.
// Protocol: one line per request: shortest|closest n, n*n basis entries, n target entries.
// Inputs have already been scaled to integer targets by the Python driver.
#include <fplll/fplll.h>
#include <gmpxx.h>
#include <chrono>
#include <iostream>
#include <sstream>
#include <stdexcept>

#if FPLLL_MAJOR_VERSION != 5 || FPLLL_MINOR_VERSION != 5 || FPLLL_MICRO_VERSION != 0
#error "This comparator pins fplll 5.5.0; review its contracts before changing the pin."
#endif

using namespace fplll;
using Clock = std::chrono::steady_clock;
static long long nanos(Clock::time_point a, Clock::time_point b) {
  return std::chrono::duration_cast<std::chrono::nanoseconds>(b-a).count();
}

// Verify the actual SVP/CVP prerequisite with exact rational arithmetic before search.
// The reducer's documented guarantee is weaker than its requested parameters.
static void check_reduced(const ZZ_mat<mpz_t>& b) {
  const int n = b.get_rows(), m = b.get_cols();
  std::vector<std::vector<mpq_class>> orth(n, std::vector<mpq_class>(m));
  std::vector<mpq_class> norms(n);
  std::vector<std::vector<mpq_class>> mu(n, std::vector<mpq_class>(n));
  const mpq_class delta(99,100), eta(51,100);
  for (int i=0; i<n; ++i) {
    for (int k=0; k<m; ++k) orth[i][k] = mpz_class(b[i][k].get_data());
    for (int j=0; j<i; ++j) {
      mpq_class dot = 0;
      for (int k=0; k<m; ++k) dot += mpz_class(b[i][k].get_data()) * orth[j][k];
      mu[i][j] = dot / norms[j];
      if (abs(mu[i][j]) > eta) throw std::runtime_error("size reduction prerequisite failed");
      for (int k=0; k<m; ++k) orth[i][k] -= mu[i][j] * orth[j][k];
    }
    for (auto& x : orth[i]) norms[i] += x*x;
    if (norms[i] <= 0) throw std::runtime_error("dependent basis");
    if (i && norms[i] < (delta - mu[i][i-1]*mu[i][i-1]) * norms[i-1])
      throw std::runtime_error("Lovasz prerequisite failed");
  }
}

int main() {
  std::string line;
  while (std::getline(std::cin, line)) {
    try {
      std::istringstream in(line);
      std::string op, token;
      int n = 0;
      in >> op >> n;
      if ((op != "shortest" && op != "closest") || n < 1 || n > 32)
        throw std::runtime_error("unsupported operation or dimension");
      ZZ_mat<mpz_t> b(n,n);
      for (int i=0; i<n; ++i) for (int j=0; j<n; ++j) {
        if (!(in >> token) || !b[i][j].set_str(token.c_str())) throw std::runtime_error("invalid matrix");
      }
      std::vector<Z_NR<mpz_t>> target(n), coefficients;
      for (int i=0; i<n; ++i)
        if (!(in >> token) || !target[i].set_str(token.c_str())) throw std::runtime_error("invalid target");
      if (in >> token) throw std::runtime_error("trailing input");
      const auto start = Clock::now();
      // delta'=2*delta-1=.998 and eta'=2*eta-.5=.502 imply (.99,.51).
      const int lll_status = lll_reduction(b, .999, .501, LM_WRAPPER, FT_DEFAULT, 0, LLL_DEFAULT);
      const auto reduced = Clock::now();
      if (lll_status != RED_SUCCESS) {
        std::cout << "{\"lll_status\":" << lll_status << ",\"search_status\":null}" << std::endl;
        continue;
      }
      check_reduced(b);
      const auto checked = Clock::now();
      const int status = op == "shortest"
        ? shortest_vector(b, coefficients, SVPM_PROVED, SVP_DEFAULT)
        : closest_vector(b, target, coefficients, CVPM_PROVED, CVP_DEFAULT);
      const auto searched = Clock::now();
      std::cout << "{\"version\":\"5.5.0\",\"method\":\"" << (op == "shortest" ? "SVPM_PROVED" : "CVPM_PROVED")
        << "\",\"lll_status\":" << lll_status << ",\"search_status\":" << status
        << ",\"lll_ns\":" << nanos(start,reduced) << ",\"prerequisite_ns\":" << nanos(reduced,checked)
        << ",\"search_ns\":" << nanos(checked,searched) << ",\"basis\":[";
      for (int i=0; i<n; ++i) {
        if (i) std::cout << ',';
        std::cout << '[';
        for (int j=0; j<n; ++j) { if (j) std::cout << ','; std::cout << '"' << b[i][j] << '"'; }
        std::cout << ']';
      }
      std::cout << "],\"coefficients\":[";
      for (size_t i=0; i<coefficients.size(); ++i) { if (i) std::cout << ','; std::cout << '"' << coefficients[i] << '"'; }
      std::cout << "]}" << std::endl;
    } catch (const std::exception& e) {
      std::cerr << "lattice_enum_fplll: " << e.what() << '\n';
      return 1;
    }
  }
}
