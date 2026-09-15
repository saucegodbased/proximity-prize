// Exact joint-band probe for the isolated W=133225 terminal corner.
//
// This is deliberately a profile evaluator, not a matrix computation.  It
// reuses the independently checked finite-prefix source dimensions and exact
// stage-fibre count from the exhaustive helper audit.  At the corner we know
// both jetDegree(P)>=212 and derivativeDegree(P)>=55, hence simultaneously
//
//   mainDegree(P) >= (W-2)*212,   derivativeDegree(P) >= 55.
//
// The old one-band scans were forced to forget one of these two inequalities.
#define IDENTITY_N 262143
#define main unrestricted_helper_main
#include "weighted_helper_unrestricted_m_w133225_6900.cpp"
#undef main

static u128 joint_band_exact(const Source &s, uint64_t jet,
    uint64_t derivative) {
  const uint64_t g = (W - 2) * jet;
  u128 out = 0;
  for (uint64_t j = 1; j * derivative <= s.D; ++j) {
    const u128 spent = u128(j) * g + u128(j - 1) * DELTA;
    if (spent >= s.B) break;
    const uint64_t top = s.B - uint64_t(spent);
    const uint64_t E = s.D - j * derivative;
    out += columns(top, E) - columns(top - DELTA, E);
  }
  return out;
}

static u128 triangle_relaxed_count(uint64_t C, uint64_t E) {
  u128 out = 0;
  for (uint64_t n = 0; n <= E; ++n) {
    const uint64_t x = C > (W - 2) * n ? C - (W - 2) * n : 0;
    const uint64_t width = x ? (x + W - 1) / W : 0;
    out += u128(std::min(n, E - n) + 1) * width;
  }
  return out;
}

static u128 joint_band_relaxed(const Source &s, uint64_t jet,
    uint64_t derivative) {
  const uint64_t g = (W - 2) * jet;
  u128 out = 0;
  for (uint64_t j = 1; j * derivative <= s.D; ++j) {
    const u128 spent = u128(j) * g + u128(j - 1) * DELTA;
    if (spent >= s.B) break;
    out += u128(DELTA) * triangle_relaxed_count(
      s.B - uint64_t(spent), s.D - j * derivative);
  }
  return out;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    std::cerr << "usage: weighted_helper_exact_corner k m\n";
    return 2;
  }
  const uint64_t k = std::stoull(argv[1]);
  const uint64_t m = std::stoull(argv[2]);
  const uint64_t B = m * A, D = 4 * k, M = B / (W - 2);
  LatticeTables tab(MAX_M + 10);
  const u128 rank = exact_low(tab, m, k) + finite_high(m, k, M);
  const u128 cols = columns(B, D);
  const Source s{k, m, B, D, M, rank, cols,
    i128(cols) - i128(N * rank)};
  const u128 corner = joint_band_exact(s, 212, 55);
  const u128 relaxed = joint_band_relaxed(s, 212, 55);
  const u128 jHeavy = band_exact(s, 212, false);
  const u128 dHeavy = band_exact(s, 55, true);
  std::cout << "EXACT_CORNER k=" << k << " m=" << m << " B=" << B
    << " M=" << M << " D=" << D << " rank=" << show(rank)
    << " columns=" << show(cols) << " kernel=" << showi(s.kernel)
    << " cornerBand=" << show(corner)
    << " cornerMargin=" << showi(s.kernel - i128(corner))
    << " relaxedBand=" << show(relaxed)
    << " relaxedMargin=" << showi(s.kernel - i128(relaxed))
    << " J212Margin=" << showi(s.kernel - i128(jHeavy))
    << " D55Margin=" << showi(s.kernel - i128(dHeavy)) << "\n";
}
