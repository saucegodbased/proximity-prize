// Full arithmetic gate for the W=133226 identity-node branches.
//
// This deliberately carries the source kernel, all three strict L-shape
// helper exits, the shared terminal/exit flag LP, and the nonactive cleanup.
// It does not build a matrix.  The imported arithmetic is the independently
// checked finite-prefix rank/column/band evaluator used for W=133225.
#define N LEGACY_OPTIMIZER_N
#define TARGET LEGACY_OPTIMIZER_TARGET
#define main legacy_optimizer_main
#include "weighted_scalar_w133219_full_optimizer_6900.cpp"
#undef main
#undef TARGET
#undef N

#include <array>

constexpr uint64_t AUDIT_CORE_FLOOR = 263611557201523206ULL;
// This is the uniform shortened-Johnson common-node cap at the worst node
// cardinality 262144.  Smaller cardinalities may use a smaller cap, but the
// full-scope route intentionally needs only this one value.
constexpr uint64_t AUDIT_V = 68769;
constexpr uint64_t AUDIT_SMALL = 1453806;

static Source source_at(uint64_t n, uint64_t k, uint64_t m) {
  const uint64_t B = m * A, D = 4 * k, M = B / (W - 2);
  const u128 rank = finite_rank_general_fast(m, k, M);
  const u128 cols = pair_eval(pair_coeff(k), B) / (2 * W);
  return {k, m, B, D, 2 * k, M, rank,
    i128(cols) - i128(u128(n) * rank)};
}

static u128 corrected_first_regular(uint64_t n, uint64_t y,
    uint64_t r) {
  const u128 cost = (1 + u128(2) * W * y) * r
    + u128(W) * (2 * r - 1) * y;
  return ceil_div(u128(n - W) * cost, A - W);
}

// The final semantic consumer already puts the Y-only case in the T-free
// family, so there is no extra +M term here.
static u128 corrected_cleanup(uint64_t n, const Source &p) {
  const uint64_t y = (2 * p.T - 1) * p.M;
  const uint64_t r = (2 * p.T - 1) * p.D;
  return corrected_first_regular(n, y, r) + u128(2 * r - 1) * y
    + corrected_first_regular(n, p.M, p.D) + u128(2 * p.D - 1) * p.M;
}

static std::array<u128, 3> cumulative_coeff(Flag q, Flag r) {
  const Flag z{1, 0, 0}, yz{0, 1, 0}, all{0, 0, 1};
  const u128 cz = mixed(z, q, r);
  const u128 cy = mixed(yz, q, r);
  const u128 ca = mixed(all, q, r);
  return {cz, cy - cz, ca - cy};
}

// Nat subtraction, unlike uint64_t subtraction, truncates at zero.  Keeping
// that behavior explicit matters for the skinny profile M=S=T=32.
static Flag audit_agreement_flag(uint64_t M, uint64_t S, uint64_t T) {
  const uint64_t zTail = 2 * (M - S) >= 1 ? 2 * (M - S) - 1 : 0;
  const uint64_t tTail = T >= 1 ? T - 1 : 0;
  return {1 + u128(W) * zTail,
    u128(2) * W * (S - T) + W, u128(2) * W * tTail};
}

struct Coupled {
  u128 numerator, cap;
  std::array<u128, 3> restCoeff, exitCoeff;
};

// Exact maximum of the six-variable shared-budget LP.  `primaryCumulative`
// is (J,M,S) and `restCumulative` is the selected terminal arm.  For each
// nested resource, positivity spends the whole primary budget and the larger
// of the rest/exit marginal receives as much as its terminal cap permits.
static Coupled coupled_cap(uint64_t n, const Source &p, Flag helper,
    uint64_t restJ, uint64_t restM, uint64_t restS) {
  const Flag restFlag{restJ - restM, restM - restS, restS};
  const Flag restAgreement = audit_agreement_flag(restJ, restM, restS);
  const Flag primaryAgreement = audit_agreement_flag(p.M, p.D, p.T);
  const auto rc0 = cumulative_coeff(restAgreement, restAgreement);
  const auto ec0 = cumulative_coeff(helper, primaryAgreement);
  std::array<u128, 3> rc{}, ec{};
  const std::array<uint64_t, 3> total{p.M, p.D, p.T};
  const std::array<uint64_t, 3> restCap{restJ, restM, restS};
  u128 numerator = 0;
  for (size_t i = 0; i < 3; ++i) {
    rc[i] = u128(n - AUDIT_V) * (n - AUDIT_V) * rc0[i];
    ec[i] = u128(n - AUDIT_V) * (A - AUDIT_V) * ec0[i];
    numerator += ec[i] * total[i];
    if (rc[i] > ec[i])
      numerator += (rc[i] - ec[i]) * std::min(total[i], restCap[i]);
  }
  return {numerator,
    ceil_div(numerator, u128(A - AUDIT_V) * (A - AUDIT_V)), rc, ec};
}

static u128 joint_band_exact_at(const Source &s, uint64_t jet,
    uint64_t derivative) {
  const uint64_t g = (W - 2) * jet;
  const uint64_t delta = A - W + 2;
  u128 out = 0;
  for (uint64_t j = 1; j * derivative <= s.D; ++j) {
    const u128 spent = u128(j) * g + u128(j - 1) * delta;
    if (spent >= s.B) break;
    const uint64_t top = s.B - uint64_t(spent);
    const uint64_t E = s.D - j * derivative;
    out += columns_linear(top, E) - columns_linear(top - delta, E);
  }
  return out;
}

static u128 triangle_relaxed_at(uint64_t C, uint64_t E) {
  u128 out = 0;
  for (uint64_t e = 0; e <= E; ++e) {
    const uint64_t x = C > (W - 2) * e ? C - (W - 2) * e : 0;
    const uint64_t width = x ? (x + W - 1) / W : 0;
    out += u128(std::min(e, E - e) + 1) * width;
  }
  return out;
}

// This is the literal relaxed upper sum used by the Lean stage theorem; the
// stronger exact column difference above is retained only as a cross-check.
static u128 joint_band_relaxed_at(const Source &s, uint64_t jet,
    uint64_t derivative) {
  const uint64_t g = (W - 2) * jet;
  const uint64_t delta = A - W + 2;
  u128 out = 0;
  for (uint64_t j = 1; j * derivative <= s.D; ++j) {
    const u128 spent = u128(j) * g + u128(j - 1) * delta;
    if (spent >= s.B) break;
    out += u128(delta) * triangle_relaxed_at(
      s.B - uint64_t(spent), s.D - j * derivative);
  }
  return out;
}

static u128 two_incidence_cap(uint64_t n, Flag source, Flag agreement) {
  return ceil_div(u128(n - AUDIT_V) * (n - AUDIT_V)
      * mixed(source, agreement, agreement),
    u128(A - AUDIT_V) * (A - AUDIT_V));
}

static u128 one_incidence_cap(uint64_t n, Flag source, Flag helper,
    Flag agreement) {
  return ceil_div(u128(n - AUDIT_V) * mixed(source, helper, agreement),
    A - AUDIT_V);
}

static void full_scope_max_node_route() {
  constexpr uint64_t n = 262144;
  const Source primary = source_at(n, 61, 550);
  const Source helperSource = source_at(n, 1312, 11810);
  const Flag primaryFlag{500, 122, 122};
  const Flag helperFlag{10745, 2624, 2624};
  const Flag primaryAgreement = audit_agreement_flag(744, 244, 122);
  const u128 cleanup = corrected_cleanup(n, primary);
  const u128 helperExit = one_incidence_cap(n, primaryFlag, helperFlag,
    primaryAgreement);

  struct JointGate { uint64_t jet, derivative; const char *label; };
  for (const JointGate gate : {JointGate{213, 4, "J-heavy"},
      JointGate{33, 56, "D-heavy"}, JointGate{212, 55, "corner"}}) {
    const u128 exact = joint_band_exact_at(helperSource,
      gate.jet, gate.derivative);
    const u128 relaxed = joint_band_relaxed_at(helperSource,
      gate.jet, gate.derivative);
    std::cout << "FULL_HELPER name=" << gate.label << " jet=" << gate.jet
      << " derivative=" << gate.derivative << " exactBand=" << show(exact)
      << " relaxedBand=" << show(relaxed) << " formalMargin="
      << showi(helperSource.kernel - i128(relaxed)) << "\n";
  }

  std::cout << "FULL_SOURCE primaryRank=" << show(primary.rank)
    << " primaryKernelLower=" << showi(primary.kernel)
    << " helperRank=" << show(helperSource.rank)
    << " helperKernelLower=" << showi(helperSource.kernel)
    << " helperExit=" << show(helperExit) << " cleanup=" << show(cleanup)
    << "\n";

  struct Terminal { uint64_t M, S, T; const char *label; bool coupled; };
  for (const Terminal terminal : {
      Terminal{211, 55, 27, "old-arm-A", true},
      Terminal{212, 54, 27, "old-arm-B", true},
      // derivativeDegree<=3 implies RT<=3 and T<=1.  We deliberately loosen
      // to S=T=5: T=1 would make the reduced agreement all-coordinate zero
      // and fail the small-family curve absorption gate.
      Terminal{744, 5, 5, "derivative<=3-loose", false},
      // jetDegree<=32 implies RT,T<=32.  M is loosened to 33 because the
      // reduced-agreement support theorem requires S<M.
      Terminal{33, 32, 32, "jet<=32-loose", false}}) {
    const Flag source{terminal.M - terminal.S,
      terminal.S - terminal.T, terminal.T};
    const Flag agreement = audit_agreement_flag(
      terminal.M, terminal.S, terminal.T);
    u128 active;
    if (terminal.coupled) {
      active = coupled_cap(n, primary, helperFlag,
        terminal.M, terminal.S, terminal.T).cap;
    } else {
      // These branches have enormous slack, so charge rest and exits against
      // their independent valid budgets; no shared-budget optimization is
      // needed here.
      active = two_incidence_cap(n, source, agreement) + helperExit;
    }
    const u128 total = active + cleanup;
    const u128 curveLeft = u128(AUDIT_SMALL) * (A - AUDIT_V);
    const u128 curveRight = u128(n - AUDIT_V) * agreement.a;
    const u128 surfaceLeft = u128(AUDIT_SMALL)
      * (A - AUDIT_V) * (A - AUDIT_V);
    const u128 surfaceRight = u128(n - AUDIT_V) * (n - AUDIT_V)
      * agreement.a * agreement.a;
    const u128 projection = (agreement.y + agreement.a) * source.a
      + (source.y + source.a) * agreement.a;
    std::cout << "FULL_TERMINAL name=" << terminal.label
      << " sourceFlag=" << show(source.z) << "," << show(source.y)
      << "," << show(source.a) << " agreementFlag=" << show(agreement.z)
      << "," << show(agreement.y) << "," << show(agreement.a)
      << " curveAbsMargin=" << showi(i128(curveRight)-i128(curveLeft))
      << " surfaceAbsMargin="
      << showi(i128(surfaceRight)-i128(surfaceLeft))
      << " projection=" << show(projection)
      << " projectionMargin=" << showi(i128(PRIME)-i128(projection))
      << " active=" << show(active) << " total=" << show(total)
      << " endpointMargin="
      << showi(i128(AUDIT_CORE_FLOOR)-i128(total)) << "\n";
  }
}

struct LedgerBest {
  u128 worst = ~u128(0), armA = 0, armB = 0, cleanup = 0;
  Source p{};
};

static LedgerBest best_primary(uint64_t n, Flag helper,
    uint64_t terminalJ, uint64_t terminalD) {
  LedgerBest best;
  const uint64_t terminalT = terminalD / 2;
  const uint64_t armBJ = terminalJ + 1;
  const uint64_t armBD = terminalD - 1;
  const uint64_t armBT = armBD / 2;
  for (uint64_t k = 1; k <= 200; ++k) {
    for (uint64_t m = 8 * k;
        m <= std::min<uint64_t>(11810, 12 * k); ++m) {
      const Source p = source_at(n, k, m);
      if (p.kernel <= 0 || p.M < armBJ || p.D < terminalD
          || p.T < std::max(terminalT, armBT)) continue;
      const Coupled aCap = coupled_cap(n, p, helper,
        terminalJ, terminalD, terminalT);
      const Coupled bCap = coupled_cap(n, p, helper,
        armBJ, armBD, armBT);
      const u128 clean = corrected_cleanup(n, p);
      const u128 armA = aCap.cap + clean, armB = bCap.cap + clean;
      const u128 worst = std::max(armA, armB);
      if (worst < best.worst)
        best = {worst, armA, armB, clean, p};
    }
  }
  return best;
}

static void print_helper(uint64_t n, const char *name, const Source &s,
    uint64_t jetCap, uint64_t derivativeCap) {
  const u128 jb = exact_band(s, jetCap, false);
  const u128 db = exact_band(s, derivativeCap, true);
  std::cout << "HELPER n=" << n << " name=" << name << " k=" << s.k
    << " m=" << s.m << " B=" << s.B << " M=" << s.M
    << " D=" << s.D << " T=" << s.T << " rank=" << show(s.rank)
    << " kernelLower=" << showi(s.kernel)
    << " Jcap=" << jetCap << " Jband=" << show(jb)
    << " Jmargin=" << showi(s.kernel - i128(jb))
    << " Dcap=" << derivativeCap << " Dband=" << show(db)
    << " Dmargin=" << showi(s.kernel - i128(db)) << "\n";
}

static void audit_case(uint64_t n, uint64_t terminalJ,
    uint64_t terminalD, uint64_t jK, uint64_t jM,
    uint64_t dK, uint64_t dM, uint64_t commonM,
    uint64_t commonD, uint64_t commonT) {
  const Source hJ = source_at(n, jK, jM);
  const Source hD = source_at(n, dK, dM);
  const Flag helper{commonM - commonD, commonD - commonT, commonT};
  const uint64_t jBandCap = terminalJ + 1;
  const uint64_t dBandCap = terminalD;
  print_helper(n, "J", hJ, jBandCap, dBandCap);
  print_helper(n, "D", hD, jBandCap, dBandCap);
  const u128 corner = joint_band_exact_at(hJ, terminalJ + 1, terminalD);
  std::cout << "CORNER n=" << n << " jet=" << terminalJ + 1
    << " derivative=" << terminalD << " band=" << show(corner)
    << " margin=" << showi(hJ.kernel - i128(corner)) << "\n";
  const LedgerBest b = best_primary(n, helper, terminalJ, terminalD);
  const Coupled ca = coupled_cap(n, b.p, helper,
    terminalJ, terminalD, terminalD / 2);
  const Coupled cb = coupled_cap(n, b.p, helper,
    terminalJ + 1, terminalD - 1, (terminalD - 1) / 2);
  std::cout << "LEDGER n=" << n << " terminal=(" << terminalJ << ","
    << terminalD << ")U(" << terminalJ + 1 << "," << terminalD - 1
    << ") primary=" << b.p.k << "," << b.p.m << " M=" << b.p.M
    << " D=" << b.p.D << " T=" << b.p.T
    << " primaryKernel=" << showi(b.p.kernel)
    << " helperFlag=" << show(helper.z) << "," << show(helper.y)
    << "," << show(helper.a) << " armAActive=" << show(ca.cap)
    << " armBActive=" << show(cb.cap) << " cleanup=" << show(b.cleanup)
    << " armATotal=" << show(b.armA) << " armBTotal=" << show(b.armB)
    << " worst=" << show(b.worst) << " margin="
    << showi(i128(AUDIT_CORE_FLOOR) - i128(b.worst)) << "\n";
  std::cout << "LP_MARGINS n=" << n;
  for (size_t i = 0; i < 3; ++i)
    std::cout << " A" << i << "=" << showi(i128(ca.restCoeff[i])
      - i128(ca.exitCoeff[i]));
  for (size_t i = 0; i < 3; ++i)
    std::cout << " B" << i << "=" << showi(i128(cb.restCoeff[i])
      - i128(cb.exitCoeff[i]));
  std::cout << "\n";
}

int main(int argc, char **argv) {
  W = argc > 1 ? std::stoull(argv[1]) : 133226;
  if (W != 133226 && W != 133225) {
    std::cerr << "this audit is scoped to W=133226 (133225 is allowed only "
      "as a regression cross-check)\n";
    return 2;
  }
  std::cout << "PARAM W=" << W << " A=" << A
    << " delta=" << A - W + 2 << " coreFloor=" << AUDIT_CORE_FLOOR
    << "\n";

  full_scope_max_node_route();

  // Three or more nonidentity nodes.  Two nearby sources share the literal
  // common global box (15993,5248,2624).
  audit_case(262141, 211, 55, 1312, 11810, 1306, 11809,
    15993, 5248, 2624);

  // The one- and two-exception cases need a one-step larger L terminal.  The
  // single (1312,11810) source handles every exit at these cutoffs.
  audit_case(262142, 212, 56, 1312, 11810, 1312, 11810,
    15993, 5248, 2624);
  audit_case(262143, 212, 56, 1312, 11810, 1312, 11810,
    15993, 5248, 2624);

  // With zero exceptions the J exit needs one further unit.
  audit_case(262144, 213, 56, 1312, 11810, 1312, 11810,
    15993, 5248, 2624);

  for (uint64_t n : {262141ULL, 262142ULL, 262143ULL, 262144ULL}) {
    const uint64_t u = AUDIT_V + 1;
    const i128 inner = i128(A - u) * (A - u)
      - i128(n - u) * (W - u);
    const u128 lhs = u128(n - u) * (n - W);
    const i128 rhs = i128(AUDIT_SMALL + 1) * inner;
    std::cout << "JOHNSON n=" << n << " lhs=" << show(lhs)
      << " rhs=" << showi(rhs) << " margin="
      << showi(rhs - i128(lhs)) << "\n";
  }
}
