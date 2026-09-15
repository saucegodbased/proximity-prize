#define W133226_AUDIT_NO_MAIN
#include "weighted_w133226_cutoff34_full_audit_6900.cpp"
#undef W133226_AUDIT_NO_MAIN

constexpr uint64_t N227 = 262144;
static uint64_t VPROBE = 68774;

static uint64_t johnson_v() {
  for (uint64_t v = 0; v < W; ++v) {
    const uint64_t u = v + 1;
    const i128 inner = i128(A - u) * (A - u)
      - i128(N227 - u) * (W - u);
    if (inner <= 0) continue;
    const u128 lhs = u128(N227 - u) * (N227 - W);
    const u128 rhs = u128(AUDIT_SMALL + 1) * u128(inner);
    if (lhs < rhs) return v;
  }
  __builtin_trap();
}

static Source cached_source(uint64_t n, uint64_t k, uint64_t m,
    const PairCoeff &pc) {
  const uint64_t B = m * A, D = 4 * k, M = B / (W - 2);
  const u128 rank = finite_rank_general_fast(m, k, M);
  return {k, m, B, D, 2 * k, M, rank,
    i128(pair_eval(pc, B) / (2 * W)) - i128(u128(n) * rank)};
}

static uint64_t min_joint_derivative(const Source &s, uint64_t jet) {
  uint64_t lo = 0, hi = 1;
  while (joint_band_relaxed_at(s, jet, hi) >= u128(s.kernel)) hi *= 2;
  while (lo + 1 < hi) {
    const uint64_t mid = (lo + hi) / 2;
    if (joint_band_relaxed_at(s, jet, mid) < u128(s.kernel)) hi = mid;
    else lo = mid;
  }
  return hi;
}

static uint64_t min_joint_jet(const Source &s, uint64_t derivative) {
  uint64_t lo = 0, hi = 1;
  while (joint_band_relaxed_at(s, hi, derivative) >= u128(s.kernel)) hi *= 2;
  while (lo + 1 < hi) {
    const uint64_t mid = (lo + hi) / 2;
    if (joint_band_relaxed_at(s, mid, derivative) < u128(s.kernel)) hi = mid;
    else lo = mid;
  }
  return hi;
}

static u128 one_cap_227(Flag p, Flag q, Flag r) {
  return ceil_div(u128(N227 - VPROBE) * mixed(p, q, r), A - VPROBE);
}

static u128 two_cap_227(Flag p, Flag q) {
  return ceil_div(u128(N227 - VPROBE) * (N227 - VPROBE) * mixed(p, q, q),
    u128(A - VPROBE) * (A - VPROBE));
}

static Coupled coupled_227(const Source &p, Flag helper,
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
    rc[i] = u128(N227 - VPROBE) * (N227 - VPROBE) * rc0[i];
    ec[i] = u128(N227 - VPROBE) * (A - VPROBE) * ec0[i];
    numerator += ec[i] * total[i];
    if (rc[i] > ec[i])
      numerator += (rc[i] - ec[i]) * std::min(total[i], restCap[i]);
  }
  return {numerator,
    ceil_div(numerator, u128(A - VPROBE) * (A - VPROBE)), rc, ec};
}

static bool terminal_gates(const Flag &source, const Flag &agreement) {
  const u128 curveLeft = u128(AUDIT_SMALL) * (A - VPROBE);
  const u128 curveRight = u128(N227 - VPROBE) * agreement.a;
  const u128 surfaceLeft = u128(AUDIT_SMALL) * (A - VPROBE) * (A - VPROBE);
  const u128 surfaceRight = u128(N227 - VPROBE) * (N227 - VPROBE)
    * agreement.a * agreement.a;
  const u128 projection = (agreement.y + agreement.a) * source.a
    + (source.y + source.a) * agreement.a;
  return agreement.a >= AUDIT_SMALL && curveLeft <= curveRight
    && surfaceLeft <= surfaceRight && projection < PRIME;
}

int main(int argc, char **argv) {
  W = argc > 1 ? std::stoull(argv[1]) : 133227;
  VPROBE = johnson_v();
  const uint64_t armAJ = argc > 2 ? std::stoull(argv[2]) : 211;
  const uint64_t armAD = argc > 3 ? std::stoull(argv[3]) : 55;
  const uint64_t armBJ = armAJ + 1, armBD = armAD - 1;
  const uint64_t armAT = armAD / 2, armBT = armBD / 2;
  std::vector<Source> primary;
  for (uint64_t k = 1; k <= 200; ++k) {
    const PairCoeff pc = pair_coeff(k);
    for (uint64_t m = 8 * k;
        m <= std::min<uint64_t>(11810, 12 * k); ++m) {
      const Source p = cached_source(N227, k, m, pc);
      if (p.kernel > 0 && p.M >= armBJ && p.D >= armAD
          && p.T >= std::max(armAT, armBT))
        primary.push_back(p);
    }
  }
  std::cout << "PARAM W=" << W << " v=" << VPROBE
    << " PRIMARY count=" << primary.size() << "\n";

  u128 global = ~u128(0);
  Source bestH{}, bestP{};
  uint64_t bestDGate = 0, bestJGate = 0;
  u128 bestA = 0, bestB = 0, bestDSkinny = 0, bestJSkinny = 0;
  for (uint64_t k = 80; k <= 1320; ++k) {
    const uint64_t m = std::min<uint64_t>(11810, 9 * k);
    const PairCoeff pc = pair_coeff(k);
    const Source h = cached_source(N227, k, m, pc);
    if (h.kernel <= 0) continue;
    if (joint_band_relaxed_at(h, armAJ + 1, armBD + 1)
        >= u128(h.kernel)) continue;
    const uint64_t dGate = min_joint_derivative(h, armBJ + 1);
    const uint64_t jGate = min_joint_jet(h, armAD + 1);
    const uint64_t d0 = dGate - 1, j0 = jGate - 1;
    const Flag helper = sf(h);

    for (const Source &p : primary) {
      const uint64_t derivativeST = 2 * d0 + 1;
      if (derivativeST >= p.M || derivativeST > p.D || j0 == 0
          || j0 >= p.M || j0 > p.D) continue;
      const Flag derivativeFlag{p.M - derivativeST, 0, derivativeST};
      const Flag derivativeAgreement = audit_agreement_flag(
        p.M, derivativeST, derivativeST);
      const Flag jetFlag{1, 0, j0};
      const Flag jetAgreement = audit_agreement_flag(j0 + 1, j0, j0);
      if (!terminal_gates(derivativeFlag, derivativeAgreement)
          || !terminal_gates(jetFlag, jetAgreement)) continue;

      const Coupled aCap = coupled_227(p, helper, armAJ, armAD, armAT);
      const Coupled bCap = coupled_227(p, helper, armBJ, armBD, armBT);
      const u128 cleanup = corrected_cleanup(N227, p);
      const u128 helperExit = one_cap_227(sf(p), helper,
        audit_agreement_flag(p.M, p.D, p.T));
      const u128 armA = aCap.cap + cleanup;
      const u128 armB = bCap.cap + cleanup;
      const u128 derivativeTotal = two_cap_227(derivativeFlag,
        derivativeAgreement) + helperExit + cleanup;
      const u128 jetTotal = two_cap_227(jetFlag, jetAgreement)
        + helperExit + cleanup;
      const u128 worst = std::max({armA, armB, derivativeTotal, jetTotal});
      if (worst < global) {
        global = worst; bestH = h; bestP = p;
        bestDGate = dGate; bestJGate = jGate;
        bestA = armA; bestB = armB;
        bestDSkinny = derivativeTotal; bestJSkinny = jetTotal;
        std::cout << "IMPROVE worst=" << show(worst)
          << " margin=" << showi(i128(AUDIT_CORE_FLOOR) - i128(worst))
          << " h=" << h.k << "," << h.m << "," << h.M << "," << h.D
          << " terminal=" << armAJ << "x" << armAD << "," << armBJ
          << "x" << armBD << " gates=" << armBJ + 1 << "x" << dGate
          << "," << jGate << "x" << armAD + 1 << "," << armAJ + 1
          << "x" << armBD + 1
          << " p=" << p.k << "," << p.m << "," << p.M << "," << p.D
          << " arms=" << show(armA) << "," << show(armB)
          << " skinny=" << show(derivativeTotal) << "," << show(jetTotal)
          << "\n";
      }
    }
  }
  std::cout << "BEST worst=" << show(global)
    << " margin=" << showi(i128(AUDIT_CORE_FLOOR) - i128(global))
    << " h=" << bestH.k << "," << bestH.m << "," << bestH.M << ","
    << bestH.D << " terminal=" << armAJ << "x" << armAD << ","
    << armBJ << "x" << armBD << " gates=" << armBJ + 1 << "x"
    << bestDGate << "," << bestJGate << "x" << armAD + 1 << ","
    << armAJ + 1 << "x" << armBD + 1 << " p=" << bestP.k << ","
    << bestP.m << ","
    << bestP.M << "," << bestP.D << " arms=" << show(bestA) << ","
    << show(bestB) << " skinny=" << show(bestDSkinny) << ","
    << show(bestJSkinny) << "\n";
}
