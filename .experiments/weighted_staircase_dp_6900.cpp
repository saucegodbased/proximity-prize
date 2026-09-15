// Exact arithmetic search for monotone terminal staircases at the full
// identity core (n = 262144).  This reuses the independently checked finite
// source/rank/band formulas, but all Johnson- and W-dependent quantities below
// are recomputed for the requested weight.
#define W133226_AUDIT_NO_MAIN
#include "weighted_w133226_cutoff34_full_audit_6900.cpp"
#undef W133226_AUDIT_NO_MAIN

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

constexpr uint64_t STAIR_N = 262144;
static uint64_t stairV = 0;

static i128 stair_johnson_margin(uint64_t v) {
  const uint64_t u = v + 1;
  const i128 inner = i128(A - u) * (A - u)
    - i128(STAIR_N - u) * (W - u);
  return i128(AUDIT_SMALL + 1) * inner
    - i128(u128(STAIR_N - u) * (STAIR_N - W));
}

static uint64_t stair_minimum_v() {
  for (uint64_t v = 0; v < W; ++v)
    if (stair_johnson_margin(v) > 0) return v;
  __builtin_trap();
}

static Source stair_source(uint64_t k, uint64_t m, const PairCoeff &pc) {
  const uint64_t B = m * A, D = 4 * k, M = B / (W - 2);
  const u128 rank = finite_rank_general_fast(m, k, M);
  const u128 columns = pair_eval(pc, B) / (2 * W);
  return {k, m, B, D, 2 * k, M, rank,
    i128(columns) - i128(u128(STAIR_N) * rank)};
}

static u128 stair_two_cap(Flag source, Flag agreement) {
  return ceil_div(u128(STAIR_N - stairV) * (STAIR_N - stairV)
      * mixed(source, agreement, agreement),
    u128(A - stairV) * (A - stairV));
}

static u128 stair_one_cap(Flag source, Flag helper, Flag agreement) {
  return ceil_div(u128(STAIR_N - stairV)
      * mixed(source, helper, agreement), A - stairV);
}

static Coupled stair_coupled_cap(const Source &primary, Flag helper,
    uint64_t restJ, uint64_t restD, uint64_t restT) {
  const Flag restFlag{restJ - restD, restD - restT, restT};
  const Flag restAgreement = audit_agreement_flag(restJ, restD, restT);
  const Flag primaryAgreement = audit_agreement_flag(primary.M,
    primary.D, primary.T);
  const auto rest0 = cumulative_coeff(restAgreement, restAgreement);
  const auto exit0 = cumulative_coeff(helper, primaryAgreement);
  std::array<u128, 3> rest{}, exit{};
  const std::array<uint64_t, 3> total{primary.M, primary.D, primary.T};
  const std::array<uint64_t, 3> cap{restJ, restD, restT};
  u128 numerator = 0;
  for (size_t i = 0; i < 3; ++i) {
    rest[i] = u128(STAIR_N - stairV) * (STAIR_N - stairV) * rest0[i];
    exit[i] = u128(STAIR_N - stairV) * (A - stairV) * exit0[i];
    numerator += exit[i] * total[i];
    if (rest[i] > exit[i])
      numerator += (rest[i] - exit[i]) * std::min(total[i], cap[i]);
  }
  return {numerator,
    ceil_div(numerator, u128(A - stairV) * (A - stairV)), rest, exit};
}

static bool stair_semantic_gate(Flag source, Flag agreement) {
  const u128 curveLeft = u128(AUDIT_SMALL) * (A - stairV);
  const u128 curveRight = u128(STAIR_N - stairV) * agreement.a;
  const u128 surfaceLeft = u128(AUDIT_SMALL)
    * (A - stairV) * (A - stairV);
  const u128 surfaceRight = u128(STAIR_N - stairV)
    * (STAIR_N - stairV) * agreement.a * agreement.a;
  const u128 projection = (agreement.y + agreement.a) * source.a
    + (source.y + source.a) * agreement.a;
  return agreement.a >= AUDIT_SMALL && curveLeft <= curveRight
    && surfaceLeft <= surfaceRight && projection < PRIME;
}

static void inspect_source(uint64_t k, uint64_t m) {
  const PairCoeff pc = pair_coeff(k);
  const Source s = stair_source(k, m, pc);
  std::cout << "SOURCE k=" << k << " m=" << m << " M=" << s.M
    << " D=" << s.D << " T=" << s.T << " rank=" << show(s.rank)
    << " kernel=" << showi(s.kernel) << " flag=" << show(sf(s).z)
    << "," << show(sf(s).y) << "," << show(sf(s).a) << "\n";
  for (uint64_t jet : {48ULL, 64ULL, 96ULL, 128ULL, 160ULL, 192ULL,
      208ULL, 210ULL, 211ULL, 212ULL, 213ULL, 224ULL, 256ULL}) {
    uint64_t lo = 0, hi = std::min<uint64_t>(s.D + 1, 256);
    if (s.kernel <= 0 || joint_band_relaxed_at(s, jet, hi)
        >= u128(s.kernel)) {
      std::cout << "THRESHOLD J=" << jet << " none<=256\n";
      continue;
    }
    while (lo + 1 < hi) {
      const uint64_t mid = (lo + hi) / 2;
      if (joint_band_relaxed_at(s, jet, mid) < u128(s.kernel)) hi = mid;
      else lo = mid;
    }
    std::cout << "THRESHOLD J=" << jet << " minD=" << hi
      << " margin="
      << showi(s.kernel - i128(joint_band_relaxed_at(s, jet, hi)))
      << " previousMargin="
      << showi(s.kernel - i128(joint_band_relaxed_at(s, jet, hi - 1)))
      << "\n";
  }
}

struct StairNode {
  uint64_t J = 0, D = 0, T = 0;
  u128 total = 0;
};

struct StairResult {
  bool valid = false;
  u128 worst = ~u128(0), pathWorst = ~u128(0);
  u128 jetSkinny = 0, derivativeSkinny = 0, helperExit = 0, cleanup = 0;
  uint64_t j0 = 0, d0 = 0;
  std::vector<StairNode> path;
};

static uint64_t relaxed_min_derivative(const Source &helper,
    uint64_t jet, uint64_t maximum) {
  if (helper.kernel <= 0) return maximum + 1;
  if (joint_band_relaxed_at(helper, jet, maximum) >= u128(helper.kernel))
    return maximum + 1;
  uint64_t lo = 0, hi = maximum;
  while (lo + 1 < hi) {
    const uint64_t mid = (lo + hi) / 2;
    if (joint_band_relaxed_at(helper, jet, mid) < u128(helper.kernel))
      hi = mid;
    else
      lo = mid;
  }
  return hi;
}

// Minimax dynamic program for a monotone staircase.  A node (J,D) denotes
// the terminal rectangle J'<=J, D'<=D.  From (J,D) to (J',D') with J'>J and
// D'<D, the uncovered complement is killed exactly by the helper gate
// (J+1,D'+1).  The two skinny endpoints use J<=j0 and D<=d0.
static StairResult staircase_for(const Source &primary, const Source &helper,
    uint64_t j0, uint64_t d0, uint64_t maxJ = 320,
    uint64_t maxD = 100,
    const std::vector<uint64_t> *cachedThreshold = nullptr) {
  StairResult out;
  if (primary.kernel <= 0 || helper.kernel <= 0 || j0 == 0
      || d0 == 0 || j0 >= primary.M) return out;
  maxJ = std::min(maxJ, primary.M);
  maxD = std::min(maxD, primary.D);
  if (maxJ <= j0 || maxD <= d0) return out;

  const Flag pf = sf(primary), hf = sf(helper);
  const Flag pa = audit_agreement_flag(primary.M, primary.D, primary.T);
  const u128 cleanup = corrected_cleanup(STAIR_N, primary);
  const u128 helperExit = stair_one_cap(pf, hf, pa);

  // Honest left skinny: M=j0+1,S=T=j0.  Honest right skinny after a
  // derivative cutoff d0: the semantic reduction only yields S=T=2*d0+1.
  const Flag jetFlag{1, 0, j0};
  const Flag jetAgreement = audit_agreement_flag(j0 + 1, j0, j0);
  const uint64_t skinnyST = 2 * d0 + 1;
  if (skinnyST >= primary.M || skinnyST > primary.D) return out;
  const Flag derivativeFlag{primary.M - skinnyST, 0, skinnyST};
  const Flag derivativeAgreement = audit_agreement_flag(primary.M,
    skinnyST, skinnyST);
  if (!stair_semantic_gate(jetFlag, jetAgreement)
      || !stair_semantic_gate(derivativeFlag, derivativeAgreement)) return out;
  const u128 jetTotal = stair_two_cap(jetFlag, jetAgreement)
    + helperExit + cleanup;
  const u128 derivativeTotal = stair_two_cap(derivativeFlag,
    derivativeAgreement) + helperExit + cleanup;

  // Green-band threshold for each possible predecessor jet coordinate.  The
  // largest derivative coordinate queried is maxD+1.
  std::vector<uint64_t> localThreshold;
  if (!cachedThreshold) {
    localThreshold.assign(maxJ + 2, maxD + 2);
    for (uint64_t jet = j0 + 1; jet <= maxJ + 1; ++jet)
      localThreshold[jet] = relaxed_min_derivative(helper, jet, maxD + 1);
    cachedThreshold = &localThreshold;
  }
  const std::vector<uint64_t> &threshold = *cachedThreshold;

  const u128 INF = ~u128(0);
  const uint64_t dCount = maxD + 1;
  std::vector<u128> transition(dCount, INF);
  std::vector<int64_t> transitionPred(dCount, -2);
  // Per-grid-node DP and predecessor.  Dense storage keeps reconstruction
  // simple and remains tiny (<1 MiB for the ranges used here).
  const uint64_t stride = maxD + 1;
  std::vector<u128> dp((maxJ + 1) * stride, INF);
  std::vector<int64_t> pred((maxJ + 1) * stride, -2);
  auto index = [=](uint64_t J, uint64_t D) { return J * stride + D; };

  u128 bestEnd = INF;
  int64_t bestEndNode = -1;
  for (uint64_t J = j0 + 1; J <= maxJ; ++J) {
    std::vector<u128> rowValue(maxD + 2, INF);
    std::vector<int64_t> rowNode(maxD + 2, -2);
    for (uint64_t D = d0 + 1; D <= maxD; ++D) {
      const uint64_t T = D / 2;
      if (T == 0 || T > primary.T || D > primary.D || D > J) continue;
      const Flag rest{J - D, D - T, T};
      const Flag agreement = audit_agreement_flag(J, D, T);
      if (!stair_semantic_gate(rest, agreement)) continue;
      u128 previous = INF;
      int64_t previousNode = -2;
      // Initial complement gate (j0+1,D+1).
      if (D + 1 >= threshold[j0 + 1]) {
        previous = 0;
        previousNode = -1;
      }
      if (transition[D] < previous) {
        previous = transition[D];
        previousNode = transitionPred[D];
      }
      if (previous == INF) continue;
      const u128 total = stair_coupled_cap(primary, hf, J, D, T).cap
        + cleanup;
      const u128 here = std::max(previous, total);
      const uint64_t at = index(J, D);
      dp[at] = here;
      pred[at] = previousNode;
      rowValue[D] = here;
      rowNode[D] = int64_t(at);
      // Final complement gate (J+1,d0+1).
      if (d0 + 1 >= threshold[J + 1] && here < bestEnd) {
        bestEnd = here;
        bestEndNode = int64_t(at);
      }
    }
    // Only lower-J rows may precede a later rectangle, so delay these range
    // relaxations until the whole current row has been evaluated.
    const uint64_t lower = threshold[J + 1] > 0
      ? threshold[J + 1] - 1 : 0;
    std::vector<u128> suffix(maxD + 3, INF);
    std::vector<int64_t> suffixNode(maxD + 3, -2);
    for (uint64_t D = maxD; D > d0; --D) {
      suffix[D] = suffix[D + 1];
      suffixNode[D] = suffixNode[D + 1];
      if (rowValue[D] < suffix[D]) {
        suffix[D] = rowValue[D];
        suffixNode[D] = rowNode[D];
      }
    }
    for (uint64_t nextD = std::max(d0 + 1, lower);
        nextD < maxD; ++nextD) {
      if (suffix[nextD + 1] < transition[nextD]) {
        transition[nextD] = suffix[nextD + 1];
        transitionPred[nextD] = suffixNode[nextD + 1];
      }
    }
  }
  if (bestEnd == INF) return out;

  out.valid = true;
  out.pathWorst = bestEnd;
  out.jetSkinny = jetTotal;
  out.derivativeSkinny = derivativeTotal;
  out.helperExit = helperExit;
  out.cleanup = cleanup;
  out.j0 = j0;
  out.d0 = d0;
  out.worst = std::max({bestEnd, jetTotal, derivativeTotal});
  for (int64_t at = bestEndNode; at >= 0; at = pred[size_t(at)]) {
    const uint64_t J = uint64_t(at) / stride;
    const uint64_t D = uint64_t(at) % stride;
    const uint64_t T = D / 2;
    out.path.push_back({J, D, T,
      stair_coupled_cap(primary, hf, J, D, T).cap + cleanup});
  }
  std::reverse(out.path.begin(), out.path.end());
  return out;
}

struct PrimaryProxy {
  Source p{};
  u128 score = ~u128(0);
};

static std::vector<PrimaryProxy> primary_shortlist(const Source &helper,
    size_t keep = 80) {
  std::vector<PrimaryProxy> best;
  const Flag hf = sf(helper);
  for (uint64_t k = 15; k <= 220; ++k) {
    const PairCoeff pc = pair_coeff(k);
    for (uint64_t m = std::max<uint64_t>(1, 8 * k - 1);
        m <= std::min<uint64_t>(11810, 12 * k); ++m) {
      const Source p = stair_source(k, m, pc);
      if (p.kernel <= 0 || p.M < 224 || p.D < 64 || p.T < 28) continue;
      const Flag pf = sf(p);
      const Flag pa = audit_agreement_flag(p.M, p.D, p.T);
      const u128 cleanup = corrected_cleanup(STAIR_N, p);
      const u128 exit = stair_one_cap(pf, hf, pa);
      // Three points sample a staircase rather than assuming the retired
      // two-arm shape.  Skinny charges are included so a huge helper flag
      // cannot look artificially cheap.
      u128 score = cleanup + std::max({
        stair_coupled_cap(p, hf, 176, 54, 27).cap,
        stair_coupled_cap(p, hf, 200, 36, 18).cap,
        stair_coupled_cap(p, hf, 216, 16, 8).cap});
      const Flag jf{1, 0, 63};
      const Flag ja = audit_agreement_flag(64, 63, 63);
      const Flag df{p.M - 21, 0, 21};
      const Flag da = audit_agreement_flag(p.M, 21, 21);
      score = std::max(score, cleanup + exit + stair_two_cap(jf, ja));
      score = std::max(score, cleanup + exit + stair_two_cap(df, da));
      best.push_back({p, score});
    }
  }
  std::sort(best.begin(), best.end(), [](const auto &a, const auto &b) {
    return a.score < b.score;
  });
  if (best.size() > keep) best.resize(keep);
  return best;
}

static void print_stair_result(const Source &primary, const Source &helper,
    const StairResult &r, const char *label) {
  std::cout << label << " status=" << (r.valid ? "VALID" : "INVALID")
    << " p=" << primary.k << "," << primary.m << "," << primary.M
    << "," << primary.D << " pKernel=" << showi(primary.kernel)
    << " h=" << helper.k << "," << helper.m << "," << helper.M
    << "," << helper.D << " hKernel=" << showi(helper.kernel);
  if (!r.valid) { std::cout << "\n"; return; }
  std::cout << " j0=" << r.j0 << " d0=" << r.d0
    << " cleanup=" << show(r.cleanup) << " exit=" << show(r.helperExit)
    << " jet=" << show(r.jetSkinny)
    << " derivative=" << show(r.derivativeSkinny)
    << " pathWorst=" << show(r.pathWorst) << " worst=" << show(r.worst)
    << " margin=" << showi(i128(AUDIT_CORE_FLOOR) - i128(r.worst))
    << " arms=";
  for (const auto &node : r.path)
    std::cout << "(" << node.J << "," << node.D << "," << node.T
      << ":" << show(node.total) << ")";
  std::cout << "\n";
}

static void search_fixed_helper(uint64_t hk, uint64_t hm) {
  const Source helper = stair_source(hk, hm, pair_coeff(hk));
  const auto shortlist = primary_shortlist(helper);
  std::vector<uint64_t> threshold(322, 102);
  for (uint64_t jet = 1; jet <= 321; ++jet)
    threshold[jet] = relaxed_min_derivative(helper, jet, 101);
  std::cout << "SHORTLIST count=" << shortlist.size() << " helper=" << hk
    << "," << hm << "\n";
  StairResult global;
  Source bestPrimary{};
  for (const PrimaryProxy &candidate : shortlist) {
    for (uint64_t j0 = 56; j0 <= 63; ++j0) {
      for (uint64_t d0 = 7; d0 <= 24; ++d0) {
        const StairResult r = staircase_for(candidate.p, helper, j0, d0,
          320, 100, &threshold);
        if (r.valid && (!global.valid || r.worst < global.worst)) {
          global = r;
          bestPrimary = candidate.p;
          print_stair_result(bestPrimary, helper, global, "IMPROVE");
        }
      }
    }
  }
  print_stair_result(bestPrimary, helper, global, "BEST");
}

static void scan_source_existence() {
  Source global{}, primary{};
  uint64_t positives = 0, primaryPositives = 0;
  i128 globalKernel = std::numeric_limits<i128>::min();
  i128 primaryKernel = std::numeric_limits<i128>::min();
  #pragma omp parallel
  {
    Source local{}, localPrimary{};
    uint64_t localPositives = 0, localPrimaryPositives = 0;
    i128 localKernel = std::numeric_limits<i128>::min();
    i128 localPrimaryKernel = std::numeric_limits<i128>::min();
    #pragma omp for schedule(dynamic)
    for (int64_t signedK = 1; signedK <= int64_t(11810 / 8); ++signedK) {
      const uint64_t k = uint64_t(signedK);
      const PairCoeff pc = pair_coeff(k);
      const uint64_t lo = std::max<uint64_t>(1, 8 * k - 1);
      const uint64_t hi = std::min<uint64_t>(11810, 12 * k);
      for (uint64_t m = lo; m <= hi; ++m) {
        const Source s = stair_source(k, m, pc);
        if (s.kernel > localKernel) { localKernel = s.kernel; local = s; }
        if (s.kernel > 0) ++localPositives;
        if (k <= 400 && s.M >= 64 && s.D >= 14) {
          if (s.kernel > localPrimaryKernel) {
            localPrimaryKernel = s.kernel;
            localPrimary = s;
          }
          if (s.kernel > 0) ++localPrimaryPositives;
        }
      }
    }
    #pragma omp critical
    {
      positives += localPositives;
      primaryPositives += localPrimaryPositives;
      if (localKernel > globalKernel) {
        globalKernel = localKernel;
        global = local;
      }
      if (localPrimaryKernel > primaryKernel) {
        primaryKernel = localPrimaryKernel;
        primary = localPrimary;
      }
    }
  }
  std::cout << "SOURCE_FRONTIER W=" << W << " positives=" << positives
    << " best=" << global.k << "," << global.m << "," << global.M
    << "," << global.D << " kernel=" << showi(globalKernel)
    << " primaryPositives=" << primaryPositives << " bestPrimary="
    << primary.k << "," << primary.m << "," << primary.M << ","
    << primary.D << " primaryKernel=" << showi(primaryKernel) << "\n";
}

static void audit_compressed_w133233() {
  if (W != 133233) {
    std::cerr << "compressed audit is only for W=133233\n";
    return;
  }
  const Source p = stair_source(64, 575, pair_coeff(64));
  const Source h = stair_source(1312, 11810, pair_coeff(1312));
  const Flag pf = sf(p), hf = sf(h);
  const Flag pa = audit_agreement_flag(p.M, p.D, p.T);
  const u128 cleanup = corrected_cleanup(STAIR_N, p);
  const u128 helperExit = stair_one_cap(pf, hf, pa);
  const u128 helperProjection = (hf.y + hf.a) * pf.a
    + (pf.y + pf.a) * hf.a;
  std::cout << "AUDIT_SOURCE role=primary k=" << p.k << " m=" << p.m
    << " B=" << p.B << " M=" << p.M << " D=" << p.D
    << " T=" << p.T << " rank=" << show(p.rank) << " columns="
    << show(u128(p.kernel) + u128(STAIR_N) * p.rank) << " kernel="
    << showi(p.kernel) << " flag=" << show(pf.z) << "," << show(pf.y)
    << "," << show(pf.a) << "\n";
  std::cout << "AUDIT_SOURCE role=helper k=" << h.k << " m=" << h.m
    << " B=" << h.B << " M=" << h.M << " D=" << h.D
    << " T=" << h.T << " rank=" << show(h.rank) << " columns="
    << show(u128(h.kernel) + u128(STAIR_N) * h.rank) << " kernel="
    << showi(h.kernel) << " flag=" << show(hf.z) << "," << show(hf.y)
    << "," << show(hf.a) << "\n";
  for (auto [J, D] : {std::pair<uint64_t,uint64_t>{64,56},
      {209,15}, {213,11}}) {
    const u128 exact = joint_band_exact_at(h, J, D);
    const u128 relaxed = joint_band_relaxed_at(h, J, D);
    std::cout << "AUDIT_GATE J=" << J << " D=" << D
      << " exact=" << show(exact) << " relaxed=" << show(relaxed)
      << " relaxedMargin=" << showi(h.kernel - i128(relaxed)) << "\n";
  }
  auto terminal = [&](const char *name, uint64_t J, uint64_t D,
      uint64_t T, bool coupled) {
    const Flag source{J-D,D-T,T};
    const Flag agreement = audit_agreement_flag(J,D,T);
    const u128 projection = (agreement.y+agreement.a)*source.a
      +(source.y+source.a)*agreement.a;
    const u128 curveMargin = u128(STAIR_N-stairV)*agreement.a
      -u128(AUDIT_SMALL)*(A-stairV);
    const u128 surfaceMargin = u128(STAIR_N-stairV)*(STAIR_N-stairV)
      *agreement.a*agreement.a
      -u128(AUDIT_SMALL)*(A-stairV)*(A-stairV);
    const u128 active = coupled
      ? stair_coupled_cap(p,hf,J,D,T).cap
      : stair_two_cap(source,agreement)+helperExit;
    const u128 total = active+cleanup;
    std::cout << "AUDIT_TERMINAL name=" << name << " cumulative=" << J
      << "," << D << "," << T << " source=" << show(source.z) << ","
      << show(source.y) << "," << show(source.a) << " agreement="
      << show(agreement.z) << "," << show(agreement.y) << ","
      << show(agreement.a) << " projection=" << show(projection)
      << " projectionMargin=" << showi(i128(PRIME)-i128(projection))
      << " curveMargin=" << show(curveMargin)
      << " surfaceMargin=" << show(surfaceMargin)
      << " active=" << show(active) << " cleanup=" << show(cleanup)
      << " total=" << show(total) << " endpointMargin="
      << showi(i128(AUDIT_CORE_FLOOR)-i128(total)) << "\n";
  };
  terminal("rectangle-A",208,55,27,true);
  terminal("rectangle-B",212,14,7,true);
  terminal("jet<=63",64,63,63,false);
  terminal("derivative<=10",p.M,21,21,false);
  std::cout << "AUDIT_COMMON v=" << stairV << " johnsonMargin="
    << showi(stair_johnson_margin(stairV)) << " helperExit="
    << show(helperExit) << " cleanup=" << show(cleanup)
    << " helperProjection=" << show(helperProjection)
    << " helperProjectionMargin="
    << showi(i128(PRIME)-i128(helperProjection)) << "\n";
}

int main(int argc, char **argv) {
  W = argc > 1 ? std::stoull(argv[1]) : 133233;
  stairV = stair_minimum_v();
  std::cout << "PARAM W=" << W << " n=" << STAIR_N << " v=" << stairV
    << " johnsonMargin=" << showi(stair_johnson_margin(stairV)) << "\n";
  const uint64_t k = argc > 2 ? std::stoull(argv[2]) : 1312;
  const uint64_t m = argc > 3 ? std::stoull(argv[3]) : 11810;
  if (argc > 4 && std::string(argv[4]) == "inspect")
    inspect_source(k, m);
  else if (argc > 4 && std::string(argv[4]) == "source")
    scan_source_existence();
  else if (argc > 4 && std::string(argv[4]) == "audit233")
    audit_compressed_w133233();
  else if (argc > 8 && std::string(argv[4]) == "fixed") {
    const uint64_t pk = std::stoull(argv[5]);
    const uint64_t pm = std::stoull(argv[6]);
    const uint64_t j0 = std::stoull(argv[7]);
    const uint64_t d0 = std::stoull(argv[8]);
    const Source helper = stair_source(k, m, pair_coeff(k));
    const Source primary = stair_source(pk, pm, pair_coeff(pk));
    const StairResult r = staircase_for(primary, helper, j0, d0);
    print_stair_result(primary, helper, r, "FIXED");
  }
  else if (argc > 9 && std::string(argv[4]) == "terminal") {
    const uint64_t pk = std::stoull(argv[5]);
    const uint64_t pm = std::stoull(argv[6]);
    const uint64_t J = std::stoull(argv[7]);
    const uint64_t D = std::stoull(argv[8]);
    const uint64_t T = std::stoull(argv[9]);
    const Source helper = stair_source(k, m, pair_coeff(k));
    const Source primary = stair_source(pk, pm, pair_coeff(pk));
    const u128 total = stair_coupled_cap(primary, sf(helper), J, D, T).cap
      + corrected_cleanup(STAIR_N, primary);
    std::cout << "TERMINAL J=" << J << " D=" << D << " T=" << T
      << " total=" << show(total) << " margin="
      << showi(i128(AUDIT_CORE_FLOOR) - i128(total)) << "\n";
  }
  else if (argc > 6 && std::string(argv[4]) == "gate") {
    const uint64_t J = std::stoull(argv[5]);
    const uint64_t D = std::stoull(argv[6]);
    const Source helper = stair_source(k, m, pair_coeff(k));
    const u128 exact = joint_band_exact_at(helper, J, D);
    const u128 relaxed = joint_band_relaxed_at(helper, J, D);
    std::cout << "GATE J=" << J << " D=" << D
      << " exact=" << show(exact) << " relaxed=" << show(relaxed)
      << " exactMargin=" << showi(helper.kernel - i128(exact))
      << " relaxedMargin=" << showi(helper.kernel - i128(relaxed))
      << "\n";
  }
  else
    search_fixed_helper(k, m);
}
