// Independent exhaustive joint-band audit for the W=133225 helper on an
// identity universe of 262143 nodes.  The implementation reuses the exact
// arithmetic primitives from the unrestricted helper checker, but supplies
// a separate main so that *both* necessary band inequalities are applied
// before any expensive exact-stage expansion.
#define IDENTITY_N 262143
#define main unrestricted_helper_main
#include "weighted_helper_unrestricted_m_w133225_6900.cpp"
#undef main

struct JointHit {
  i128 upperMin;
  i128 upperD;
  i128 upperJ;
  uint64_t k;
  uint64_t m;
};

struct AdaptiveStats {
  uint64_t blocks = 0;
  uint64_t rejectedPoints = 0;
  uint64_t exactPoints = 0;
  uint64_t sourceUpperPositive = 0;
  uint64_t dNecessary = 0;
  std::vector<JointHit> hits;
  i128 bestUpperMin = std::numeric_limits<i128>::min();
  JointHit best{};
};

static void adaptive_block(const LatticeTables &tab, uint64_t k,
    const PairInfo &pi, uint64_t left, uint64_t right, AdaptiveStats &out) {
  ++out.blocks;
  const uint64_t BL = left * A, ML = BL / (W - 2);
  const u128 rankLeft = exact_low(tab, left, k) + finite_high(left, k, ML);
  // Target rank is monotone in m and columns are monotone in B.  Therefore
  // this cross-endpoint expression bounds every kernel in [left,right].
  const i128 blockUpper =
      i128(columns_upper(pi, right * A)) - i128(N * rankLeft);
  if (blockUpper <= 0) {
    out.rejectedPoints += right - left + 1;
    return;
  }
  if (left != right) {
    const uint64_t mid = left + (right - left) / 2;
    adaptive_block(tab, k, pi, left, mid, out);
    adaptive_block(tab, k, pi, mid + 1, right, out);
    return;
  }

  ++out.exactPoints;
  const uint64_t m = left, B = m * A, M = B / (W - 2), D = 4 * k;
  const i128 kup = i128(columns_upper(pi, B)) - i128(N * rankLeft);
  if (kup <= 0) return;
  ++out.sourceUpperPositive;
  const Source optimistic{k, m, B, D, M, rankLeft, 0, kup};
  const i128 upperD = kup - i128(band_lower(optimistic, 55, true));
  if (upperD <= 0) return;
  ++out.dNecessary;
  const i128 upperJ = kup - i128(band_lower(optimistic, 211, false));
  const i128 upperMin = std::min(upperD, upperJ);
  if (upperMin > out.bestUpperMin) {
    out.bestUpperMin = upperMin;
    out.best = {upperMin, upperD, upperJ, k, m};
  }
  if (upperJ > 0)
    out.hits.push_back({upperMin, upperD, upperJ, k, m});
}

static void exact_joint_hits(const LatticeTables &tab,
    std::vector<JointHit> &hits, const char *label) {
  std::sort(hits.begin(), hits.end(), [](const auto &x, const auto &y) {
    return x.upperMin > y.upperMin;
  });
  i128 bestExactMin = std::numeric_limits<i128>::min();
  JointHit exactBest{};
  uint64_t exactBoth = 0;
  for (size_t i = 0; i < hits.size(); ++i) {
    const uint64_t k = hits[i].k, m = hits[i].m;
    const uint64_t B = m * A, M = B / (W - 2), D = 4 * k;
    const u128 rank = exact_low(tab, m, k) + finite_high(m, k, M);
    const u128 cols = columns(B, D);
    const Source s{k, m, B, D, M, rank, cols,
                   i128(cols) - i128(N * rank)};
    const i128 dm = s.kernel - i128(band_exact(s, 55, true));
    const i128 jm = s.kernel - i128(band_exact(s, 211, false));
    const i128 mn = std::min(dm, jm);
    if (mn > bestExactMin) {
      bestExactMin = mn;
      exactBest = {mn, dm, jm, k, m};
    }
    if (dm > 0 && jm > 0) {
      ++exactBoth;
      std::cout << "BOTH k=" << k << " m=" << m << " B=" << B
                << " M=" << M << " D=" << D
                << " rank=" << show(rank)
                << " columns=" << show(cols)
                << " kernel=" << showi(s.kernel)
                << " D55margin=" << showi(dm)
                << " J211margin=" << showi(jm) << "\n";
    }
  }
  std::cout << label << " checked=" << hits.size()
            << " both=" << exactBoth
            << " bestMin=" << showi(bestExactMin)
            << " at=" << exactBest.k << "," << exactBest.m
            << " D55margin=" << showi(exactBest.upperD)
            << " J211margin=" << showi(exactBest.upperJ) << "\n";
}

static void scan_clipped_adaptive() {
  const LatticeTables tab(MAX_M + 10);
  AdaptiveStats total;
  const uint64_t kmax = (uint64_t(MAX_M) * A / (W - 2) + 1) / 4;
#pragma omp parallel
  {
    AdaptiveStats local;
#pragma omp for schedule(dynamic, 1)
    for (int64_t kk = 1; kk <= int64_t(kmax); ++kk) {
      const uint64_t k = uint64_t(kk);
      const uint64_t lo = std::max<uint64_t>(1,
          (u128(4 * k - 1) * (W - 2) + A - 1) / A);
      const uint64_t hi = std::min<uint64_t>(MAX_M, 8 * k - 1);
      if (lo <= hi) adaptive_block(tab, k, pair_info(k), lo, hi, local);
    }
#pragma omp critical
    {
      total.blocks += local.blocks;
      total.rejectedPoints += local.rejectedPoints;
      total.exactPoints += local.exactPoints;
      total.sourceUpperPositive += local.sourceUpperPositive;
      total.dNecessary += local.dNecessary;
      total.hits.insert(total.hits.end(), local.hits.begin(), local.hits.end());
      if (local.bestUpperMin > total.bestUpperMin) {
        total.bestUpperMin = local.bestUpperMin;
        total.best = local.best;
      }
    }
  }
  std::cout << "ADAPTIVE_CLIPPED blocks=" << total.blocks
            << " rejectedPoints=" << total.rejectedPoints
            << " exactPoints=" << total.exactPoints
            << " sourceUpperPositive=" << total.sourceUpperPositive
            << " surviveDNecessary=" << total.dNecessary
            << " surviveBothNecessary=" << total.hits.size()
            << " bestUpperMin=" << showi(total.bestUpperMin)
            << " at=" << total.best.k << "," << total.best.m
            << " upperD=" << showi(total.best.upperD)
            << " upperJ=" << showi(total.best.upperJ) << "\n";
  exact_joint_hits(tab, total.hits, "ADAPTIVE_EXACT");
}

static void scan_joint(uint64_t rlo, uint64_t rhi) {
  LatticeTables tab(MAX_M + 10);
  std::vector<JointHit> hits;
  uint64_t tested = 0, sourceUpperPositive = 0, dNecessary = 0;
  i128 bestUpperMin = std::numeric_limits<i128>::min();
  JointHit best{};
  const uint64_t kmax = (uint64_t(MAX_M) * A / (W - 2) + 1) / 4;

#pragma omp parallel
  {
    std::vector<JointHit> localHits;
    uint64_t localTested = 0, localSourcePositive = 0, localDNecessary = 0;
    i128 localBest = std::numeric_limits<i128>::min();
    JointHit localBestHit{};
#pragma omp for schedule(dynamic, 4)
    for (int64_t kk = 1; kk <= int64_t(kmax); ++kk) {
      const uint64_t k = uint64_t(kk);
      const PairInfo pi = pair_info(k);
      const LowPrefixes lpref = low_prefixes(k);
      const uint64_t feasibleLo =
          (u128(4 * k - 1) * (W - 2) + A - 1) / A;
      const uint64_t lo =
          std::max<uint64_t>(feasibleLo, (u128(k) * rlo + 999) / 1000);
      const uint64_t hi =
          std::min<uint64_t>(MAX_M, u128(k) * rhi / 1000);
      if (lo > hi) continue;
      for (uint64_t m = lo; m <= hi; ++m) {
        const uint64_t B = m * A, M = B / (W - 2), D = 4 * k;
        ++localTested;
        // This is a certified lower bound on the clipped low target: it keeps
        // just the base (m-d) copy of each weighted monomial.  It becomes
        // equality at m>=8k-1.  A lower target rank makes `kup` an upper bound
        // on the true kernel, so it is sound for rejection.  Every joint
        // survivor is recomputed with `exact_low` below.
        const u128 low = low_optimistic_lower(lpref, m, D);
        const u128 rank = low + finite_high(m, k, M);
        const i128 kup = i128(columns_upper(pi, B)) - i128(N * rank);
        if (kup <= 0) continue;
        ++localSourcePositive;
        const Source optimistic{k, m, B, D, M, rank, 0, kup};
        const i128 upperD = kup - i128(band_lower(optimistic, 55, true));
        if (upperD <= 0) continue;
        ++localDNecessary;
        const i128 upperJ = kup - i128(band_lower(optimistic, 211, false));
        const i128 upperMin = std::min(upperD, upperJ);
        if (upperMin > localBest) {
          localBest = upperMin;
          localBestHit = {upperMin, upperD, upperJ, k, m};
        }
        if (upperJ > 0)
          localHits.push_back({upperMin, upperD, upperJ, k, m});
      }
    }
#pragma omp critical
    {
      tested += localTested;
      sourceUpperPositive += localSourcePositive;
      dNecessary += localDNecessary;
      hits.insert(hits.end(), localHits.begin(), localHits.end());
      if (localBest > bestUpperMin) {
        bestUpperMin = localBest;
        best = localBestHit;
      }
    }
  }

  std::sort(hits.begin(), hits.end(), [](const auto &x, const auto &y) {
    return x.upperMin > y.upperMin;
  });
  std::cout << "JOINT_FILTER ratioPermille=" << rlo << ".." << rhi
            << " tested=" << tested
            << " sourceUpperPositive=" << sourceUpperPositive
            << " surviveDNecessary=" << dNecessary
            << " surviveBothNecessary=" << hits.size()
            << " bestUpperMin=" << showi(bestUpperMin)
            << " at=" << best.k << "," << best.m
            << " upperD=" << showi(best.upperD)
            << " upperJ=" << showi(best.upperJ) << "\n";

  exact_joint_hits(tab, hits, "JOINT_EXACT");
}

int main(int argc, char **argv) {
  if (argc > 1 && std::string(argv[1]) == "adaptive") {
    scan_clipped_adaptive();
    return 0;
  }
  const uint64_t rlo = argc > 1 ? std::stoull(argv[1]) : 0;
  const uint64_t rhi = argc > 2 ? std::stoull(argv[2]) : 12000000;
  scan_joint(rlo, rhi);
}
