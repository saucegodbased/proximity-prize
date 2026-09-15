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

static u128 active_fibres_literal(uint64_t C,uint64_t E) {
  u128 out=0;
  for(uint64_t t=0;t<=E/2;++t) {
    if(u128(W-2)*t>=C)break;
    const uint64_t base=C-(W-2)*t;
    const uint64_t r=std::min(E-2*t,(base-1)/(W-1));
    const uint64_t q=(base-1)/W,rem=(base-1)%W;
    const uint64_t extra=r>=W-rem?r-(W-rem)+1:0;
    out+=u128(r+1)*(q+1)+extra-s1(r);
  }
  return out;
}

// Exact closed evaluation of the active-fibre count used by the already
// formal stage-band upper theorem.
static u128 active_fibres_formula(uint64_t C,uint64_t E) {
  if(E>=W||u128(C)<=u128(W-1)*E)return active_fibres_literal(C,E);
  const uint64_t h=E/2,n=h+1;
  const u128 st=s1(h),st2=s2(h);
  const uint64_t Q=(C-1)/W,rem=(C-1)%W;
  u128 out=u128(E+1)*(Q+1)*n-
    (u128(E+1)+u128(2)*(Q+1))*st+2*st2;
  out-=(u128(n)*(u128(E)*E+E)-u128(4*E+2)*st+4*st2)/2;
  const uint64_t wrap=(W-rem+1)/2;
  if(wrap<=h) {
    const uint64_t count=h-wrap+1;
    out+=u128(count)*(E+1)-u128(wrap+h)*count;
  }
  const uint64_t extra=E+rem+1>W?E+rem+1-W:0;
  if(extra)out+=u128(extra)*(std::min(h,wrap-1)+1);
  return out;
}

static u128 active_band_upper(const Source&s,uint64_t cap,bool derivative) {
  const uint64_t rho=derivative?cap+1:2;
  const uint64_t g=derivative?(W-2)*((rho+1)/2):(W-2)*(cap+1);
  u128 out=0;
  for(uint64_t j=1;j*rho<=s.D;++j) {
    const u128 spent=u128(j)*g+u128(j-1)*DELTA;
    if(spent>=s.B)break;
    out+=u128(DELTA)*active_fibres_formula(s.B-uint64_t(spent),s.D-j*rho);
  }
  return out;
}

struct ScanFlag {u128 z,y,a;};
static ScanFlag source_flag(const Source&s) {
  return {s.M-s.D,s.D/2,s.D/2};
}
static ScanFlag agreement_flag(uint64_t M,uint64_t D,uint64_t T) {
  return {1+u128(W)*(2*(M-D)-1),u128(2)*W*(D-T)+W,
    u128(2)*W*(T-1)};
}
static u128 scan_flag_mixed(ScanFlag p,ScanFlag q,ScanFlag r) {
  return p.a*q.a*r.a+p.z*q.a*r.a+q.z*p.a*r.a+r.z*p.a*q.a+
    p.y*q.a*r.a+q.y*p.a*r.a+r.y*p.a*q.a+
    p.a*q.y*r.y+q.a*p.y*r.y+r.a*p.y*q.y+
    p.z*q.y*r.a+p.z*r.y*q.a+q.z*p.y*r.a+q.z*r.y*p.a+
    r.z*p.y*q.a+r.z*q.y*p.a;
}

static void formal_cap_hits(const LatticeTables&tab,
    const std::vector<JointHit>&hits,uint64_t jCap,uint64_t dCap,
    const char*label) {
  uint64_t formalBoth=0; i128 bestMin=std::numeric_limits<i128>::min();
  JointHit best{};u128 bestExitCost=~u128(0);JointHit bestExit{};
  const ScanFlag primary{496,122,122};
  const ScanFlag primaryAgreement=agreement_flag(740,244,122);
  for(const JointHit&hit:hits) {
    const uint64_t k=hit.k,m=hit.m,B=m*A,M=B/(W-2),D=4*k;
    const u128 rank=exact_low(tab,m,k)+finite_high(m,k,M);
    const u128 columnLower=pair_eval(pair_info(k),B)/(2*W);
    const i128 kernel=i128(columnLower)-i128(N*rank);
    if(kernel<=0)continue;
    const Source s{k,m,B,D,M,rank,columnLower,kernel};
    const i128 jm=kernel-i128(active_band_upper(s,jCap,false));
    const i128 dm=kernel-i128(active_band_upper(s,dCap,true));
    if(jm<=0||dm<=0)continue;
    ++formalBoth;const i128 mn=std::min(jm,dm);
    if(mn>bestMin){bestMin=mn;best={mn,dm,jm,k,m};}
    const u128 ec=scan_flag_mixed(primary,source_flag(s),primaryAgreement);
    if(ec<bestExitCost){bestExitCost=ec;bestExit={mn,dm,jm,k,m};}
  }
  std::cout<<label<<" formalBoth="<<formalBoth<<" bestMin="<<showi(bestMin)
    <<" bestAt="<<best.k<<","<<best.m<<" Dmargin="<<showi(best.upperD)
    <<" Jmargin="<<showi(best.upperJ)<<" bestExitMixed="<<show(bestExitCost)
    <<" bestExitAt="<<bestExit.k<<","<<bestExit.m
    <<" bestExitDmargin="<<showi(bestExit.upperD)
    <<" bestExitJmargin="<<showi(bestExit.upperJ)<<"\n";
}

struct AdaptiveStats {
  uint64_t blocks = 0;
  uint64_t rejectedPoints = 0;
  uint64_t exactPoints = 0;
  uint64_t sourceUpperPositive = 0;
  uint64_t dNecessary = 0;
  uint64_t minSourceK = UINT64_MAX;
  uint64_t maxSourceK = 0;
  std::vector<JointHit> hits;
  i128 bestUpperMin = std::numeric_limits<i128>::min();
  JointHit best{};
};

static void adaptive_block(const LatticeTables &tab, uint64_t k,
    const PairInfo &pi, uint64_t left, uint64_t right, AdaptiveStats &out,
    uint64_t jCap, uint64_t dCap) {
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
    adaptive_block(tab, k, pi, left, mid, out,jCap,dCap);
    adaptive_block(tab, k, pi, mid + 1, right, out,jCap,dCap);
    return;
  }

  ++out.exactPoints;
  const uint64_t m = left, B = m * A, M = B / (W - 2), D = 4 * k;
  const i128 kup = i128(columns_upper(pi, B)) - i128(N * rankLeft);
  if (kup <= 0) return;
  ++out.sourceUpperPositive;
  out.minSourceK=std::min(out.minSourceK,k);
  out.maxSourceK=std::max(out.maxSourceK,k);
  const Source optimistic{k, m, B, D, M, rankLeft, 0, kup};
  const i128 upperD = kup - i128(band_lower(optimistic, dCap, true));
  if (upperD <= 0) return;
  ++out.dNecessary;
  const i128 upperJ = kup - i128(band_lower(optimistic, jCap, false));
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

static void scan_clipped_adaptive(uint64_t jCap=211,uint64_t dCap=55) {
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
      if (lo <= hi) adaptive_block(tab, k, pair_info(k), lo, hi, local,jCap,dCap);
    }
#pragma omp critical
    {
      total.blocks += local.blocks;
      total.rejectedPoints += local.rejectedPoints;
      total.exactPoints += local.exactPoints;
      total.sourceUpperPositive += local.sourceUpperPositive;
      total.dNecessary += local.dNecessary;
      total.minSourceK=std::min(total.minSourceK,local.minSourceK);
      total.maxSourceK=std::max(total.maxSourceK,local.maxSourceK);
      total.hits.insert(total.hits.end(), local.hits.begin(), local.hits.end());
      if (local.bestUpperMin > total.bestUpperMin) {
        total.bestUpperMin = local.bestUpperMin;
        total.best = local.best;
      }
    }
  }
  std::cout << "ADAPTIVE_CLIPPED J="<<jCap<<" D="<<dCap
            << " blocks=" << total.blocks
            << " rejectedPoints=" << total.rejectedPoints
            << " exactPoints=" << total.exactPoints
            << " sourceUpperPositive=" << total.sourceUpperPositive
            << " sourceK="<<total.minSourceK<<".."<<total.maxSourceK
            << " surviveDNecessary=" << total.dNecessary
            << " surviveBothNecessary=" << total.hits.size()
            << " bestUpperMin=" << showi(total.bestUpperMin)
            << " at=" << total.best.k << "," << total.best.m
            << " upperD=" << showi(total.best.upperD)
            << " upperJ=" << showi(total.best.upperJ) << "\n";
  if(jCap==211&&dCap==55)
    exact_joint_hits(tab, total.hits, "ADAPTIVE_EXACT");
}

static void scan_joint(uint64_t rlo, uint64_t rhi,
    uint64_t jCap=211, uint64_t dCap=55) {
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
        const i128 upperD = kup - i128(band_lower(optimistic, dCap, true));
        if (upperD <= 0) continue;
        ++localDNecessary;
        const i128 upperJ = kup - i128(band_lower(optimistic, jCap, false));
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
  std::cout << "JOINT_FILTER J=" << jCap << " D=" << dCap
            << " ratioPermille=" << rlo << ".." << rhi
            << " tested=" << tested
            << " sourceUpperPositive=" << sourceUpperPositive
            << " surviveDNecessary=" << dNecessary
            << " surviveBothNecessary=" << hits.size()
            << " bestUpperMin=" << showi(bestUpperMin)
            << " at=" << best.k << "," << best.m
            << " upperD=" << showi(best.upperD)
            << " upperJ=" << showi(best.upperJ) << "\n";

  formal_cap_hits(tab,hits,jCap,dCap,"FORMAL_CAP");
  // Preserve the literal exact-stage detail for the canonical audit.
  if(jCap==211 && dCap==55) exact_joint_hits(tab, hits, "JOINT_EXACT");
}

int main(int argc, char **argv) {
  if (argc > 1 && std::string(argv[1]) == "adaptive") {
    scan_clipped_adaptive(argc>2?std::stoull(argv[2]):211,
      argc>3?std::stoull(argv[3]):55);
    return 0;
  }
  const uint64_t rlo = argc > 1 ? std::stoull(argv[1]) : 0;
  const uint64_t rhi = argc > 2 ? std::stoull(argv[2]) : 12000000;
  const uint64_t jCap = argc > 3 ? std::stoull(argv[3]) : 211;
  const uint64_t dCap = argc > 4 ? std::stoull(argv[4]) : 55;
  scan_joint(rlo, rhi,jCap,dCap);
}
