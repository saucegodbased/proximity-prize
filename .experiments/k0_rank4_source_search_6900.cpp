#define main promoted_profile_search_hidden_main
#include "promoted_second_jet_target_profile_search_6900.cpp"
#undef main

/*
Target-6900 source arithmetic for the candidate-major rank-four route.

We deliberately set k=0,n0=1.  Hence reserve(h)=0 for every h, the cutoff
is m*A in every curvature layer, and only the undifferentiated fixed source
is used.  This is a source/degree discriminator only; it does not assert the
rank-four theorem for the resulting contact kernel.
*/

struct K0Hit {
  int m, B, s, U, L;
  i128 margin;
  i128 chartCost;
  i128 ordinaryProjection;
  int capSlack;
};

static K0Hit inspect_k0(int m, int B, int s, int U) {
  Aff rank = rank_affine(m, B, s, U);
  Aff columns{};
  int minSlack = std::numeric_limits<int>::max();
  for (int h = 0; h <= s; ++h) {
    Aff cell = column_cell(m, B, U, h, 0);
    columns.slope += cell.slope;
    columns.intercept += cell.intercept;
    minSlack = std::min(minSlack, cap_slack(m, B, U, h, 0));
  }
  Aff margin{columns.slope - i128(N) * rank.slope,
             columns.intercept - i128(N) * rank.intercept};
  int L = std::max(U, m + B + s);
  if (margin.slope > 0 && margin.slope * L + margin.intercept <= 0) {
    i128 need = (-margin.intercept) / margin.slope + 1;
    if (need > 200000) return {m,B,s,U,0,-1,-1,-1,minSlack};
    L = std::max<i128>(L, need);
  }
  i128 value = margin.slope * L + margin.intercept;
  i128 j = U;
  i128 chart = 588*j*j*j*j + 1560*j*j*j*L;
  i128 projection = 3*(j*j*j + 3*j*j*(L+j));
  return {m,B,s,U,L,value,chart,projection,minSlack};
}

int main(int argc, char **argv) {
  int samples = argc > 1 ? std::stoi(argv[1]) : 1000000;
  int mCap = argc > 2 ? std::stoi(argv[2]) : 320;
  bool terminal = argc > 3 && std::string(argv[3]) == "terminal";
  K0Hit control = inspect_k0(47,16,8,64);
  if (control.L != 3757 || control.margin != i128(2371080) ||
      control.chartCost != i128(1546270015488LL) ||
      control.ordinaryProjection != i128(141643776) ||
      control.capSlack != 0) return 2;
  std::cout << "CONTROL m 47 B 16 s 8 U 64 L " << control.L
    << " margin " << out128(control.margin)
    << " chart " << out128(control.chartCost)
    << " projection " << out128(control.ordinaryProjection)
    << " slack " << control.capSlack << "\n";
  std::mt19937_64 gen(690004);
  std::vector<K0Hit> hits;
  for (int z = 0; z < samples; ++z) {
    int m = 2 + gen()%std::max(1,mCap-1);
    int s = 1 + gen()%std::max(1,m/2);
    int B = 2*s + gen()%std::max(1,m-2*s+1);
    int maxU = int((i64(m)*A+B-1)/W);
    int minU = std::max({m+s,B,1});
    if (minU > maxU) continue;
    int U = minU + gen()%(maxU-minU+1);
    if (terminal && U-B < m+1) continue;
    if (terminal && i64(m)*A-i64(W)*(B+m+1) <= N-A) continue;
    K0Hit h = inspect_k0(m,B,s,U);
    if (h.margin <= 0 || h.capSlack < 0) continue;
    if (h.ordinaryProjection >= 2130706433) continue;
    hits.push_back(h);
  }
  std::sort(hits.begin(), hits.end(), [](auto const &a, auto const &b) {
    if (a.chartCost != b.chartCost) return a.chartCost < b.chartCost;
    if (a.L != b.L) return a.L < b.L;
    return a.margin > b.margin;
  });
  std::cout << "samples " << samples << " hits " << hits.size() << "\n";
  if (!hits.empty()) {
    auto minM = *std::min_element(hits.begin(), hits.end(),
      [](auto const &a, auto const &b) {
        if (a.m != b.m) return a.m < b.m;
        if (a.L != b.L) return a.L < b.L;
        return a.margin > b.margin;
      });
    std::cout << "MIN_M m " << minM.m << " B " << minM.B
      << " s " << minM.s << " U " << minM.U << " L " << minM.L
      << " margin " << out128(minM.margin)
      << " chart " << out128(minM.chartCost) << "\n";
  }
  for (size_t i=0; i<std::min<size_t>(80,hits.size()); ++i) {
    auto const &h=hits[i];
    std::cout << "HIT m " << h.m << " B " << h.B << " s " << h.s
      << " U " << h.U << " L " << h.L
      << " margin " << out128(h.margin)
      << " chart " << out128(h.chartCost)
      << " projection " << out128(h.ordinaryProjection)
      << " slack " << h.capSlack << "\n";
  }
}
