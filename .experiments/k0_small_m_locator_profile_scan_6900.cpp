#define main promoted_profile_search_hidden_main
#include "promoted_second_jet_target_profile_search_6900.cpp"
#undef main

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

/*
Exhaustive audit of every k=0 source profile with m <= 47 admitted by the
same elementary shape inequalities as k0_rank4_source_search_6900.cpp.

The key question is whether any capacity-positive profile lies in the tiny-m
regime where the literal all-node Hermite locator Omega^(m-3), together with
one active coordinate of weight W, fits below the cutoff m*A.  Such a hit
would replace the open target-uniform four-row theorem by an explicit CRT
witness.  Absence of a hit closes that tempting shortcut exactly.
*/

int main() {
  std::vector<K0Hit> hits;
  std::vector<K0Hit> locatorHits;
  long long inspected = 0;

  for (int m = 2; m <= 47; ++m) {
    for (int s = 1; s <= m / 2; ++s) {
      for (int B = 2 * s; B <= m; ++B) {
        int minU = std::max({m + s, B, 1});
        int maxU = int((i64(m) * A + B - 1) / W);
        for (int U = minU; U <= maxU; ++U) {
          ++inspected;
          K0Hit h = inspect_k0(m, B, s, U);
          if (h.margin <= 0 || h.capSlack < 0) continue;
          if (h.ordinaryProjection >= 2130706433) continue;
          hits.push_back(h);

          // Worst of the four raw boundary-coordinate carriers has one
          // active-variable weight W.  Strict source legality is degree < m*A.
          i128 locatorDegree = i128(m - 3) * N + W;
          if (m >= 3 && locatorDegree < i128(m) * A)
            locatorHits.push_back(h);
        }
      }
    }
  }

  std::sort(hits.begin(), hits.end(), [](auto const &a, auto const &b) {
    if (a.m != b.m) return a.m < b.m;
    if (a.L != b.L) return a.L < b.L;
    if (a.chartCost != b.chartCost) return a.chartCost < b.chartCost;
    return a.margin > b.margin;
  });

  std::cout << "INSPECTED " << inspected << "\n";
  std::cout << "CAPACITY_HITS " << hits.size() << "\n";
  if (!hits.empty()) {
    auto const &h = hits.front();
    std::cout << "FIRST_CAPACITY_HIT m " << h.m << " B " << h.B
      << " s " << h.s << " U " << h.U << " L " << h.L
      << " margin " << out128(h.margin)
      << " chart " << out128(h.chartCost)
      << " projection " << out128(h.ordinaryProjection)
      << " slack " << h.capSlack << "\n";
  }
  std::cout << "FOUR_AXIS_LOCATOR_HITS " << locatorHits.size() << "\n";
  for (size_t i = 0; i < std::min<size_t>(20, locatorHits.size()); ++i) {
    auto const &h = locatorHits[i];
    std::cout << "LOCATOR_HIT m " << h.m << " B " << h.B
      << " s " << h.s << " U " << h.U << " L " << h.L
      << " margin " << out128(h.margin) << "\n";
  }

  for (int m = 3; m <= 12; ++m) {
    i128 locatorDegree = i128(m - 3) * N + W;
    std::cout << "LOCATOR_BUDGET m " << m
      << " degree " << out128(locatorDegree)
      << " cutoff " << out128(i128(m) * A)
      << " slack " << out128(i128(m) * A - locatorDegree) << "\n";
  }
}
