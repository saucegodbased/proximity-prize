#define main promoted_second_jet_target_profile_search_hidden_main
#include "promoted_second_jet_target_profile_search_6900.cpp"
#undef main

/*
Exact deterministic target arithmetic for nested weighted raw-shape envelopes

  0 <= S <= sCap,   0 <= R,   R + 2*S <= BCap,

inside the m47/U64/L3757 exact-G source at the worst stratum g=180413.
For every envelope we compare its literal column count with N times its own
published blockwise contact-rank bound.  This is a source-capacity audit only;
it does not assert conormal rank four for any envelope.
*/

struct EnvelopeReceipt {
  int B, s;
  i128 columns, localRank, margin;
};

static EnvelopeReceipt envelope(int B, int s) {
  constexpr int m = 47, U = 64, L = 3757;
  Aff columns{};
  for (int h = 0; h <= s; ++h) {
    Aff c = column_cell(m, B, U, h, 0);
    columns.slope += c.slope;
    columns.intercept += c.intercept;
  }
  Aff rank = rank_affine(m, B, s, U);
  i128 cv = columns.slope * L + columns.intercept;
  i128 rv = rank.slope * L + rank.intercept;
  return {B, s, cv, rv, cv - i128(N) * rv};
}

static Aff rank_layer(int m, int B, int s, int U, int h) {
  Aff src{}, ker{};
  for (int r = 0; r < m; ++r) {
    Aff x = rectangle_affine(r + 1, B - 2*h + 1, h, U - h);
    src.slope += x.slope;
    src.intercept += x.intercept;
    int q = std::max((m-r+1)/2, std::max(0, m-r-(s-h)));
    if (q <= r && m-r+2*h <= B) {
      Aff y = rectangle_affine(r-q+1, B-2*h-q+1,
                               h+q, U-h-q);
      ker.slope += y.slope;
      ker.intercept += y.intercept;
    }
  }
  return {src.slope-ker.slope, src.intercept-ker.intercept};
}

int main() {
  constexpr int m = 47, U = 64, L = 3757;
  const i128 chart = i128(588)*U*U*U*U + i128(1560)*U*U*U*L;
  const i128 exactStrata = N-A+1;
  const i128 allowance = i128(254684620614660120LL);
  const i128 aggregate = exactStrata * chart;

  std::vector<EnvelopeReceipt> receipts;
  for (int B = 0; B <= 16; ++B) {
    for (int s = 0; s <= std::min(8, B/2); ++s) {
      receipts.push_back(envelope(B,s));
    }
  }

  std::cout << "TARGET m 47 U 64 L 3757 gmin " << A
    << " exactStrata " << out128(exactStrata)
    << " oneChart " << out128(chart)
    << " aggregate " << out128(aggregate)
    << " consumerSlack " << out128(allowance-aggregate) << "\n";

  for (auto const& e : receipts) {
    std::cout << "ENVELOPE B " << e.B << " s " << e.s
      << " columns " << out128(e.columns)
      << " localRank " << out128(e.localRank)
      << " margin " << out128(e.margin)
      << " nonnegative " << (e.margin >= 0)
      << " positive " << (e.margin > 0) << "\n";
  }

  std::vector<EnvelopeReceipt> minimalPositive;
  EnvelopeReceipt closestNegative{};
  bool haveClosestNegative = false;
  for (auto const& e : receipts) {
    if (e.margin < 0 &&
        (!haveClosestNegative || e.margin > closestNegative.margin)) {
      closestNegative = e;
      haveClosestNegative = true;
    }
    if (e.margin <= 0) continue;
    bool hasPositiveProperSubenvelope = false;
    for (auto const& f : receipts) {
      if (f.B <= e.B && f.s <= e.s && (f.B < e.B || f.s < e.s) &&
          f.margin > 0) {
        hasPositiveProperSubenvelope = true;
        break;
      }
    }
    if (!hasPositiveProperSubenvelope) minimalPositive.push_back(e);
  }
  std::cout << "MINIMAL_POSITIVE_COUNT " << minimalPositive.size() << "\n";
  for (auto const& e : minimalPositive) {
    std::cout << "MINIMAL_POSITIVE B " << e.B << " s " << e.s
      << " columns " << out128(e.columns)
      << " localRank " << out128(e.localRank)
      << " margin " << out128(e.margin) << "\n";
  }
  std::cout << "CLOSEST_NEGATIVE B " << closestNegative.B
    << " s " << closestNegative.s
    << " columns " << out128(closestNegative.columns)
    << " localRank " << out128(closestNegative.localRank)
    << " margin " << out128(closestNegative.margin) << "\n";

  EnvelopeReceipt full = envelope(16,8);
  std::cout << "FULL_LAYER_BREAKDOWN B 16 s 8\n";
  i128 layerMarginSum = 0;
  for (int h = 0; h <= 8; ++h) {
    Aff c = column_cell(m,16,U,h,0);
    Aff r = rank_layer(m,16,8,U,h);
    i128 cv = c.slope*L+c.intercept;
    i128 rv = r.slope*L+r.intercept;
    i128 mv = cv-i128(N)*rv;
    layerMarginSum += mv;
    std::cout << "S_LAYER h " << h
      << " Rmax " << 16-2*h
      << " columns " << out128(cv)
      << " localRank " << out128(rv)
      << " marginContribution " << out128(mv) << "\n";
  }
  std::cout << "FULL_CHECK columns " << out128(full.columns)
    << " localRank " << out128(full.localRank)
    << " margin " << out128(full.margin)
    << " layerMarginSum " << out128(layerMarginSum) << "\n";

  // Hard controls from the accepted exact arithmetic receipt.
  if (full.columns != i128(65061789117960LL) ||
      full.localRank != i128(248191020) ||
      full.margin != i128(2371080) ||
      chart != i128(1546270015488LL) ||
      aggregate != i128(126379740905865216LL)) return 2;
  if (minimalPositive.size() != 1) return 3;
  if (!haveClosestNegative || closestNegative.B != 16 ||
      closestNegative.s != 7 ||
      closestNegative.margin != i128(-701011338)) return 4;
  return 0;
}
