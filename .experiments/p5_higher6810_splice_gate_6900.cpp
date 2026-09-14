#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <utility>
#include <vector>

using i64 = std::int64_t;
using i128 = __int128_t;

namespace {

constexpr i64 N = 262144;
constexpr i64 W = 131071;
constexpr i64 targetAgreement = 180413;
constexpr i64 reserveS = targetAgreement - (W - 2); // 49344

constexpr i64 higherContact = 113;
constexpr i64 higherMain = 20486222;
constexpr i64 higherSlope = 34;
constexpr i64 higherMiddle = 156;
constexpr i64 higherTotal = 157823;

std::string decimal(i128 x) {
  if (x == 0) return "0";
  const bool negative = x < 0;
  if (negative) x = -x;
  std::string answer;
  while (x != 0) {
    answer.push_back(static_cast<char>('0' + x % 10));
    x /= 10;
  }
  if (negative) answer.push_back('-');
  std::reverse(answer.begin(), answer.end());
  return answer;
}

// Strict-cutoff slack for the complete nonzero S-layer of the target-native
// k=1,n0=2 P5 source after restoring contact higherContact with the full
// node locator.  A nonnegative answer is exactly the strict-box fit test.
i64 layerFitSlack(i64 m, i64 h) {
  const i64 cutoff = m * targetAgreement - reserveS - (W - 2) * h;
  const i64 locatorPower = std::max<i64>(0, higherContact - m + h);
  return higherMain - cutoff - N * locatorPower;
}

struct Affine {
  i128 slope = 0;
  i128 intercept = 0;
};

i128 triangularCount(i64 c) {
  if (c < 0) return 0;
  return i128(c + 1) * (c + 2) / 2;
}

i128 triangularMoment(i64 c) {
  if (c < 0) return 0;
  return i128(c) * (c + 1) * (c + 2) / 3;
}

// Count and sum i+j over 0<=i<a, 0<=j<b, i+j<=cap.
std::pair<i128, i128> triangleRectangle(i64 a, i64 b, i64 cap) {
  if (a <= 0 || b <= 0 || cap < 0) return {0, 0};
  const i128 count = triangularCount(cap) - triangularCount(cap - a) -
    triangularCount(cap - b) + triangularCount(cap - a - b);
  const i128 moment = triangularMoment(cap) -
    (triangularMoment(cap - a) + i128(a) * triangularCount(cap - a)) -
    (triangularMoment(cap - b) + i128(b) * triangularCount(cap - b)) +
    (triangularMoment(cap - a - b) +
      i128(a + b) * triangularCount(cap - a - b));
  return {count, moment};
}

Affine rectangleAffine(i64 a, i64 b, i64 offset, i64 cap) {
  const auto [count, moment] = triangleRectangle(a, b, cap);
  return {count, count * (1 - offset) - moment};
}

// Published clipped target-rank receipt for the promoted second-jet source.
Affine rankAffine(int m, int B, int s, int U) {
  Affine source, kernel;
  for (int r = 0; r < m; ++r) {
    for (int h = 0; h <= s; ++h) {
      const auto x = rectangleAffine(r + 1, B - 2 * h + 1, h, U - h);
      source.slope += x.slope;
      source.intercept += x.intercept;
      const int q = std::max((m - r + 1) / 2,
        std::max(0, m - r - (s - h)));
      if (q <= r && m - r + 2 * h <= B) {
        const auto y = rectangleAffine(r - q + 1, B - 2 * h - q + 1,
          h + q, U - h - q);
        kernel.slope += y.slope;
        kernel.intercept += y.intercept;
      }
    }
  }
  return {source.slope - kernel.slope, source.intercept - kernel.intercept};
}

i128 sum1(i64 n) { return n < 0 ? 0 : i128(n) * (n + 1) / 2; }
i128 sum2(i64 n) {
  return n < 0 ? 0 : i128(n) * (n + 1) * (2 * n + 1) / 6;
}
i128 sum3(i64 n) { const i128 x = sum1(n); return x * x; }

std::pair<i128, i128> fullTRange(i64 base, int R, int T) {
  if (T < 0 || R < 0) return {0, 0};
  const int u = std::min(R, T);
  const i128 p1 = sum1(u), p2 = sum2(u), p3 = sum3(u), count = u + 1;
  const i128 sumT1 = p2 + p1;
  const i128 sumT2T = p3 + p2;
  i128 S = base * (p1 + count) - i128(2 * W - 1) * sumT1 / 2;
  i128 TS = base * sumT1 - i128(2 * W - 1) * sumT2T / 2;
  if (T > u) {
    const i64 lo = u + 1, hi = T, count2 = hi - lo + 1;
    const i128 st = sum1(hi) - sum1(lo - 1);
    const i128 st2 = sum2(hi) - sum2(lo - 1);
    const i128 aa = R + 1, rr = i128(R) * (R + 1) / 2;
    S += i128(count2) * (aa * base + rr) - aa * W * st;
    TS += (aa * base + rr) * st - aa * W * st2;
  }
  return {S, TS};
}

Affine columnCell(int m, int B, int U, int h, int reserve) {
  const i64 cutoff = i64(m) * targetAgreement - i64(reserve) * reserveS;
  const i64 base = cutoff - i64(W - 2) * h;
  const int R = B - 2 * h;
  if (base <= 0 || R < 0 || U < h) return {};
  const i64 q = (base - 1) / W;
  const int T = std::min<i64>(U - h, q);
  auto [S, TS] = fullTRange(base, R, T);
  const int tb = static_cast<int>(q + 1);
  if (tb <= U - h) {
    const i64 remainder = (base - 1) - q * W;
    const int lo = static_cast<int>(W - remainder);
    const int hi = std::min(R, tb);
    if (lo <= hi) {
      const i128 count = hi - lo + 1;
      const i128 extra = count * (count + 1) / 2;
      S += extra;
      TS += i128(tb) * extra;
    }
  }
  return {S, i128(1 - h) * S - TS};
}

int capSlack(int m, int B, int U, int reserve) {
  const i64 cutoff = i64(m) * targetAgreement - i64(reserve) * reserveS;
  return static_cast<int>((cutoff + B - 1) / W) - U;
}

struct SourceBest {
  i128 margin = -(i128(1) << 126);
  i128 slope = 0;
  int B = 0;
  int U = 0;
  int L = 0;
};

// Exhaust the cap-matched closed-form source receipt with s=h.  For fixed
// m,B,s,U its margin is affine in L, so the two legal endpoints are enough.
SourceBest bestCapMatchedSource(int m, int h) {
  const int s = h;
  SourceBest best;
  for (int B = 2 * s; B <= higherSlope + 2 * h; ++B) {
    for (int U = m + s; U <= higherMiddle + h; ++U) {
      const Affine rank = rankAffine(m, B, s, U);
      Affine columns;
      bool valid = true;
      for (int layer = 0; layer <= s; ++layer) {
        // k=1,n0=2: reserve 0 on layer 0 and reserve 1 thereafter.
        const int reserve = layer == 0 ? 0 : 1;
        if (capSlack(m, B, U, reserve) < 0) {
          valid = false;
          break;
        }
        const Affine cell = columnCell(m, B, U, layer, reserve);
        columns.slope += cell.slope;
        columns.intercept += cell.intercept;
      }
      if (!valid) continue;
      const i128 slope = columns.slope - i128(N) * rank.slope;
      const i128 intercept = columns.intercept - i128(N) * rank.intercept;
      const int minL = std::max({U, m + B + s});
      const int maxL = higherTotal + h;
      if (minL > maxL) continue;
      for (const int L : {minL, maxL}) {
        const i128 margin = slope * L + intercept;
        if (margin > best.margin) best = {margin, slope, B, U, L};
      }
    }
  }
  return best;
}

} // namespace

int main() {
  std::vector<std::pair<int, int>> fits;
  for (int m = 1; m <= 500; ++m) {
    for (int h = 2; h < m; ++h) {
      if (m * targetAgreement - reserveS - (W - 2) * h > 0 &&
          layerFitSlack(m, h) >= 0) {
        fits.emplace_back(m, h);
      }
    }
  }
  assert((fits == std::vector<std::pair<int, int>>{{115, 2}, {116, 3}}));
  std::cout << "COMPLETE_LAYER_FITS";
  for (const auto& [m, h] : fits) {
    std::cout << " (m=" << m << ",h=" << h
              << ",slack=" << layerFitSlack(m, h) << ")";
  }
  std::cout << '\n';

  for (const auto& [m, h] : fits) {
    const SourceBest best = bestCapMatchedSource(m, h);
    std::cout << "BEST_SOURCE m=" << m << " s=h=" << h
              << " margin=" << decimal(best.margin)
              << " slope=" << decimal(best.slope)
              << " B=" << best.B << " U=" << best.U << " L=" << best.L
              << '\n';
    assert(best.margin < 0);
  }

  constexpr i64 full187M = 60;
  constexpr i64 full187Main = full187M * targetAgreement;
  constexpr i64 full187Locator = higherContact - full187M;
  constexpr i64 full187Used = full187Main + N * full187Locator;
  constexpr i64 full187Slack = higherMain - full187Used;
  static_assert(full187Slack == -4232190);
  std::cout << "FULL187_DIRECT locator=" << full187Locator
            << " used=" << full187Used << " slack=" << full187Slack << '\n';
  std::cout << "FULL187_BEST_EXTRACTION_PENALTY_PER_ORDER=" << N - W << '\n';

  // Accepted Higher6810 table entry at the formerly reported P5 worst flag.
  constexpr i128 rate9At46 = 17833120542407246LL;
  constexpr i128 affineAtWorst = i128(26000000000000LL) * 2920 +
    i128(9) * rate9At46;
  constexpr i128 targetAllowance = i128(253511670984674102LL);
  static_assert(affineAtWorst == i128(236418084881665214LL));
  static_assert(targetAllowance - affineAtWorst == i128(17093586103008888LL));
  std::cout << "HYPOTHETICAL_AFFINE r=9 v=46 z=2920 rate="
            << decimal(rate9At46) << " cap=" << decimal(affineAtWorst)
            << " allowanceSlack=" << decimal(targetAllowance - affineAtWorst)
            << '\n';
}
