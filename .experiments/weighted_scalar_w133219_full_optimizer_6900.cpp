#include <algorithm>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <string>
#include <tuple>
#include <vector>

using u128 = unsigned __int128;
using i128 = __int128;

constexpr uint64_t N = 262144;
constexpr uint64_t A = 180413;
static uint64_t W = 133219;
constexpr uint64_t PRIME = 2130706433;
constexpr uint64_t TARGET = 263611557201785350ULL;
constexpr uint64_t MAX_K = (PRIME - 1) / (9 * A);

static std::string show(u128 x) {
  if (!x) return "0";
  std::string s;
  while (x) { s.push_back(char('0' + x % 10)); x /= 10; }
  std::reverse(s.begin(), s.end());
  return s;
}

static std::string showi(i128 x) {
  return x < 0 ? "-" + show(u128(-x)) : show(u128(x));
}

static u128 ceil_div(u128 x, u128 y) { return (x + y - 1) / y; }
static u128 s1(uint64_t x) { return u128(x) * (x + 1) / 2; }
static u128 s2(uint64_t x) { return u128(x) * (x + 1) * (2 * x + 1) / 6; }

static u128 local_rank(uint64_t k) {
  return u128(k) * (2 * k + 1) * (2 * k + 1) * (53 * k + 11) / 2;
}

static u128 pair_sum(uint64_t k) {
  const uint64_t B = 9 * k * A, D = 4 * k;
  u128 out = 0;
  for (uint64_t t = 0; t <= D / 2; ++t) {
    const uint64_t base = B - (W - 2) * t;
    const uint64_t r = std::min(D - 2 * t, (base - 1) / (W - 1));
    const u128 count = r + 1, sr = s1(r), sr2 = s2(r);
    const u128 widths = count * base - u128(W - 1) * sr;
    const u128 widths2 = count * base * base
      - u128(2) * base * (W - 1) * sr + u128(W - 1) * (W - 1) * sr2;
    out += widths2 + u128(W) * widths;
  }
  return out;
}

static u128 pair_sum_general(uint64_t k,uint64_t m) {
  const uint64_t B=m*A,D=4*k;
  u128 out=0;
  for(uint64_t t=0;t<=D/2;++t) {
    const uint64_t base=B-(W-2)*t;
    const uint64_t r=std::min(D-2*t,(base-1)/(W-1));
    const u128 count=r+1,sr=s1(r),sr2=s2(r);
    const u128 widths=count*base-u128(W-1)*sr;
    const u128 widths2=count*base*base-u128(2)*base*(W-1)*sr+
      u128(W-1)*(W-1)*sr2;
    out+=widths2+u128(W)*widths;
  }
  return out;
}

struct Source {
  uint64_t k, m, B, D, T, M;
  u128 rank;
  i128 kernel;
};

static u128 high_prefix_value(uint64_t q,uint64_t fuel) {
  if(!q) return 0;
  if(q<=fuel) return u128(q)*(q+1)*(q+2)/6;
  const u128 at=u128(fuel)*(fuel+1)*(fuel+2)/6;
  const uint64_t count=q-fuel;
  const u128 sumq=(u128(fuel+1+q)*count)/2;
  return at+u128(fuel)*sumq-u128(count)*fuel*(fuel-1)/2;
}

static i128 isum1(uint64_t n) { return i128(n)*(n+1)/2; }
static i128 isum2(uint64_t n) { return i128(n)*(n+1)*(2*n+1)/6; }
static i128 isum3(uint64_t n) { const i128 x=isum1(n); return x*x; }
static i128 irange(i128 (*f)(uint64_t),uint64_t lo,uint64_t hi) {
  return f(hi)-(lo?f(lo-1):0);
}

// Sum P(a-3*i,f), i=0..n, where P(q,f)=sum_{r=1}^q min(r,f).
// This is the analytic collapse of the former O(k) high-prefix loop.
static u128 sum_high_prefix_step3(int64_t a,uint64_t n,uint64_t f) {
  if(a<=0) return 0;
  const uint64_t last=std::min<uint64_t>(n,(uint64_t(a)-1)/3);
  auto segment=[&](uint64_t lo,uint64_t hi,bool above)->i128 {
    if(lo>hi)return 0;
    const i128 cnt=i128(hi-lo+1),aa=a;
    const i128 si=irange(isum1,lo,hi),si2=irange(isum2,lo,hi),si3=irange(isum3,lo,hi);
    const i128 sq=cnt*aa-3*si;
    const i128 sq2=cnt*aa*aa-6*aa*si+9*si2;
    if(above) return (3*i128(f)*sq2+3*i128(f)*(2-i128(f))*sq+
      cnt*i128(f)*(f-1)*(i128(f)-2))/6;
    const i128 sq3=cnt*aa*aa*aa-9*aa*aa*si+27*aa*si2-27*si3;
    return (sq3+3*sq2+2*sq)/6;
  };
  uint64_t aboveLast=uint64_t(-1);
  if(uint64_t(a)>f) aboveLast=std::min<uint64_t>(last,(uint64_t(a)-f-1)/3);
  i128 ans=0;
  if(aboveLast!=uint64_t(-1)) ans+=segment(0,aboveLast,true);
  const uint64_t lowFirst=aboveLast==uint64_t(-1)?0:aboveLast+1;
  ans+=segment(lowFirst,last,false);
  if(ans<0)__builtin_trap();
  return u128(ans);
}

static u128 finite_rank(uint64_t k,uint64_t M) {
  const u128 low=u128(k)*(2*k+1)*(2*k+1)*(74*k+8)/6;
  const uint64_t m=9*k, kk=2*k;
  const uint64_t fuel=M+1>=4*k ? M+1-4*k : 0;
  u128 high=0;
  for(uint64_t i=0;i<=kk;++i) {
    const int64_t top=int64_t(m)-3*int64_t(i);
    if(top<=0) continue;
    const uint64_t qhi=uint64_t(top);
    const uint64_t qlo=top>int64_t(kk) ? uint64_t(top-int64_t(kk)) : 1;
    high+=high_prefix_value(qhi,fuel)-high_prefix_value(qlo-1,fuel);
  }
  return low+high;
}

static u128 finite_rank_general(uint64_t m,uint64_t k,uint64_t M) {
  // All scans below impose m >= 8*k, so every low layer d < 4*k is
  // unclipped.  Its slope in m is the exact weighted monomial count sum.
  const u128 low9=u128(k)*(2*k+1)*(2*k+1)*(74*k+8)/6;
  const u128 slope=u128(2)*k*(2*k+1)*(2*k+1);
  const i128 lowSigned=i128(low9)+(i128(m)-i128(9*k))*i128(slope);
  if(lowSigned<0) __builtin_trap();
  const u128 low=u128(lowSigned);
  const uint64_t kk=2*k;
  const uint64_t fuel=M+1>=4*k ? M+1-4*k : 0;
  u128 high=0;
  for(uint64_t i=0;i<=kk;++i) {
    const int64_t top=int64_t(m)-3*int64_t(i);
    if(top<=0) continue;
    const uint64_t qhi=uint64_t(top);
    const uint64_t qlo=top>int64_t(kk) ? uint64_t(top-int64_t(kk)) : 1;
    high+=high_prefix_value(qhi,fuel)-high_prefix_value(qlo-1,fuel);
  }
  return low+high;
}

static u128 finite_rank_general_fast(uint64_t m,uint64_t k,uint64_t M) {
  const u128 low9=u128(k)*(2*k+1)*(2*k+1)*(74*k+8)/6;
  const u128 slope=u128(2)*k*(2*k+1)*(2*k+1);
  const i128 lowSigned=i128(low9)+(i128(m)-i128(9*k))*i128(slope);
  if(lowSigned<0)__builtin_trap();
  const uint64_t fuel=M+1>=4*k?M+1-4*k:0;
  return u128(lowSigned)+sum_high_prefix_step3(m,2*k,fuel)-
    sum_high_prefix_step3(int64_t(m)-int64_t(2*k+1),2*k,fuel);
}

static uint64_t parity_count(uint64_t lo,uint64_t hi,uint64_t parity) {
  if(lo>hi)return 0;
  auto upto=[&](uint64_t x)->uint64_t {
    if(x<parity)return 0;
    return (x-parity)/2+1;
  };
  return upto(hi)-(lo?upto(lo-1):0);
}

// #{(a,e): 0<=a<=A0, 0<=e<=E0, 2a+3e<=L}.
static u128 count23(uint64_t A0,uint64_t E0,int64_t L) {
  if(L<0)return 0;
  const uint64_t Lu=uint64_t(L),emax=std::min<uint64_t>(E0,Lu/3);
  int64_t cap=-1;
  if(Lu>=2*A0)cap=std::min<uint64_t>(emax,(Lu-2*A0)/3);
  u128 out=cap>=0?u128(uint64_t(cap)+1)*(A0+1):0;
  const uint64_t lo=uint64_t(cap+1),hi=emax;
  if(lo<=hi) {
    const u128 cnt=hi-lo+1,se=u128(lo+hi)*(hi-lo+1)/2;
    const uint64_t odd=parity_count(lo,hi,1-(Lu&1));
    out+=(cnt*(Lu+2)-3*se-odd)/2;
  }
  return out;
}

// R(q,t)-R(q,t-1) for contact budget n=m-(d-q).
static u128 clipped_rank_delta(uint64_t n,uint64_t q,uint64_t t) {
  if(!t||t>q)return 0;
  const uint64_t Q=q-t;
  u128 tail=0;
  const int64_t c=int64_t(n)-3*int64_t(t);
  if(c>0) {
    const uint64_t amax=std::min<uint64_t>(Q,(uint64_t(c)-1)/2),cnt=amax+1;
    tail=u128(cnt)*uint64_t(c)-u128(cnt)*(cnt-1);
  }
  return count23(Q,t-1,int64_t(n)-1)+count23(Q,t-1,int64_t(n)-2)+tail;
}

static u128 clipped_rank_t0(uint64_t n,uint64_t q) {
  if(!n)return 0;
  const uint64_t h=std::min<uint64_t>(q,(n-1)/2),cnt=h+1;
  return u128(cnt)*n-u128(cnt)*(cnt-1);
}

static u128 clipped_rank(uint64_t n,uint64_t q,uint64_t t) {
  u128 out=clipped_rank_t0(n,q);
  for(uint64_t u=1;u<=std::min(t,q);++u)out+=clipped_rank_delta(n,q,u);
  return out;
}

static u128 clipped_rank_full_t(uint64_t n,uint64_t q) {
  if(!n)return 0;
  const uint64_t e=std::min<uint64_t>(q,(n-1)/3),cnt=e+1;
  const u128 se=s1(e),se2=s2(e);
  return u128(q+1)*n*cnt-(u128(3)*(q+1)+n)*se+3*se2;
}

// Exact generic lowRankSum m k, including the clipped chamber m<8k-1.
static u128 low_rank_clipped(uint64_t m,uint64_t k) {
  const uint64_t D=4*k,H=2*k;
  u128 out=0;
  for(uint64_t d=0;d<=H;++d)out+=clipped_rank_full_t(m,d);
  for(uint64_t d=H+1;d<D;++d)out+=clipped_rank(m,d,D-d);
  for(uint64_t q=H;q+1<D;++q) {
    const uint64_t t=D-q;
    for(uint64_t s=1;s<t;++s)out+=clipped_rank_delta(m-s,q,t);
  }
  return out;
}

static u128 low_rank_last_flag_lower(uint64_t m,uint64_t k) {
  const uint64_t D=4*k,H=2*k;u128 out=0;
  for(uint64_t d=0;d<D;++d) {
    if(d<=H)out+=clipped_rank_full_t(m,d);
    else out+=clipped_rank_full_t(m-(d-H),H);
  }
  return out;
}

static u128 finite_rank_clipped(uint64_t m,uint64_t k,uint64_t M) {
  if(M+1<4*k)__builtin_trap(); // not needed in the admissible full-width scan
  const uint64_t fuel=M+1-4*k;
  return low_rank_clipped(m,k)+sum_high_prefix_step3(m,2*k,fuel)-
    sum_high_prefix_step3(int64_t(m)-int64_t(2*k+1),2*k,fuel);
}

struct PairCoeff { i128 c2,c1,c0; };
static PairCoeff pair_coeff(uint64_t k) {
  const uint64_t D=4*k,L=W-1;
  i128 c2=0,c0=0,c1=0;
  for(uint64_t t=0;t<=D/2;++t) {
    const uint64_t c=(W-2)*t,r=D-2*t;
    const u128 n=r+1,sr=s1(r),sr2=s2(r);
    c2+=n;
    c1+=-2*i128(n)*c+i128(n)*W-2*i128(L)*i128(sr);
    c0+=i128(n)*c*c-i128(n)*W*c+2*i128(L)*c*i128(sr)-
      i128(W)*L*i128(sr)+i128(L)*L*i128(sr2);
  }
  return {c2,c1,c0};
}

static u128 pair_eval(PairCoeff c,uint64_t B) {
  const i128 ans=i128(c.c2)*B*B+c.c1*i128(B)+i128(c.c0);
  if(ans<0)__builtin_trap();
  return u128(ans);
}

static Source source_general(uint64_t k,uint64_t m) {
  const uint64_t B=m*A,D=4*k,M=B/(W-2);
  const u128 rank=finite_rank_general(m,k,M);
  return {k,m,B,D,2*k,M,rank,
    i128(pair_sum_general(k,m)/(2*W))-i128(N*rank)};
}

static Source source(uint64_t k) {
  const uint64_t B = 9 * k * A, D = 4 * k;
  const uint64_t M=B/(W-2);
  const u128 rank=finite_rank(k,M);
  return {k, 9*k, B, D, 2*k, M, rank,
    i128(pair_sum(k)/(2*W)) - i128(N*rank)};
}

static u128 active_fibres(uint64_t C, uint64_t E) {
  u128 out = 0;
  for (uint64_t t = 0; t <= E/2; ++t) {
    if (u128(W-2)*t >= C) break;
    const uint64_t base = C-(W-2)*t;
    const uint64_t r = std::min(E-2*t,(base-1)/(W-1));
    const uint64_t q=(base-1)/W, rem=(base-1)%W;
    const uint64_t extra = r >= W-rem ? r-(W-rem)+1 : 0;
    out += u128(r+1)*(q+1)+extra-s1(r);
  }
  return out;
}

static u128 active_fibres_closed_upper(uint64_t C,uint64_t E) {
  if(E<W && E<=C/W+1) {
    const uint64_t m=E/2,q=C/W;
    if(E%2==0) return u128(m+1)*(m+1)*(q+2-m);
    return u128(m+1)*(m+2)*(q+2)-u128(2*m+1)*(m+1)*(m+2)/2;
  }
  return active_fibres(C,E);
}

static u128 active_fibres_formula(uint64_t C,uint64_t E) {
  if(E>=W||u128(C)<=u128(W-1)*E)return active_fibres(C,E);
  const uint64_t h=E/2,n=h+1;
  const u128 st=s1(h),st2=s2(h);
  const uint64_t Q=(C-1)/W,rem=(C-1)%W;
  u128 out=u128(E+1)*(Q+1)*n-
    (u128(E+1)+u128(2)*(Q+1))*st+2*st2;
  out-=(u128(n)*(u128(E)*E+E)-u128(4*E+2)*st+4*st2)/2;
  const uint64_t wrap=(W-rem+1)/2;
  if(wrap<=h) {
    const uint64_t cnt=h-wrap+1;
    out+=u128(cnt)*(E+1)-u128(wrap+h)*cnt;
  }
  const uint64_t extra=E+rem+1>W?E+rem+1-W:0;
  if(extra)out+=u128(extra)*(std::min(h,wrap-1)+1);
  return out;
}

static u128 band_gr(const Source &h,uint64_t g,uint64_t rho) {
  const uint64_t delta=A-W+2;
  u128 out=0;
  for (uint64_t j=1;j*rho<=h.D;++j) {
    const u128 spent=u128(j)*g+u128(j-1)*delta;
    if (spent>=h.B) break;
    out += u128(delta)*active_fibres(h.B-uint64_t(spent),h.D-j*rho);
  }
  return out;
}

static u128 band_gr_fast(const Source &h,uint64_t g,uint64_t rho) {
  const uint64_t delta=A-W+2;
  u128 out=0;
  for (uint64_t j=1;j*rho<=h.D;++j) {
    const u128 spent=u128(j)*g+u128(j-1)*delta;
    if(spent>=h.B)break;
    out+=u128(delta)*active_fibres_closed_upper(h.B-uint64_t(spent),h.D-j*rho);
  }
  return out;
}

static u128 band_gr_formula(const Source&h,uint64_t g,uint64_t rho) {
  const uint64_t delta=A-W+2;u128 out=0;
  for(uint64_t j=1;j*rho<=h.D;++j) {
    const u128 spent=u128(j)*g+u128(j-1)*delta;
    if(spent>=h.B)break;
    out+=u128(delta)*active_fibres_formula(h.B-uint64_t(spent),h.D-j*rho);
  }
  return out;
}

static u128 band_formula(const Source&h,uint64_t cap,bool derivative) {
  const uint64_t rho=derivative?cap+1:2;
  const uint64_t g=derivative?(W-2)*((rho+1)/2):(W-2)*(cap+1);
  return band_gr_formula(h,g,rho);
}

static u128 band(const Source &h, uint64_t cap, bool derivative) {
  const uint64_t rho=derivative ? cap+1 : 2;
  const uint64_t g=derivative ? (W-2)*((rho+1)/2) : (W-2)*(cap+1);
  return band_gr(h,g,rho);
}

static u128 band_fast(const Source &h,uint64_t cap,bool derivative) {
  const uint64_t rho=derivative?cap+1:2;
  const uint64_t g=derivative?(W-2)*((rho+1)/2):(W-2)*(cap+1);
  return band_gr_fast(h,g,rho);
}

static u128 width_sum(uint64_t b) {
  if (!b) return 0;
  const uint64_t q=(b-1)/W;
  return u128(q+1)*b-u128(W)*q*(q+1)/2;
}

static u128 columns(uint64_t C,uint64_t E) {
  u128 out=0;
  for(uint64_t t=0;t<=E/2;++t) {
    if(u128(W-2)*t>=C) break;
    const uint64_t base=C-(W-2)*t;
    const uint64_t rmax=std::min(E-2*t,(base-1)/(W-1));
    for(uint64_t r=0;r<=rmax;++r) out+=width_sum(base-(W-1)*r);
  }
  return out;
}

static u128 width_sequence_segment(uint64_t base,uint64_t qb,uint64_t lo,uint64_t hi) {
  if(lo>hi)return 0;
  const i128 n=hi-lo+1,sr=irange(isum1,lo,hi),sr2=irange(isum2,lo,hi);
  const i128 L=W-1,b=base,q=qb;
  const i128 twice=2*((q+1)*b*n-((q+1)*L+b)*sr+L*sr2)-
    i128(W)*(q*(q+1)*n-(2*q+1)*sr+sr2);
  if(twice<0||twice%2)__builtin_trap();
  return u128(twice/2);
}

// Exact column count in O(E), analytically summing the inner r progression.
static u128 columns_linear(uint64_t C,uint64_t E) {
  u128 out=0;
  for(uint64_t t=0;t<=E/2;++t) {
    if(u128(W-2)*t>=C)break;
    const uint64_t base=C-(W-2)*t,n0=base-1;
    const uint64_t R=std::min(E-2*t,n0/(W-1));
    const uint64_t q0=n0/W,rem=n0%W,split=W-rem;
    if(split>0)out+=width_sequence_segment(base,q0,0,std::min(R,split-1));
    if(R>=split)out+=width_sequence_segment(base,q0+1,split,R);
  }
  return out;
}

static u128 exact_band_gr(const Source&h,uint64_t g,uint64_t rho) {
  const uint64_t delta=A-W+2;
  u128 out=0;
  for(uint64_t j=1;j*rho<=h.D;++j) {
    const u128 spent=u128(j)*g+u128(j-1)*delta;
    if(spent>=h.B)break;
    const uint64_t top=h.B-uint64_t(spent),E=h.D-j*rho;
    out+=columns(top,E)-columns(top-delta,E);
  }
  return out;
}

static u128 exact_band_gr_linear(const Source&h,uint64_t g,uint64_t rho) {
  const uint64_t delta=A-W+2;
  u128 out=0;
  for(uint64_t j=1;j*rho<=h.D;++j) {
    const u128 spent=u128(j)*g+u128(j-1)*delta;
    if(spent>=h.B)break;
    const uint64_t top=h.B-uint64_t(spent),E=h.D-j*rho;
    out+=columns_linear(top,E)-columns_linear(top-delta,E);
  }
  return out;
}


static u128 exact_band(const Source&h,uint64_t cap,bool derivative) {
  const uint64_t rho=derivative?cap+1:2;
  const uint64_t g=derivative?(W-2)*((rho+1)/2):(W-2)*(cap+1);
  return exact_band_gr_linear(h,g,rho);
}

static uint64_t min_cap(const Source &h, bool derivative) {
  uint64_t lo=0,hi=1;
  if (band(h,0,derivative)<u128(h.kernel)) return 0;
  while (band(h,hi,derivative)>=u128(h.kernel)) hi*=2;
  while (lo+1<hi) {
    uint64_t m=(lo+hi)/2;
    if (band(h,m,derivative)<u128(h.kernel)) hi=m; else lo=m;
  }
  return hi;
}

static uint64_t min_cap_fast(const Source &h,bool derivative) {
  uint64_t lo=0,hi=1;
  if(band_fast(h,0,derivative)<u128(h.kernel))return 0;
  while(band_fast(h,hi,derivative)>=u128(h.kernel))hi*=2;
  while(lo+1<hi){uint64_t m=(lo+hi)/2;if(band_fast(h,m,derivative)<u128(h.kernel))hi=m;else lo=m;}
  return hi;
}

static uint64_t min_cap_formula(const Source&h,bool derivative) {
  uint64_t lo=0,hi=1;
  if(band_formula(h,0,derivative)<u128(h.kernel))return 0;
  while(band_formula(h,hi,derivative)>=u128(h.kernel))hi*=2;
  while(lo+1<hi){const uint64_t m=(lo+hi)/2;
    if(band_formula(h,m,derivative)<u128(h.kernel))hi=m;else lo=m;}
  return hi;
}

struct Flag { u128 z,y,a; };
static Flag sf(const Source &s) { return {s.M-s.D,s.D-s.T,s.T}; }
static Flag af(uint64_t M,uint64_t D,uint64_t T) {
  return {1+u128(W)*(2*(M-D)-1),u128(2)*W*(D-T)+W,u128(2)*W*(T-1)};
}
static u128 mixed(Flag p,Flag q,Flag r) {
  return p.a*q.a*r.a+p.z*q.a*r.a+q.z*p.a*r.a+r.z*p.a*q.a
    +p.y*q.a*r.a+q.y*p.a*r.a+r.y*p.a*q.a
    +p.a*q.y*r.y+q.a*p.y*r.y+r.a*p.y*q.y
    +p.z*q.y*r.a+p.z*r.y*q.a+q.z*p.y*r.a+q.z*r.y*p.a
    +r.z*p.y*q.a+r.z*q.y*p.a;
}

static u128 first_regular(uint64_t y,uint64_t r) {
  const u128 cost=(1+u128(2)*W*y)*r+u128(W)*(2*r-1)*y;
  return ceil_div(u128(N-W)*cost,A-W);
}
static u128 cleanup(const Source &p) {
  const uint64_t y=(2*p.T-1)*p.M,r=(2*p.T-1)*p.D;
  return first_regular(y,r)+u128(2*r-1)*y
    +first_regular(p.M,p.D)+u128(2*p.D-1)*p.M+p.M;
}

static uint64_t min_v_and_q(uint64_t &q_required) {
  for (uint64_t v=0;v<W;++v) {
    const uint64_t u=v+1;
    const i128 inner=i128(A-u)*(A-u)-i128(N-u)*(W-u);
    if (inner<=0) continue;
    const u128 lhs=u128(N-u)*(N-W);
    q_required=uint64_t(lhs/u128(inner));
    return v;
  }
  __builtin_unreachable();
}

struct Best {
  u128 total=~u128(0),cheap=0,exits=0,clean=0;
  uint64_t pk=0,pm=0,hk=0,hm=0,J=0,D=0,v=0,qmin=0,qmax=0;
};

int main(int argc,char**argv) {
  const bool generalScan=argc>1 && std::string(argv[1])=="gscan";
  const bool generalProfile=argc>1 && std::string(argv[1])=="gprofile";
  const bool generalFull=argc>1 && std::string(argv[1])=="fullg";
  const bool helperScan=argc>1 && std::string(argv[1])=="hscan";
  const bool clippedProbe=argc>1 && std::string(argv[1])=="clipprobe";
  const bool clippedProfile=argc>1 && std::string(argv[1])=="clipprofile";
  const bool helperFront=argc>1 && std::string(argv[1])=="hfront";
  const bool primaryLedger=argc>1 && std::string(argv[1])=="pledger";
  const bool boundaryScan=argc>1 && std::string(argv[1])=="boundary";
  const bool clippedEdge=argc>1 && std::string(argv[1])=="clipedge";
  const bool exactMode=argc>1 && std::string(argv[1])=="exact";
  const bool fastMode=generalFull ? !(argc>3&&std::string(argv[3])=="slow") :
    !(argc>2 && std::string(argv[2])=="slow");
  const uint64_t forcedPrimary=!generalFull&&argc>3 ? std::stoull(argv[3]) : 0;
  if(generalScan||generalProfile||generalFull||helperScan||clippedProbe||clippedProfile||helperFront||primaryLedger||boundaryScan||clippedEdge)
    W=std::stoull(argv[2]);
  else if(argc>1 && !exactMode) W=std::stoull(argv[1]);
  if(generalScan) {
    const uint64_t k=std::stoull(argv[3]);
    const uint64_t mlo=argc>4?std::stoull(argv[4]):8*k;
    const uint64_t mhi=argc>5?std::stoull(argv[5]):std::min<uint64_t>(11810,12*k);
    i128 best=std::numeric_limits<i128>::min();uint64_t bm=0,first=0,last=0,count=0;
    for(uint64_t m=mlo;m<=mhi;++m) {
      Source s=source_general(k,m);
      if(s.kernel>best){best=s.kernel;bm=m;}
      if(s.kernel>0){if(!count)first=m;last=m;++count;}
    }
    const Source b=source_general(k,bm);
    const u128 fastRank=finite_rank_general_fast(bm,k,b.M);
    const u128 fastPair=pair_eval(pair_coeff(k),b.B);
    std::cout<<"GSCAN W="<<W<<" k="<<k<<" bestm="<<bm
      <<" bestgap="<<showi(best)<<" B="<<b.B<<" M="<<b.M
      <<" rank="<<show(b.rank)<<" positive="<<first<<".."<<last
      <<" count="<<count<<" fastRankEq="<<(fastRank==b.rank)
      <<" fastPairEq="<<(fastPair==pair_sum_general(k,bm))<<"\n";
    return count?0:2;
  }
  if(generalProfile) {
    const uint64_t k=std::stoull(argv[3]),m=std::stoull(argv[4]);
    const bool check=argc>5&&std::string(argv[5])=="check";
    const bool slow=argc>5&&(std::string(argv[5])=="slow"||check);
    const Source s=source_general(k,m);
    const uint64_t J=slow?min_cap(s,false):min_cap_fast(s,false);
    const uint64_t D=slow?min_cap(s,true):min_cap_fast(s,true);
    const u128 jb=slow?band(s,J,false):band_fast(s,J,false);
    const u128 db=slow?band(s,D,true):band_fast(s,D,true);
    const u128 j211=slow?exact_band(s,211,false):band_fast(s,211,false);
    const u128 d55=slow?exact_band(s,55,true):band_fast(s,55,true);
    const u128 j211active=band(s,211,false),d55active=band(s,55,true);
    std::cout<<"GPROFILE W="<<W<<" k="<<k<<" m="<<m<<" B="<<s.B
      <<" M="<<s.M<<" rank="<<show(s.rank)<<" kernel="<<showi(s.kernel)
      <<" J="<<J<<" D="<<D<<" Jband="<<show(jb)
      <<" Jmargin="<<showi(s.kernel-i128(jb))<<" Dband="<<show(db)
      <<" Dmargin="<<showi(s.kernel-i128(db))
      <<" J211margin="<<showi(s.kernel-i128(j211))
      <<" D55margin="<<showi(s.kernel-i128(d55))
      <<" J211active="<<showi(s.kernel-i128(j211active))
      <<" D55active="<<showi(s.kernel-i128(d55active));
    if(check) {
      const uint64_t rho=56,g=(W-2)*28;
      std::cout<<" columnsEq="<<(columns(s.B,s.D)==columns_linear(s.B,s.D))
        <<" D55oldEq="<<(exact_band_gr(s,g,rho)==d55);
    }
    std::cout<<"\n";
    return s.kernel>0?0:2;
  }
  if(helperScan) {
    struct Candidate { i128 fastMargin; Source s; };
    const uint64_t klo=argc>3?std::stoull(argv[3]):800;
    std::vector<Candidate> candidates;
    const uint64_t unclippedKMax=11810/8;
    for(uint64_t k=klo;k<=unclippedKMax;++k) {
      const PairCoeff pc=pair_coeff(k);
      const uint64_t hi=std::min<uint64_t>(11810,12*k);
      for(uint64_t m=8*k;m<=hi;++m) {
        const uint64_t B=m*A,M=B/(W-2);
        const u128 rank=finite_rank_general_fast(m,k,M);
        Source s={k,m,B,4*k,2*k,M,rank,
          i128(pair_eval(pc,B)/(2*W))-i128(N*rank)};
        if(s.kernel<=0)continue;
        const i128 dm=s.kernel-i128(band_formula(s,55,true));
        candidates.push_back({dm,s});
      }
    }
    std::sort(candidates.begin(),candidates.end(),[](const Candidate&a,const Candidate&b){
      return a.fastMargin>b.fastMargin;
    });
    const size_t take=std::min<size_t>(3,candidates.size());
    if(take) std::cerr<<"HSCAN candidates="<<candidates.size()<<" topActive="
      <<showi(candidates[0].fastMargin)<<" at="<<candidates[0].s.k<<","
      <<candidates[0].s.m<<"\n";
    i128 bestExact=std::numeric_limits<i128>::min();size_t bei=0;
    for(size_t i=0;i<take;++i) {
      const Source&s=candidates[i].s;
      const i128 de=s.kernel-i128(exact_band(s,55,true));
      const i128 je=s.kernel-i128(exact_band(s,211,false));
      if(de>bestExact){bestExact=de;bei=i;}
      std::cout<<"HCAND i="<<i<<" k="<<s.k<<" m="<<s.m<<" M="<<s.M
        <<" K="<<showi(s.kernel)<<" D55active="<<showi(candidates[i].fastMargin)
        <<" D55exact="<<showi(de)<<" J211exact="<<showi(je)<<"\n";
    }
    if(take) std::cout<<"HSCAN count="<<candidates.size()<<" bestExactTop="
      <<showi(bestExact)<<" at="<<candidates[bei].s.k<<","<<candidates[bei].s.m<<"\n";
    return 0;
  }
  if(helperFront) {
    const uint64_t pk=std::stoull(argv[3]),pm=std::stoull(argv[4]);
    const Source p=source_general(pk,pm);
    uint64_t qmin=0;const uint64_t v=min_v_and_q(qmin);
    u128 best=~u128(0),bc=0,bx=0;Source bs{};uint64_t bJ=0,bD=0,eligible=0;
    for(uint64_t k=1;k<=11810/8;++k) {
      const PairCoeff pc=pair_coeff(k);
      for(uint64_t m=std::max<uint64_t>(1,8*k-1);m<=std::min<uint64_t>(11810,12*k);++m) {
        const uint64_t B=m*A,M=B/(W-2);
        const u128 rank=finite_rank_general_fast(m,k,M);
        Source s={k,m,B,4*k,2*k,M,rank,
          i128(pair_eval(pc,B)/(2*W))-i128(N*rank)};
        if(s.kernel<=0||band_formula(s,56,true)>=u128(s.kernel))continue;
        ++eligible;
        const uint64_t D=56;
        if(band_formula(s,212,false)>=u128(s.kernel))continue;
        uint64_t J=212;
        while(J>D&&band_formula(s,J-1,false)<u128(s.kernel))--J;
        const uint64_t T=D/2;
        const Flag cf={J-D,D-T,T},ca=af(J,D,T),hf=sf(s);
        const u128 cheap=ceil_div(u128(N-v)*(N-v)*mixed(cf,ca,ca),u128(A-v)*(A-v));
        const u128 exits=ceil_div(u128(N-v)*mixed(sf(p),hf,af(p.M,p.D,p.T)),A-v);
        const u128 total=cheap+exits+cleanup(p);
        if(total<best){best=total;bc=cheap;bx=exits;bs=s;bJ=J;bD=D;}
      }
    }
    std::cout<<"HFRONT W="<<W<<" primary="<<pk<<","<<pm<<" eligible="<<eligible
      <<" total="<<show(best)<<" gap="<<showi(i128(best)-TARGET)<<" hk="<<bs.k
      <<" hm="<<bs.m<<" M="<<bs.M<<" J="<<bJ<<" D="<<bD
      <<" K="<<showi(bs.kernel)<<" Jmargin="
      <<showi(bs.kernel-i128(band_formula(bs,bJ,false)))<<" Dmargin="
      <<showi(bs.kernel-i128(band_formula(bs,bD,true)))<<" cheap="<<show(bc)
      <<" exits="<<show(bx)<<" cleanup="<<show(cleanup(p))<<"\n";
    return 0;
  }
  if(primaryLedger) {
    const uint64_t hk=std::stoull(argv[3]),hm=std::stoull(argv[4]);
    const uint64_t J=std::stoull(argv[5]),D=std::stoull(argv[6]),T=D/2;
    const Source h=source_general(hk,hm);const Flag hf=sf(h),cf={J-D,D-T,T},ca=af(J,D,T);
    uint64_t qmin=0;const uint64_t v=min_v_and_q(qmin);
    const u128 cheap=ceil_div(u128(N-v)*(N-v)*mixed(cf,ca,ca),u128(A-v)*(A-v));
    Best best;
    for(uint64_t k=1;k<=200;++k)for(uint64_t m=8*k;m<=std::min<uint64_t>(11810,12*k);++m) {
      const Source p=source_general(k,m);if(p.kernel<=0)continue;
      const Flag pa=af(p.M,p.D,p.T);
      uint64_t qmax=uint64_t(std::min(u128(N-v)*ca.a/(A-v),u128(N-v)*pa.a/(A-v)));
      qmax=uint64_t(std::min(u128(qmax),u128(N-v)*(N-v)*ca.a*ca.a/(u128(A-v)*(A-v))));
      if(qmin>qmax)continue;
      const u128 exits=ceil_div(u128(N-v)*mixed(sf(p),hf,pa),A-v),cl=cleanup(p);
      const u128 total=cheap+exits+cl;
      if(total<best.total)best={total,cheap,exits,cl,k,m,hk,hm,J,D,v,qmin,qmax};
    }
    std::cout<<"PLEDGER W="<<W<<" total="<<show(best.total)<<" gap="
      <<showi(i128(best.total)-TARGET)<<" pk="<<best.pk<<" pm="<<best.pm
      <<" hk="<<hk<<" hm="<<hm<<" J="<<J<<" D="<<D<<" cheap="
      <<show(best.cheap)<<" exits="<<show(best.exits)<<" cleanup="<<show(best.clean)<<"\n";
    return 0;
  }
  if(boundaryScan) {
    const uint64_t cap=std::stoull(argv[3]);const bool deriv=std::stoull(argv[4]);
    i128 best=std::numeric_limits<i128>::min();Source bs{};uint64_t cnt=0,first=0,last=0;
    for(uint64_t k=1;k<=11810/8;++k) {
      const uint64_t m=8*k-1,B=m*A,M=B/(W-2);const PairCoeff pc=pair_coeff(k);
      const u128 rank=finite_rank_general_fast(m,k,M);
      const Source s={k,m,B,4*k,2*k,M,rank,
        i128(pair_eval(pc,B)/(2*W))-i128(N*rank)};
      if(s.kernel<=0)continue;
      if(!cnt)first=k;last=k;++cnt;
      const i128 margin=s.kernel-i128(band_formula(s,cap,deriv));
      if(margin>best){best=margin;bs=s;}
    }
    std::cout<<"BOUNDARY W="<<W<<" cap="<<cap<<" deriv="<<deriv<<" best="
      <<showi(best)<<" k="<<bs.k<<" m="<<bs.m<<" K="<<showi(bs.kernel)
      <<" positive="<<first<<".."<<last<<" count="<<cnt<<"\n";
    return 0;
  }
  if(clippedEdge) {
    struct Edge { i128 K=0,J=0,D=0; };
    std::vector<Edge> e0(1484),e1(1484),e8(1484),e32(1484);
    #pragma omp parallel for schedule(dynamic)
    for(int64_t ki=594;ki<=1483;++ki) {
      const uint64_t k=ki,top=std::min<uint64_t>(11810,8*k-1);const PairCoeff pc=pair_coeff(k);
      auto eval=[&](uint64_t m)->Edge {
        const uint64_t B=m*A,M=B/(W-2);const u128 rank=finite_rank_clipped(m,k,M);
        const i128 K=i128(pair_eval(pc,B)/(2*W))-i128(N*rank);
        const Source s={k,m,B,4*k,2*k,M,rank,K};
        return {K,K-i128(band_formula(s,212,false)),K-i128(band_formula(s,56,true))};
      };
      e0[k]=eval(top);e1[k]=eval(top-1);e8[k]=eval(top-8);e32[k]=eval(top-32);
    }
    for(const auto &[name,es]:std::vector<std::pair<std::string,const std::vector<Edge>*>>{
        {"edge",&e0},{"minus1",&e1},{"minus8",&e8},{"minus32",&e32}}) {
      i128 bK=std::numeric_limits<i128>::min(),bJ=bK,bD=bK;uint64_t kK=0,kJ=0,kD=0;
      for(uint64_t k=594;k<=1483;++k){if((*es)[k].K>bK){bK=(*es)[k].K;kK=k;}
        if((*es)[k].J>bJ){bJ=(*es)[k].J;kJ=k;}if((*es)[k].D>bD){bD=(*es)[k].D;kD=k;}}
      std::cout<<"CLIPEDGE "<<name<<" bestK="<<showi(bK)<<"@"<<kK
        <<" bestJ212="<<showi(bJ)<<"@"<<kJ<<" bestD56="<<showi(bD)<<"@"<<kD<<"\n";
    }
    i128 minDK=std::numeric_limits<i128>::max(),minJK=minDK,minKK=minDK;uint64_t kd=0,kj=0,kk=0;
    for(uint64_t k=594;k<=1483;++k){const i128 dd=e0[k].D-e1[k].D,dj=e0[k].J-e1[k].J,dk=e0[k].K-e1[k].K;
      if(dd<minDK){minDK=dd;kd=k;}if(dj<minJK){minJK=dj;kj=k;}if(dk<minKK){minKK=dk;kk=k;}}
    std::cout<<"CLIPEDGE minLastIncrement K="<<showi(minKK)<<"@"<<kk
      <<" J="<<showi(minJK)<<"@"<<kj<<" D="<<showi(minDK)<<"@"<<kd<<"\n";
    for(const auto &[name,a,b,span]:std::vector<std::tuple<std::string,const std::vector<Edge>*,const std::vector<Edge>*,uint64_t>>{
        {"edge-minus8",&e0,&e8,8},{"minus8-minus32",&e8,&e32,24}}) {
      i128 mk=std::numeric_limits<i128>::max(),mj=mk,md=mk;uint64_t ak=0,aj=0,ad=0;
      for(uint64_t k=594;k<=1483;++k){const i128 dk=((*a)[k].K-(*b)[k].K)/span;
        const i128 dj=((*a)[k].J-(*b)[k].J)/span,dd=((*a)[k].D-(*b)[k].D)/span;
        if(dk<mk){mk=dk;ak=k;}if(dj<mj){mj=dj;aj=k;}if(dd<md){md=dd;ad=k;}}
      std::cout<<"CLIPEDGE minAverageIncrement "<<name<<" K="<<showi(mk)<<"@"<<ak
        <<" J="<<showi(mj)<<"@"<<aj<<" D="<<showi(md)<<"@"<<ad<<"\n";
    }
    return 0;
  }
  if(clippedProbe) {
    i128 best=std::numeric_limits<i128>::min();uint64_t bk=0,bm=0,bM=0;
    uint64_t positiveCount=0,minpk=0,maxpk=0;
    const uint64_t kmax=11810*A/(4*(W-1));
    for(uint64_t k=1;k<=kmax;++k) {
      const PairCoeff pc=pair_coeff(k);
      const uint64_t lo=uint64_t((u128(4)*k*(W-1))/A)+1;
      const uint64_t hi=std::min<uint64_t>(11810,8*k-1);
      if(lo>hi)continue;
      for(uint64_t m=lo;m<=hi;++m) {
        const uint64_t B=m*A,M=B/(W-2);
        const u128 rankOptimistic=finite_rank_general_fast(m,k,M);
        const i128 gap=i128(pair_eval(pc,B)/(2*W))-i128(N*rankOptimistic);
        if(gap>best){best=gap;bk=k;bm=m;bM=M;}
        if(gap>0){++positiveCount;if(!minpk)minpk=k;maxpk=k;}
      }
    }
    std::cout<<"CLIPPROBE W="<<W<<" kmax="<<kmax<<" bestOptimisticGap="
      <<showi(best)<<" k="<<bk<<" m="<<bm<<" M="<<bM
      <<" optimisticPositive="<<positiveCount<<" kRange="<<minpk<<".."<<maxpk<<"\n";
    return 0;
  }
  if(clippedProfile) {
    const uint64_t k=std::stoull(argv[3]),m=std::stoull(argv[4]);
    const uint64_t B=m*A,M=B/(W-2);
    const PairCoeff pc=pair_coeff(k);
    const u128 low=low_rank_clipped(m,k),rank=finite_rank_clipped(m,k,M);
    u128 lowA=0,lowB1=0;
    for(uint64_t d=0;d<=2*k;++d)lowA+=clipped_rank_full_t(m,d);
    for(uint64_t d=2*k+1;d<4*k;++d)lowB1+=clipped_rank(m,d,4*k-d);
    const u128 lowLB=low_rank_last_flag_lower(m,k);
    const uint64_t fuel=M+1-4*k;
    const u128 high=sum_high_prefix_step3(m,2*k,fuel)-
      sum_high_prefix_step3(int64_t(m)-int64_t(2*k+1),2*k,fuel);
    const i128 kernelLB=i128(pair_eval(pc,B)/(2*W))-i128(N*(lowLB+high));
    const i128 kernel=i128(pair_eval(pc,B)/(2*W))-i128(N*rank);
    const Source s={k,m,B,4*k,2*k,M,rank,kernel};
    std::cout<<"CLIPPROFILE W="<<W<<" k="<<k<<" m="<<m<<" B="<<B<<" M="<<M
      <<" low="<<show(low)<<" rank="<<show(rank)<<" kernel="<<showi(kernel)
      <<" lowA="<<show(lowA)<<" lowB1="<<show(lowB1)<<" lowB2="<<show(low-lowA-lowB1)
      <<" lowLB="<<show(lowLB)<<" optimisticLBgap="<<showi(kernelLB)
      <<" J="<<min_cap_fast(s,false)<<" D="<<min_cap_fast(s,true)
      <<" J211fast="<<showi(kernel-i128(band_fast(s,211,false)))
      <<" D55fast="<<showi(kernel-i128(band_fast(s,55,true)))
      <<" J212active="<<showi(kernel-i128(band_formula(s,212,false)))
      <<" D56active="<<showi(kernel-i128(band_formula(s,56,true)))<<"\n";
    return 0;
  }
  std::vector<Source> sources(MAX_K+1);
  std::vector<uint64_t> positive;
  for (uint64_t k=1;k<=MAX_K;++k) {
    sources[k]=source(k);
    if (sources[k].kernel>0) positive.push_back(k);
  }
  if(positive.empty()) { std::cout<<"NO_SOURCE W="<<W<<"\n"; return 2; }
  std::cerr << "positive=" << positive.front() << ".." << positive.back()
    << " count=" << positive.size() << "\n";
  if(exactMode) {
    for(uint64_t k:{58ULL,59ULL,60ULL,61ULL,1287ULL,1312ULL}) {
      const u128 exactColumns=columns(sources[k].B,sources[k].D);
      const i128 exactKernel=i128(exactColumns)-i128(N*sources[k].rank);
      std::cout<<"SOURCE k="<<k<<" exactColumns="<<show(exactColumns)
        <<" exactKernel="<<showi(exactKernel)
        <<" sourceRefund="<<showi(exactKernel-sources[k].kernel)<<"\n";
      for(uint64_t cap:{211ULL,212ULL}) {
        const u128 e=exact_band(sources[k],cap,false);
        std::cout<<"EXACT k="<<k<<" J="<<cap<<" band="<<show(e)
          <<" margin="<<showi(sources[k].kernel-i128(e))
          <<" approxRefund="<<show(band(sources[k],cap,false)-e)<<"\n";
      }
      const u128 e=exact_band(sources[k],55,true);
      std::cout<<"EXACT k="<<k<<" D=55 band="<<show(e)
        <<" margin="<<showi(sources[k].kernel-i128(e))
        <<" approxRefund="<<show(band(sources[k],55,true)-e)<<"\n";
      u128 worstApprox=0;uint64_t wad=0;
      constexpr uint64_t jet=212;
      for(uint64_t d=2;d<=2*jet;++d) {
        const uint64_t g=(W-2)*jet+(2*jet-d);
        const u128 xa=band_gr(sources[k],g,d);
        if(xa>worstApprox){worstApprox=xa;wad=d;}
      }
      const uint64_t wg=(W-2)*jet+(2*jet-wad);
      const u128 worst=exact_band_gr(sources[k],wg,wad);
      std::cout<<"JOINT k="<<k<<" exactAtApproxWorst="<<show(worst)<<" d="<<wad
        <<" exactMargin="<<showi(exactKernel-i128(worst))
        <<" approxWorst="<<show(worstApprox)<<" d="<<wad
        <<" approxMargin="<<showi(sources[k].kernel-i128(worstApprox))<<"\n";
    }
    return 0;
  }

  struct H { uint64_t k,J,D; u128 jb,db; };
  std::vector<H> helpers(positive.size());
  i128 bestD54 = std::numeric_limits<i128>::min();
  i128 bestD54withJ212 = std::numeric_limits<i128>::min();
  i128 bestJ211withD55 = std::numeric_limits<i128>::min();
  uint64_t bestD54k=0,bestD54withJ212k=0;
  uint64_t bestJ211withD55k=0;
  #pragma omp parallel for schedule(dynamic)
  for (int64_t ii=0;ii<int64_t(positive.size());++ii) {
    const uint64_t k=positive[ii];
    const auto &h=sources[k];
    uint64_t J=fastMode?min_cap_fast(h,false):min_cap(h,false);
    uint64_t D=fastMode?min_cap_fast(h,true):min_cap(h,true);
    J=std::max(J,D);
    helpers[ii]={k,J,D,fastMode?band_fast(h,J,false):band(h,J,false),
      fastMode?band_fast(h,D,true):band(h,D,true)};
  }
  if(argc==1) for (uint64_t k:positive) {
    const auto &h=sources[k];
    const i128 d54=h.kernel-i128(band(h,54,true));
    if(d54>bestD54){bestD54=d54;bestD54k=k;}
    if(band(h,212,false)<u128(h.kernel)&&d54>bestD54withJ212){
      bestD54withJ212=d54;bestD54withJ212k=k;
    }
    const i128 j211=h.kernel-i128(band(h,211,false));
    if(band(h,55,true)<u128(h.kernel)&&j211>bestJ211withD55){
      bestJ211withD55=j211;bestJ211withD55k=k;
    }
  }
  if(argc==1) std::cerr << "best D54 margin=" << showi(bestD54) << " k=" << bestD54k
    << "; with J212=" << showi(bestD54withJ212)
    << " k=" << bestD54withJ212k << "\n";
  if(argc==1) std::cerr << "best J211 margin with D55=" << showi(bestJ211withD55)
    << " k=" << bestJ211withD55k << "\n";

  uint64_t qmin=0;
  const uint64_t v=min_v_and_q(qmin);
  std::cerr << "algebraic_min_v=" << v << " qmin=" << qmin << "\n";
  Best best;
  std::vector<Source> primaryCandidates;
  if(generalFull) {
    for(uint64_t k=1;k<=200;++k) {
      const uint64_t hi=std::min<uint64_t>(11810,12*k);
      for(uint64_t m=8*k;m<=hi;++m) {
        Source p=source_general(k,m);
        if(p.kernel>0) primaryCandidates.push_back(p);
      }
    }
    std::cerr<<"general_primary_records="<<primaryCandidates.size()<<"\n";
  } else if(forcedPrimary) primaryCandidates.push_back(sources[forcedPrimary]);
  else for(uint64_t pk:positive) primaryCandidates.push_back(sources[pk]);
  for (const H &h:helpers) {
    const uint64_t T=h.D/2;
    const Flag cf={h.J-h.D,h.D-T,T},ca=af(h.J,h.D,T),hf=sf(sources[h.k]);
    const u128 cheap=ceil_div(u128(N-v)*(N-v)*mixed(cf,ca,ca),u128(A-v)*(A-v));
    for (const Source &p:primaryCandidates) {
      const Flag pf=sf(p),pa=af(p.M,p.D,p.T);
      uint64_t qmax=uint64_t(std::min(
        u128(N-v)*ca.a/(A-v),u128(N-v)*pa.a/(A-v)));
      qmax=uint64_t(std::min(u128(qmax),
        u128(N-v)*(N-v)*ca.a*ca.a/(u128(A-v)*(A-v))));
      if (qmin>qmax) continue;
      const u128 exits=ceil_div(u128(N-v)*mixed(pf,hf,pa),A-v);
      const u128 clean=cleanup(p),total=cheap+exits+clean;
      if (total<best.total) best={total,cheap,exits,clean,p.k,p.m,h.k,sources[h.k].m,
        h.J,h.D,v,qmin,qmax};
    }
  }
  std::cout << "BEST total=" << show(best.total)
    << " target=" << TARGET << " gap=" << showi(i128(best.total)-TARGET)
    << " pk=" << best.pk << " pm="<<best.pm<<" hk=" << best.hk
    << " hm="<<best.hm<<" J=" << best.J
    << " D=" << best.D << " T=" << best.D/2 << " v=" << best.v
    << " qmin=" << best.qmin << " qmax=" << best.qmax
    << " cheap=" << show(best.cheap) << " exits=" << show(best.exits)
    << " cleanup=" << show(best.clean) << "\n";
  const auto &bh=*std::find_if(helpers.begin(),helpers.end(),[&](const H&h){return h.k==best.hk;});
  std::cout << "helper K=" << showi(sources[best.hk].kernel)
    << " Jband=" << show(bh.jb) << " Jmargin=" << showi(sources[best.hk].kernel-i128(bh.jb))
    << " Dband=" << show(bh.db) << " Dmargin=" << showi(sources[best.hk].kernel-i128(bh.db)) << "\n";
  if(argc==1) for(uint64_t k:{1287ULL,1312ULL}) {
    const u128 ej=exact_band(sources[k],211,false);
    const u128 ed=exact_band(sources[k],55,true);
    std::cout << "EXACT k="<<k<<" J211="<<show(ej)
      <<" Jmargin="<<showi(sources[k].kernel-i128(ej))
      <<" D55="<<show(ed)<<" Dmargin="<<showi(sources[k].kernel-i128(ed))<<"\n";
  }

  std::map<std::pair<uint64_t,uint64_t>,std::tuple<u128,uint64_t,uint64_t>> combos;
  if(argc==1) for (const H& h:helpers) {
    auto key=std::make_pair(h.J,h.D);
    const Flag hf=sf(sources[h.k]);
    u128 best_exit=~u128(0);uint64_t bp=0;
    for(uint64_t pk:positive) {
      const u128 x=ceil_div(u128(N-v)*mixed(sf(sources[pk]),hf,
        af(sources[pk].M,sources[pk].D,sources[pk].T)),A-v)+cleanup(sources[pk]);
      if(x<best_exit){best_exit=x;bp=pk;}
    }
    auto it=combos.find(key);
    if(it==combos.end()||best_exit<std::get<0>(it->second)) combos[key]={best_exit,bp,h.k};
  }
  if(argc==1) for(auto &[key,val]:combos) {
    auto [ec,pk,hk]=val;uint64_t J=key.first,D=key.second,T=D/2;
    Flag cf={J-D,D-T,T},ca=af(J,D,T);
    u128 cheap=ceil_div(u128(N-v)*(N-v)*mixed(cf,ca,ca),u128(A-v)*(A-v));
    std::cout << "COMBO J="<<J<<" D="<<D<<" bestTotal="<<show(cheap+ec)
      <<" gap="<<showi(i128(cheap+ec)-TARGET)<<" pk="<<pk<<" hk="<<hk<<"\n";
  }
}
