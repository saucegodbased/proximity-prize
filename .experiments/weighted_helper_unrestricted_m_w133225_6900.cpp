#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <tuple>
#include <vector>

// Exhaustive arithmetic gate for arbitrary weighted-source contact order m.
// This deliberately does not assume m >= 8*k.  It mirrors the Nat-valued
// definitions weightedFlagUnionRank, highRankBound, and columns at W=133225.
using u128 = unsigned __int128;
using i128 = __int128;

#ifndef IDENTITY_N
#define IDENTITY_N 262144
#endif
constexpr uint64_t N = IDENTITY_N;
#ifndef AGREEMENT_A
#define AGREEMENT_A 180413
#endif
constexpr uint64_t A = AGREEMENT_A;
constexpr uint64_t W = 133225;
constexpr uint64_t PRIME = 2130706433;
constexpr uint64_t DELTA = A - W + 2;
constexpr uint64_t MAX_M = (PRIME - 1) / A;

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
static u128 s1(uint64_t x) { return u128(x) * (x + 1) / 2; }
static u128 s2(uint64_t x) { return u128(x) * (x + 1) * (2*x + 1) / 6; }
static i128 is1(uint64_t x) { return i128(x) * (x + 1) / 2; }
static i128 is2(uint64_t x) { return i128(x) * (x + 1) * (2*x + 1) / 6; }
static i128 is3(uint64_t x) { i128 q=is1(x); return q*q; }
static i128 irange(i128 (*f)(uint64_t), uint64_t lo, uint64_t hi) {
  return f(hi) - (lo ? f(lo-1) : 0);
}

// P(q,f)=sum_{r=1}^q min(r,f), analytically summed over q=a-3*i.
static u128 sum_high_prefix_step3(int64_t a,uint64_t n,uint64_t f) {
  if(a<=0) return 0;
  const uint64_t last=std::min<uint64_t>(n,(uint64_t(a)-1)/3);
  auto segment=[&](uint64_t lo,uint64_t hi,bool above)->i128 {
    if(lo>hi)return 0;
    const i128 cnt=i128(hi-lo+1),aa=a;
    const i128 si=irange(is1,lo,hi),si2=irange(is2,lo,hi),si3=irange(is3,lo,hi);
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
  assert(ans>=0);
  return u128(ans);
}
static u128 finite_high(uint64_t m,uint64_t k,uint64_t M) {
  const uint64_t fuel=M+1>=4*k ? M+1-4*k : 0;
  return sum_high_prefix_step3(m,2*k,fuel)-
    sum_high_prefix_step3(int64_t(m)-int64_t(2*k+1),2*k,fuel);
}

// Tables for the unbounded lattice 3*e+2*z <= C.  F is its cardinality,
// G the sum of z, and H(C)=sum_{y=0}^C F(y).  They turn the exact clipped
// low block into O(k), rather than expanding four nested finite sums.
struct LatticeTables {
  std::vector<u128> F,G,H;
  explicit LatticeTables(uint64_t cap):F(cap+1),G(cap+1),H(cap+1) {
    std::vector<u128> at(cap+1),zat(cap+1);
    for(uint64_t e=0;3*e<=cap;++e)
      for(uint64_t z=0, w=3*e;w<=cap;++z,w+=2) {
        ++at[w]; zat[w]+=z;
      }
    for(uint64_t c=0;c<=cap;++c) {
      F[c]=at[c]+(c?F[c-1]:0);
      G[c]=zat[c]+(c?G[c-1]:0);
      H[c]=F[c]+(c?H[c-1]:0);
    }
  }
  u128 get(const std::vector<u128>&v,int64_t c) const {
    return c<0?0:v.at(uint64_t(c));
  }
  u128 f(int64_t c)const{return get(F,c);}
  u128 g(int64_t c)const{return get(G,c);}
  u128 h(int64_t c)const{return get(H,c);}
};

static u128 f_rect(const LatticeTables&T,uint64_t t,uint64_t n,int64_t c) {
  const int64_t a=3*int64_t(t), b=2*int64_t(n+1);
  return T.f(c)-T.f(c-a)-T.f(c-b)+T.f(c-a-b);
}
static u128 g_rect(const LatticeTables&T,uint64_t t,uint64_t n,int64_t c) {
  const int64_t a=3*int64_t(t), q=int64_t(n+1), b=2*q;
  return T.g(c)-T.g(c-a)-T.g(c-b)-u128(q)*T.f(c-b)
    +T.g(c-a-b)+u128(q)*T.f(c-a-b);
}
static u128 h_rect(const LatticeTables&T,uint64_t t,uint64_t n,int64_t c) {
  const int64_t a=3*int64_t(t),b=2*int64_t(n+1);
  return T.h(c)-T.h(c-a)-T.h(c-b)+T.h(c-a-b);
}
static u128 sum_hinge2(int64_t a,uint64_t n) {
  if(a<=0)return 0;
  uint64_t q=std::min<uint64_t>(n,uint64_t(a-1)/2), cnt=q+1;
  return u128(cnt)*uint64_t(a)-u128(q)*cnt;
}
static u128 sum_prefix_hinge2(int64_t C,uint64_t n) {
  // sum_{a=1}^C sum_{z=0}^n max(a-2*z,0)
  if(C<=0)return 0;
  uint64_t q=std::min<uint64_t>(n,uint64_t(C-1)/2),cnt=q+1;
  // sum_z ((C-2z)(C-2z+1)/2)
  i128 cc=C;
  i128 twice=i128(cnt)*(cc*cc+cc)-i128(4*cc+2)*is1(q)+4*is2(q);
  assert(twice>=0 && twice%2==0);
  return u128(twice/2);
}

static u128 exact_low(const LatticeTables&T,uint64_t m,uint64_t k,
    uint64_t tcap=std::numeric_limits<uint64_t>::max()) {
  const uint64_t D=4*k,p=std::min<uint64_t>(2*k,tcap);
  uint64_t q0=std::min<uint64_t>(D-1,(m?m-1:0));
  q0=std::min<uint64_t>(q0,(m?m-1:0)/2);
  u128 out=0;
  if(m) {
    const u128 cnt=q0+1, sh=s1(q0), sh2=s2(q0);
    out=cnt*D*m-u128(2*D+m)*sh+2*sh2;
  }
  for(uint64_t t=1;t<=p;++t) {
    const uint64_t nn=D-2*t;
    // d=t..D-t, written n=d-t.  Each (e,z) persists for n=z..nn.
    for(int off=1;off<=2;++off) {
      u128 fr=f_rect(T,t,nn,int64_t(m)-off);
      u128 zr=g_rect(T,t,nn,int64_t(m)-off);
      out+=u128(nn+1)*fr-zr;
    }
    int64_t aa=int64_t(m)-3*int64_t(t);
    if(aa>0) {
      uint64_t q=std::min<uint64_t>(nn,uint64_t(aa-1)/2),cnt=q+1;
      u128 sh=s1(q),sh2=s2(q);
      out+=u128(nn+1)*(u128(cnt)*uint64_t(aa)-2*sh)
        -(u128(uint64_t(aa))*sh-2*sh2);
    }
    // d=D-t+c, c=1..t-1.  Consecutive threshold sums use H_rect.
    if(t>=2) {
      out+=h_rect(T,t,nn,int64_t(m)-2)-h_rect(T,t,nn,int64_t(m)-int64_t(t)-1);
      out+=h_rect(T,t,nn,int64_t(m)-3)-h_rect(T,t,nn,int64_t(m)-int64_t(t)-2);
      out+=sum_prefix_hinge2(int64_t(m)-3*int64_t(t)-1,nn)
        -sum_prefix_hinge2(int64_t(m)-4*int64_t(t),nn);
    }
  }
  return out;
}

static u128 weighted_count(uint64_t k,uint64_t d) {
  if(d<=2*k)return u128(d+1)*(d+2)/2;
  uint64_t j=d-2*k;
  return (u128(2*k+1)*(2*k+2)+u128(4*k+2)*j-u128(j)*(j+1))/2;
}
struct LowPrefixes { std::vector<u128> c,dc; };
static LowPrefixes low_prefixes(uint64_t k) {
  uint64_t D=4*k; LowPrefixes p{{0},{0}};
  p.c.reserve(D+1);p.dc.reserve(D+1);
  for(uint64_t d=0;d<D;++d) {
    u128 x=weighted_count(k,d);
    p.c.push_back(p.c.back()+x);p.dc.push_back(p.dc.back()+u128(d)*x);
  }
  return p;
}
static u128 low_optimistic_lower(const LowPrefixes&p,uint64_t m,uint64_t D) {
  uint64_t q=std::min<uint64_t>(D,m);
  return u128(m)*p.c[q]-p.dc[q];
}

struct PairInfo { i128 c2,c1,c0; uint64_t pairs; };
static PairInfo pair_info(uint64_t k) {
  const uint64_t D=4*k,L=W-1; i128 c2=0,c1=0,c0=0;uint64_t pairs=0;
  // Under 4*k <= M+1, all derivative pairs have positive pairWidth.
  for(uint64_t t=0;t<=D/2;++t) {
    const uint64_t c=(W-2)*t,r=D-2*t;
    const u128 n=r+1,sr=s1(r),sr2=s2(r);
    pairs+=r+1;c2+=n;
    c1+=-2*i128(n)*c+i128(n)*W-2*i128(L)*i128(sr);
    c0+=i128(n)*c*c-i128(n)*W*c+2*i128(L)*c*i128(sr)-
      i128(W)*L*i128(sr)+i128(L)*L*i128(sr2);
  }
  return {c2,c1,c0,pairs};
}
static u128 pair_eval(const PairInfo&p,uint64_t B) {
  i128 x=p.c2*i128(B)*B+p.c1*i128(B)+p.c0;assert(x>=0);return u128(x);
}
static u128 columns_upper(const PairInfo&p,uint64_t B) {
  // widthSum identity: 2W*width = b^2+Wb+W*r-r^2, with W*r-r^2 <= W^2/4.
  u128 num=pair_eval(p,B)+u128(p.pairs)*(u128(W)*W/4);
  return (num+2*W-1)/(2*W);
}
static u128 width_sum(uint64_t b) {
  if(!b)return 0;uint64_t q=(b-1)/W;
  return u128(q+1)*b-u128(W)*q*(q+1)/2;
}
static u128 width_sequence_segment(uint64_t base,uint64_t qb,uint64_t lo,uint64_t hi) {
  if(lo>hi)return 0;
  i128 n=hi-lo+1,sr=irange(is1,lo,hi),sr2=irange(is2,lo,hi),L=W-1,b=base,q=qb;
  i128 twice=2*((q+1)*b*n-((q+1)*L+b)*sr+L*sr2)-
    i128(W)*(q*(q+1)*n-(2*q+1)*sr+sr2);
  assert(twice>=0&&twice%2==0);return u128(twice/2);
}
static u128 columns(uint64_t C,uint64_t E) {
  u128 out=0;
  for(uint64_t t=0;t<=E/2;++t) {
    if(u128(W-2)*t>=C)break;
    uint64_t base=C-(W-2)*t,n0=base-1,R=std::min(E-2*t,n0/(W-1));
    uint64_t q0=n0/W,rem=n0%W,split=W-rem;
    if(split)out+=width_sequence_segment(base,q0,0,std::min(R,split-1));
    if(R>=split)out+=width_sequence_segment(base,q0+1,split,R);
  }
  return out;
}
static u128 active_fibres_lower(uint64_t C,uint64_t E) {
  if(!C)return 0;
  // Drop the nonnegative quotient-carry indicators.  The remaining affine
  // sum is a certified lower bound (and max(sum,0) stays a lower bound).
  if(E<W && E<=C/W+1) {
    uint64_t h=E/2,q=C/W,eps=C%W?1:0;
    i128 raw;
    if(E%2==0) {
      i128 pairs=i128(h+1)*(h+1);
      raw=pairs*(i128(q)+eps-i128(h));
    } else {
      i128 pairs=i128(h+1)*(h+2);
      raw=pairs*(i128(q)+eps)-i128(2*h+1)*pairs/2;
    }
    return raw>0?u128(raw):0;
  }
  u128 out=0;
  for(uint64_t t=0;t<=E/2;++t) {
    if(u128(W-2)*t>=C)break;
    uint64_t base=C-(W-2)*t,r=std::min(E-2*t,(base-1)/(W-1));
    uint64_t q=(base-1)/W,rem=(base-1)%W;
    uint64_t extra=r>=W-rem?r-(W-rem)+1:0;
    out+=u128(r+1)*(q+1)+extra-s1(r);
  }
  return out;
}
struct Source {uint64_t k,m,B,D,M;u128 rank,cols;i128 kernel;};
static u128 band_lower(const Source&s,uint64_t cap,bool derivative) {
  uint64_t rho=derivative?cap+1:2;
  uint64_t g=derivative?(W-2)*((rho+1)/2):(W-2)*(cap+1);
  u128 out=0;
  for(uint64_t j=1;j*rho<=s.D;++j) {
    u128 spent=u128(j)*g+u128(j-1)*DELTA;
    if(spent>=s.B)break;
    uint64_t top=s.B-uint64_t(spent),E=s.D-j*rho;
    if(top>DELTA)out+=u128(DELTA)*active_fibres_lower(top-DELTA,E);
  }
  return out;
}
static u128 band_exact(const Source&s,uint64_t cap,bool derivative) {
  uint64_t rho=derivative?cap+1:2;
  uint64_t g=derivative?(W-2)*((rho+1)/2):(W-2)*(cap+1);
  u128 out=0;
  for(uint64_t j=1;j*rho<=s.D;++j) {
    u128 spent=u128(j)*g+u128(j-1)*DELTA;
    if(spent>=s.B)break;
    uint64_t top=s.B-uint64_t(spent),E=s.D-j*rho;
    out+=columns(top,E)-columns(top-DELTA,E);
  }
  return out;
}

static uint64_t brute_asym(uint64_t m,uint64_t d,uint64_t q,uint64_t t) {
  uint64_t out=0;
  for(uint64_t b=0;b<=q;++b)for(uint64_t e=0;e<=std::min(q-b,t);++e) {
    uint64_t r=(q-b)-std::min(q-b,t),v=d-q+2*r+3*e;
    out+=m>v?m-v:0;
  }
  return out;
}
static uint64_t brute_low(uint64_t m,uint64_t k) {
  uint64_t D=4*k,p=2*k,out=0;
  for(uint64_t d=0;d<D;++d) {
    uint64_t ranks=0,over=0;
    for(uint64_t i=0;i<=p;++i)ranks+=brute_asym(m,d,std::min(d,D-i),i);
    for(uint64_t i=0;i<p;++i)over+=brute_asym(m,d,std::min(d,D-i-1),i);
    out+=ranks-over;
  }
  return out;
}

int main(int argc,char**argv) {
  LatticeTables tab(MAX_M+10);
  if(argc>1 && std::string(argv[1])=="selfcheck") {
    for(uint64_t k=1;k<=6;++k)for(uint64_t m=1;m<=60;++m) {
      u128 a=exact_low(tab,m,k),b=brute_low(m,k);
      if(a!=b){std::cerr<<"LOW_MISMATCH k="<<k<<" m="<<m<<" a="<<show(a)<<" b="<<show(b)<<"\n";return 2;}
      auto p=low_prefixes(k);assert(low_optimistic_lower(p,m,4*k)<=a);
    }
    std::cout<<"SELFCHECK exact clipped low rank agrees with literal Lean sums\n";return 0;
  }
  if(argc>1 && std::string(argv[1])=="profile") {
    uint64_t k=std::stoull(argv[2]),m=std::stoull(argv[3]),B=m*A,D=4*k,M=B/(W-2);
    uint64_t jcap=argc>4?std::stoull(argv[4]):211;
    uint64_t dcap=argc>5?std::stoull(argv[5]):55;
    u128 low=exact_low(tab,m,k),high=finite_high(m,k,M),rank=low+high,cols=columns(B,D);
    Source s{k,m,B,D,M,rank,cols,i128(cols)-i128(N*rank)};
    u128 jb=band_exact(s,jcap,false),db=band_exact(s,dcap,true);
    std::cout<<"PROFILE k="<<k<<" m="<<m<<" B="<<B<<" M="<<M
      <<" low="<<show(low)<<" high="<<show(high)<<" rank="<<show(rank)
      <<" columns="<<show(cols)<<" kernel="<<showi(s.kernel)
      <<" J"<<jcap<<"="<<show(jb)<<" Jmargin="<<showi(s.kernel-i128(jb))
      <<" D"<<dcap<<"="<<show(db)<<" Dmargin="<<showi(s.kernel-i128(db))<<"\n";
    return 0;
  }
  if(argc>1 && std::string(argv[1])=="sourceprofile") {
    uint64_t k=std::stoull(argv[2]),m=std::stoull(argv[3]),B=m*A,D=4*k,M=B/(W-2);
    auto lp=low_prefixes(k);auto pi=pair_info(k);
    u128 low=exact_low(tab,m,k),lowlo=low_optimistic_lower(lp,m,D);
    u128 lowq=exact_low(tab,m,k,k/4),lowh=exact_low(tab,m,k,k/2);
    u128 high=finite_high(m,k,M),cols=columns(B,D),colhi=columns_upper(pi,B);
    i128 ker=i128(cols)-i128(N*(low+high));
    i128 opt=i128(colhi)-i128(N*(lowlo+high));
    std::cout<<"SOURCEPROFILE k="<<k<<" m="<<m<<" ratio="<<(double(m)/k)
      <<" low="<<show(low)<<" lowLower="<<show(lowlo)
      <<" correction="<<show(low-lowlo)<<" partialQuarter="<<show(lowq)
      <<" partialHalf="<<show(lowh)<<" high="<<show(high)
      <<" kernel="<<showi(ker)<<" optimistic="<<showi(opt)<<"\n";
    return 0;
  }
  if(argc>1 && std::string(argv[1])=="coarse") {
    uint64_t step=argc>2?std::stoull(argv[2]):32;
    struct Hit{i128 ker;uint64_t k,m;};std::vector<Hit> hits;
    i128 best=std::numeric_limits<i128>::min();Hit bh{};uint64_t tested=0;
    uint64_t kmax=(uint64_t(MAX_M)*A/(W-2)+1)/4;
    for(uint64_t k=1;k<=kmax;++k) {
      auto pi=pair_info(k);uint64_t mlo=(u128(4*k-1)*(W-2)+A-1)/A;
      for(uint64_t m=mlo;m<=MAX_M;) {
        uint64_t B=m*A,M=B/(W-2);u128 rank=exact_low(tab,m,k)+finite_high(m,k,M);
        i128 ker=i128(columns_upper(pi,B))-i128(N*rank);++tested;
        if(ker>best){best=ker;bh={ker,k,m};}if(ker>0)hits.push_back({ker,k,m});
        if(MAX_M-m<step)break;m+=step;
      }
      // Include both upper endpoint and the important m=8*k boundary.
      for(uint64_t m:{MAX_M,8*k-1,8*k})if(m>=mlo&&m<=MAX_M) {
        uint64_t B=m*A,M=B/(W-2);u128 rank=exact_low(tab,m,k)+finite_high(m,k,M);
        i128 ker=i128(columns_upper(pi,B))-i128(N*rank);++tested;
        if(ker>best){best=ker;bh={ker,k,m};}if(ker>0)hits.push_back({ker,k,m});
      }
    }
    uint64_t mink=UINT64_MAX,maxk=0,minm=UINT64_MAX,maxm=0;
    for(auto h:hits){mink=std::min(mink,h.k);maxk=std::max(maxk,h.k);minm=std::min(minm,h.m);maxm=std::max(maxm,h.m);}
    std::cout<<"COARSE step="<<step<<" tested="<<tested<<" positive="<<hits.size()
      <<" kRange="<<mink<<".."<<maxk<<" mRange="<<minm<<".."<<maxm
      <<" bestUpperKernel="<<showi(best)<<" at="<<bh.k<<","<<bh.m<<"\n";
    return 0;
  }
  if(argc>1 && std::string(argv[1])=="focus") {
    uint64_t rlo=argc>2?std::stoull(argv[2]):7000;
    uint64_t rhi=argc>3?std::stoull(argv[3]):7999;
    const bool optimisticAll = argc > 5 && std::string(argv[5]) == "optimistic";
    struct Hit{i128 upperD;uint64_t k,m;};std::vector<Hit> hits;
    uint64_t tested=0,sourcePositive=0; i128 maxUpperD=std::numeric_limits<i128>::min();
    uint64_t muk=0,mum=0;
    uint64_t kmax=(uint64_t(MAX_M)*A/(W-2)+1)/4;
    #pragma omp parallel
    {
      std::vector<Hit> localHits;uint64_t localTested=0,localPositive=0;
      i128 localMax=std::numeric_limits<i128>::min();uint64_t lk=0,lm=0;
      #pragma omp for schedule(dynamic,4)
      for(int64_t kk=1;kk<=int64_t(kmax);++kk) {
        uint64_t k=uint64_t(kk);auto pi=pair_info(k);auto lpref=low_prefixes(k);
        uint64_t feasibleLo=(u128(4*k-1)*(W-2)+A-1)/A;
        uint64_t lo=std::max<uint64_t>(feasibleLo,(u128(k)*rlo+999)/1000);
        uint64_t hi=std::min<uint64_t>(MAX_M,u128(k)*rhi/1000);
        if(lo>hi)continue;
        for(uint64_t m=lo;m<=hi;++m) {
          uint64_t B=m*A,M=B/(W-2);++localTested;
          u128 low=(optimisticAll || m>=8*k-1)?
            low_optimistic_lower(lpref,m,4*k):exact_low(tab,m,k);
          u128 rank=low+finite_high(m,k,M);
          i128 kup=i128(columns_upper(pi,B))-i128(N*rank);if(kup<=0)continue;
          ++localPositive;Source s{k,m,B,4*k,M,rank,0,kup};
          i128 ud=kup-i128(band_lower(s,55,true));
          if(ud>localMax){localMax=ud;lk=k;lm=m;}
          if(ud>0)localHits.push_back({ud,k,m});
        }
      }
      #pragma omp critical
      {
        tested+=localTested;sourcePositive+=localPositive;
        hits.insert(hits.end(),localHits.begin(),localHits.end());
        if(localMax>maxUpperD){maxUpperD=localMax;muk=lk;mum=lm;}
      }
    }
    std::sort(hits.begin(),hits.end(),[](auto&a,auto&b){return a.upperD>b.upperD;});
    std::cout<<"FOCUS ratioPermille="<<rlo<<".."<<rhi<<" tested="<<tested
      <<" sourceUpperPositive="<<sourcePositive<<" surviveD55Necessary="<<hits.size()
      <<" maxUpperD="<<showi(maxUpperD)<<" at="<<muk<<","<<mum<<"\n";
    i128 bestD=std::numeric_limits<i128>::min(),bestMin=std::numeric_limits<i128>::min();
    uint64_t bdk=0,bdm=0,bmk=0,bmm=0;size_t checked=0,both=0;
    const bool exhaustive = argc > 4 && std::string(argv[4]) == "exhaustive";
    const size_t exactLimit = exhaustive ? hits.size() : std::min<size_t>(hits.size(), 500);
    for(size_t i=0;i<exactLimit;++i) {
      if(!exhaustive && bestD!=std::numeric_limits<i128>::min()&&hits[i].upperD<=bestD)break;
      uint64_t k=hits[i].k,m=hits[i].m,B=m*A,D=4*k,M=B/(W-2);
      auto lpref=low_prefixes(k);
      u128 low=(optimisticAll || m>=8*k-1)?
        low_optimistic_lower(lpref,m,D):exact_low(tab,m,k);
      u128 rank=low+finite_high(m,k,M),cols=columns(B,D);
      Source s{k,m,B,D,M,rank,cols,i128(cols)-i128(N*rank)};
      u128 db=band_exact(s,55,true),jb=band_exact(s,211,false);
      i128 dm=s.kernel-i128(db),jm=s.kernel-i128(jb);++checked;
      if(dm>bestD){bestD=dm;bdk=k;bdm=m;}
      if(dm>0&&jm>0){++both;i128 mm=std::min(dm,jm);if(mm>bestMin){bestMin=mm;bmk=k;bmm=m;}}
      if(i<20 || (dm>0&&jm>0))std::cout<<"FHIT i="<<i<<" k="<<k<<" m="<<m
        <<" upperD="<<showi(hits[i].upperD)<<" kernel="<<showi(s.kernel)
        <<" D55margin="<<showi(dm)<<" J211margin="<<showi(jm)<<"\n";
    }
    std::cout<<"FOCUS_EXACT checked="<<checked<<" both="<<both
      <<" bestD="<<showi(bestD)<<" at="<<bdk<<","<<bdm
      <<" bestMin="<<showi(bestMin)<<" at="<<bmk<<","<<bmm<<"\n";
    return 0;
  }
  if(argc>1 && (std::string(argv[1])=="cover" ||
      std::string(argv[1])=="coverD")) {
    const bool includeD = std::string(argv[1])=="coverD";
    uint64_t rlo=argc>2?std::stoull(argv[2]):0;
    uint64_t rhi=argc>3?std::stoull(argv[3]):5999;
    uint64_t step=argc>4?std::stoull(argv[4]):32;
    uint64_t onlyKLo=argc>5?std::stoull(argv[5]):1;
    struct Block{i128 upper;uint64_t k,lo,hi;};std::vector<Block> survivors;
    uint64_t blocks=0,points=0; i128 worst=std::numeric_limits<i128>::min();
    Block wb{};uint64_t kmax=argc>6?std::stoull(argv[6]):(uint64_t(MAX_M)*A/(W-2)+1)/4;
    #pragma omp parallel
    {
      std::vector<Block> local;uint64_t lb=0,lp=0;i128 lw=std::numeric_limits<i128>::min();Block lwb{};
      #pragma omp for schedule(dynamic,4)
      for(int64_t kk=int64_t(onlyKLo);kk<=int64_t(kmax);++kk) {
        uint64_t k=uint64_t(kk);
        uint64_t feasibleLo=(u128(4*k-1)*(W-2)+A-1)/A;
        uint64_t lo=std::max<uint64_t>(feasibleLo,(u128(k)*rlo+999)/1000);
        uint64_t hi=std::min<uint64_t>(MAX_M,u128(k)*rhi/1000);
        if(lo>hi)continue;
        for(uint64_t left=lo;left<=hi;) {
          uint64_t right=std::min<uint64_t>(hi,left+step-1);
          uint64_t BL=left*A,ML=BL/(W-2),BR=right*A;
          u128 rankLeft=exact_low(tab,left,k)+finite_high(left,k,ML);
          // Both numerical rank caps and columns are monotone in m.  Hence
          // columns(right)-N*rank(left) bounds every kernel in this block.
          i128 up=i128(columns(BR,4*k))-i128(N*rankLeft);
          // The certified derivative-band lower bound is monotone in B.
          // Subtracting it at the left endpoint therefore preserves an upper
          // bound for every point in the block.
          if(includeD) {
            Source leftSource{k,left,BL,4*k,ML,rankLeft,0,0};
            up-=i128(band_lower(leftSource,55,true));
          }
          ++lb;lp+=right-left+1;
          if(up>lw){lw=up;lwb={up,k,left,right};}
          if(up>0)local.push_back({up,k,left,right});
          if(right==hi)break;left=right+1;
        }
      }
      #pragma omp critical
      {
        blocks+=lb;points+=lp;survivors.insert(survivors.end(),local.begin(),local.end());
        if(lw>worst){worst=lw;wb=lwb;}
      }
    }
    std::sort(survivors.begin(),survivors.end(),[](auto&a,auto&b){return a.upper>b.upper;});
    uint64_t sklo=UINT64_MAX,skhi=0,srlo=UINT64_MAX,srhi=0;
    for(auto b:survivors){sklo=std::min(sklo,b.k);skhi=std::max(skhi,b.k);
      srlo=std::min<uint64_t>(srlo,u128(1000000)*b.lo/b.k);
      srhi=std::max<uint64_t>(srhi,u128(1000000)*b.hi/b.k);}
    std::cout<<(includeD?"COVER_D":"COVER")<<" ratioPermille="<<rlo<<".."<<rhi<<" step="<<step
      <<" points="<<points<<" blocks="<<blocks<<" survivingBlocks="<<survivors.size()
      <<" survivorK="<<sklo<<".."<<skhi<<" survivorRatioPPM="<<srlo<<".."<<srhi
      <<" worstBlockUpper="<<showi(worst)<<" at="<<wb.k<<","<<wb.lo<<".."<<wb.hi<<"\n";
    for(size_t i=0;i<std::min<size_t>(20,survivors.size());++i)
      std::cout<<"BLOCK i="<<i<<" upper="<<showi(survivors[i].upper)<<" k="<<survivors[i].k
        <<" range="<<survivors[i].lo<<".."<<survivors[i].hi<<"\n";
    return 0;
  }
  struct Maybe {i128 optimistic;uint64_t k,m;};
  std::vector<Maybe> possible;
  uint64_t feasible=0,optPositive=0;
  i128 bestOpt=std::numeric_limits<i128>::min();Maybe best{};
  const uint64_t kmax=(uint64_t(MAX_M)*A/(W-2)+1)/4;
  for(uint64_t k=1;k<=kmax;++k) {
    PairInfo pi=pair_info(k);LowPrefixes lp=low_prefixes(k);
    uint64_t mlo=(u128(4*k-1)*(W-2)+A-1)/A;
    mlo=std::max<uint64_t>(1,mlo);
    for(uint64_t m=mlo;m<=MAX_M;++m) {
      uint64_t B=m*A,M=B/(W-2);if(4*k>M+1)continue;++feasible;
      u128 ranklo=low_optimistic_lower(lp,m,4*k)+finite_high(m,k,M);
      i128 opt=i128(columns_upper(pi,B))-i128(N*ranklo);
      if(opt>bestOpt){bestOpt=opt;best={opt,k,m};}
      if(opt<=0)continue;++optPositive;
      // Necessary D55 test, using an exact per-fibre lower bound on the exact band.
      Source s{k,m,B,4*k,M,ranklo,0,opt};
      u128 dl=band_lower(s,55,true);
      if(opt>i128(dl))possible.push_back({opt-i128(dl),k,m});
    }
  }
  std::sort(possible.begin(),possible.end(),[](auto&a,auto&b){return a.optimistic>b.optimistic;});
  std::cout<<"SCAN W="<<W<<" MAX_M="<<MAX_M<<" kmax="<<kmax
    <<" feasible="<<feasible<<" optimisticSourcePositive="<<optPositive
    <<" surviveNecessaryD55="<<possible.size()<<" bestSourceOptimistic="<<showi(bestOpt)
    <<" at="<<best.k<<","<<best.m<<"\n";
  size_t take=std::min<size_t>(possible.size(),200);
  i128 bestD=std::numeric_limits<i128>::min(),bestBoth=std::numeric_limits<i128>::min();
  uint64_t bdk=0,bdm=0,bbk=0,bbm=0;size_t both=0;
  for(size_t i=0;i<take;++i) {
    uint64_t k=possible[i].k,m=possible[i].m,B=m*A,D=4*k,M=B/(W-2);
    u128 rank=exact_low(tab,m,k)+finite_high(m,k,M),cols=columns(B,D);
    Source s{k,m,B,D,M,rank,cols,i128(cols)-i128(N*rank)};
    u128 db=band_exact(s,55,true),jb=band_exact(s,211,false);
    i128 dm=s.kernel-i128(db),jm=s.kernel-i128(jb);
    if(dm>bestD){bestD=dm;bdk=k;bdm=m;}
    if(dm>0&&jm>0){++both;i128 mm=std::min(dm,jm);if(mm>bestBoth){bestBoth=mm;bbk=k;bbm=m;}}
    if(i<20)std::cout<<"CAND i="<<i<<" k="<<k<<" m="<<m
      <<" optimisticD="<<showi(possible[i].optimistic)<<" kernel="<<showi(s.kernel)
      <<" D55margin="<<showi(dm)<<" J211margin="<<showi(jm)<<"\n";
  }
  std::cout<<"EXACT_TOP checked="<<take<<" both="<<both<<" bestD55="<<showi(bestD)
    <<" at="<<bdk<<","<<bdm<<" bestBothMin="<<showi(bestBoth)
    <<" at="<<bbk<<","<<bbm<<"\n";
}
