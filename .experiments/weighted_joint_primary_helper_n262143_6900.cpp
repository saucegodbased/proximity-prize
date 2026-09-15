// Joint primary/helper ledger optimizer for the W=133225 one-exception
// identity universe.  This imports the previously cross-checked finite-prefix
// arithmetic, but recomputes every N-dependent source and ledger expression
// at N=262143.
#define N OLD_OPTIMIZER_N
#define TARGET OLD_OPTIMIZER_TARGET
#define main old_weighted_optimizer_main
#include "weighted_scalar_w133219_full_optimizer_6900.cpp"
#undef main
#undef TARGET
#undef N

constexpr uint64_t JOINT_N = 262143;
constexpr uint64_t JOINT_TARGET = 263611557201785349ULL;

static Source joint_source_with_pair(uint64_t k, uint64_t m,
    const PairCoeff &pc) {
  const uint64_t B = m*A, D = 4*k, M = B/(W-2);
  const u128 rank = finite_rank_general_fast(m,k,M);
  return {k,m,B,D,2*k,M,rank,
    i128(pair_eval(pc,B)/(2*W))-i128(JOINT_N*rank)};
}

static Source joint_source(uint64_t k, uint64_t m) {
  return joint_source_with_pair(k,m,pair_coeff(k));
}

static u128 joint_first_regular(uint64_t y,uint64_t r) {
  const u128 cost=(1+u128(2)*W*y)*r+u128(W)*(2*r-1)*y;
  return ceil_div(u128(JOINT_N-W)*cost,A-W);
}

static u128 joint_cleanup(const Source &p) {
  const uint64_t y=(2*p.T-1)*p.M,r=(2*p.T-1)*p.D;
  // The identity-core semantic consumer already includes the Y-only subcase
  // in its T-free family, so there is no extra +p.M term here.
  return joint_first_regular(y,r)+u128(2*r-1)*y+
    joint_first_regular(p.M,p.D)+u128(2*p.D-1)*p.M;
}

static uint64_t joint_min_cap(const Source &h,bool derivative) {
  uint64_t lo=0,hi=1;
  if(band_formula(h,0,derivative)<u128(h.kernel))return 0;
  while(band_formula(h,hi,derivative)>=u128(h.kernel))hi*=2;
  while(lo+1<hi) {
    const uint64_t mid=(lo+hi)/2;
    if(band_formula(h,mid,derivative)<u128(h.kernel))hi=mid;else lo=mid;
  }
  return hi;
}

static u128 joint_cheap(uint64_t J,uint64_t D,uint64_t v) {
  const uint64_t T=D/2;
  const Flag cf={J-D,D-T,T},ca=af(J,D,T);
  return ceil_div(u128(JOINT_N-v)*(JOINT_N-v)*mixed(cf,ca,ca),
    u128(A-v)*(A-v));
}

static u128 joint_exits(const Source&p,const Source&h,uint64_t v) {
  return ceil_div(u128(JOINT_N-v)*mixed(sf(p),sf(h),af(p.M,p.D,p.T)),A-v);
}

static void optimize_primary_for_helper(uint64_t hk,uint64_t hm,
    uint64_t J,uint64_t D,uint64_t v) {
  const Source h=joint_source(hk,hm);
  const u128 cheap=joint_cheap(J,D,v);
  Best best;
  u128 minCleanup=~u128(0);uint64_t minCleanupK=0,minCleanupM=0;
  uint64_t tested=0,sourcePositive=0,ledgerPossible=0;
  const uint64_t kmax=11810/8;
  for(uint64_t k=1;k<=kmax;++k) {
    const PairCoeff pc=pair_coeff(k);
    const uint64_t lo=std::max<uint64_t>(1,8*k-1);
    const uint64_t hi=std::min<uint64_t>(11810,12*k);
    if(lo>hi)continue;
    for(uint64_t m=lo;m<=hi;++m) {
      ++tested;const Source p=joint_source_with_pair(k,m,pc);
      if(p.kernel<=0)continue;++sourcePositive;
      const u128 clean=joint_cleanup(p);
      if(clean<minCleanup){minCleanup=clean;minCleanupK=k;minCleanupM=m;}
      if(cheap+clean>=JOINT_TARGET)continue;++ledgerPossible;
      const u128 exits=joint_exits(p,h,v),total=cheap+clean+exits;
      if(total<best.total)best={total,cheap,exits,clean,p.k,p.m,h.k,h.m,J,D,v,0,0};
    }
  }
  std::cout<<"PRIMARY_FOR_HELPER tested="<<tested
    <<" sourcePositive="<<sourcePositive<<" ledgerPossible="<<ledgerPossible
    <<" minCleanup="<<show(minCleanup)<<" minCleanupAt="<<minCleanupK<<","<<minCleanupM
    <<" total="<<show(best.total)<<" gap="<<showi(i128(best.total)-JOINT_TARGET)
    <<" pk="<<best.pk<<" pm="<<best.pm<<" hk="<<hk<<" hm="<<hm
    <<" J="<<J<<" D="<<D<<" cheap="<<show(best.cheap)
    <<" exits="<<show(best.exits)<<" cleanup="<<show(best.clean)<<"\n";
}

static void profile_joint(uint64_t k,uint64_t m) {
  const Source s=joint_source(k,m);
  const uint64_t J=joint_min_cap(s,false),D=joint_min_cap(s,true);
  std::cout<<"JOINT_PROFILE k="<<k<<" m="<<m<<" B="<<s.B<<" M="<<s.M
    <<" rank="<<show(s.rank)<<" kernel="<<showi(s.kernel)
    <<" J="<<J<<" D="<<D
    <<" Jmargin="<<showi(s.kernel-i128(band_formula(s,J,false)))
    <<" Dmargin="<<showi(s.kernel-i128(band_formula(s,D,true)))
    <<" helperFlag="<<show(sf(s).z)<<","<<show(sf(s).y)<<","<<show(sf(s).a)
    <<"\n";
}

int main(int argc,char**argv) {
  W=133225;
  if(argc>1&&std::string(argv[1])=="profile") {
    profile_joint(std::stoull(argv[2]),std::stoull(argv[3]));return 0;
  }
  if(argc>1&&std::string(argv[1])=="primary") {
    optimize_primary_for_helper(std::stoull(argv[2]),std::stoull(argv[3]),
      std::stoull(argv[4]),std::stoull(argv[5]),
      argc>6?std::stoull(argv[6]):68763);return 0;
  }
  profile_joint(1312,11803);
  optimize_primary_for_helper(1312,11803,212,55,68763);
}
