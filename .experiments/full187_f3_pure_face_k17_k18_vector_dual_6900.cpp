#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <sys/resource.h>
#include <vector>

#include <givaro/modular.h>
#include <linbox/algorithms/polynomial-matrix/order-basis.h>
#include <linbox/matrix/polynomial-matrix.h>

namespace {
int64_t mul_mod(uint32_t a, uint32_t b, uint32_t p) {
    return static_cast<int64_t>((__int128)a * b % p);
}
int64_t neg_mod(uint32_t a, uint32_t p) { return a ? p - a : 0; }
}

int main(int argc, char** argv) {
    const std::string input = argc > 1 ? argv[1] :
        "/tmp/full187_f3_pure_face_k17_k18_vector_dual_6900.bin";
    std::ifstream in(input, std::ios::binary);
    if (!in) { std::cerr << "cannot open " << input << "\n"; return 2; }
    std::array<char,8> magic{};
    std::array<uint32_t,12> h{};
    in.read(magic.data(), magic.size());
    in.read(reinterpret_cast<char*>(h.data()), sizeof(h));
    if (std::string(magic.data(), 7) != "F3K4X2D" ||
        h[9] != 6 || h[10] != 4) {
        std::cerr << "bad header\n"; return 2;
    }
    const uint32_t prime=h[0], edeg=h[1], mdeg=h[2], rwidth=h[3];
    const uint32_t zwidth=h[4], outrows=h[5], lowbound=h[6];
    const uint32_t order=h[7], threshold=h[8], column_shift=h[11];
    std::array<uint32_t,4> bounds{}, initial_shift{};
    in.read(reinterpret_cast<char*>(bounds.data()), sizeof(bounds));
    in.read(reinterpret_cast<char*>(initial_shift.data()),
            sizeof(initial_shift));
    if (!in || mdeg != 18*edeg || lowbound+outrows != mdeg ||
        order != edeg+outrows || column_shift != 57193) {
        std::cerr << "inconsistent dimensions\n"; return 2;
    }

    // int64 storage is required for this 31-bit field.
    using Field = Givaro::Modular<int64_t>;
    using PMat = LinBox::PolynomialMatrix<Field, LinBox::PMType::polfirst>;
    Field F(prime);
    PMat series(F,4,2,order);
    std::vector<uint32_t> data(order);
    for (size_t which=0; which<6; ++which) {
        in.read(reinterpret_cast<char*>(data.data()),
                data.size()*sizeof(uint32_t));
        if (!in) { std::cerr << "truncated input\n"; return 2; }
        for (size_t k=0; k<order; ++k) {
            const uint32_t x=data[k];
            switch(which) {
            case 0: series.ref(0,0,k)=x; break;
            case 1: series.ref(1,0,k)=x; break;
            case 2: series.ref(0,1,k)=x; break;
            case 3: series.ref(1,1,k)=x; break;
            case 4: series.ref(2,1,k)=x; break;
            case 5: series.ref(3,1,k)=x; break;
            }
        }
    }

    std::vector<size_t> shift(initial_shift.begin(), initial_shift.end());
    PMat basis(F,4,4,order+1);
    LinBox::OrderBasis<Field> ob(F);
    const size_t det_degree=ob.PM_Basis(basis,series,order,shift);

    std::cout << "p_E_M_R_Z_Q_B_order " << prime << " " << edeg << " "
              << mdeg << " " << rwidth << " " << zwidth << " "
              << outrows << " " << lowbound << " " << order << "\n";
    std::cout << "threshold " << threshold << "\n";
    std::cout << "det_degree " << det_degree << "\n";
    std::cout << "initial_shift";
    for (auto x:initial_shift) std::cout << " " << x;
    std::cout << "\nfinal_shift";
    for (auto x:shift) std::cout << " " << x;
    std::cout << "\n";

    // The first column is x^column_shift times a primitive column and the
    // second is primitive independently (the C,S minor is a unit after
    // removing that power).  The determinant degree is therefore
    // (order-column_shift)+order.
    std::array<std::array<int64_t,4>,4> lead{};
    for(size_t i=0;i<4;i++) for(size_t j=0;j<4;j++) {
        if(shift[i] >= initial_shift[j]) {
            const size_t k=shift[i]-initial_shift[j];
            if(k < basis.size()) lead[i][j]=basis.get(i,j,k);
        }
    }
    int64_t lead_det=1;
    for(size_t col=0;col<4;col++) {
        size_t pivot=col;
        while(pivot<4 && lead[pivot][col]==0) ++pivot;
        if(pivot==4) { lead_det=0; break; }
        if(pivot!=col) {
            std::swap(lead[pivot],lead[col]);
            lead_det=lead_det ? prime-lead_det : 0;
        }
        const int64_t pv=lead[col][col];
        lead_det=static_cast<int64_t>((__int128)lead_det*pv%prime);
        int64_t inv=1, base=pv, exp=prime-2;
        while(exp) {
            if(exp&1) inv=static_cast<int64_t>((__int128)inv*base%prime);
            base=static_cast<int64_t>((__int128)base*base%prime);
            exp>>=1;
        }
        for(size_t row=col+1;row<4;row++) if(lead[row][col]) {
            const int64_t factor=static_cast<int64_t>(
                (__int128)lead[row][col]*inv%prime);
            for(size_t k=col;k<4;k++) {
                lead[row][k]=(lead[row][k]-static_cast<int64_t>(
                    (__int128)factor*lead[col][k]%prime))%prime;
                if(lead[row][k]<0) lead[row][k]+=prime;
            }
        }
    }
    size_t initial_sum=0, final_sum=0;
    for(size_t i=0;i<4;i++) {
        initial_sum += initial_shift[i];
        final_sum += shift[i];
    }
    const size_t shift_gain=final_sum-initial_sum;
    std::cout << "shift_gain_expected " << shift_gain << " "
              << 2*static_cast<size_t>(order)-column_shift << "\n";
    std::cout << "shift_leading_determinant " << lead_det << "\n";
    if(shift_gain != 2*static_cast<size_t>(order)-column_shift || lead_det==0) {
        std::cerr << "invalid shifted-basis certificate\n"; return 3;
    }

    const std::string basis_path=
        "/tmp/full187_f3_pure_face_k17_k18_vector_dual_basis_6900.bin";
    std::ofstream bout(basis_path,std::ios::binary);
    const std::array<char,8> bmagic={'F','3','K','4','X','2','B','\0'};
    bout.write(bmagic.data(),bmagic.size());
    const std::array<uint32_t,3> bh={prime,order,
                                     static_cast<uint32_t>(basis.size())};
    bout.write(reinterpret_cast<const char*>(bh.data()),sizeof(bh));
    for(auto x:initial_shift) { uint32_t y=x;
        bout.write(reinterpret_cast<const char*>(&y),sizeof(y)); }
    for(auto x:shift) { uint32_t y=static_cast<uint32_t>(x);
        bout.write(reinterpret_cast<const char*>(&y),sizeof(y)); }
    for(size_t i=0;i<4;i++) for(size_t j=0;j<4;j++)
        for(size_t k=0;k<basis.size();k++) {
            uint32_t x=static_cast<uint32_t>(basis.get(i,j,k));
            bout.write(reinterpret_cast<const char*>(&x),sizeof(x));
        }
    bout.close();
    std::cout << "basis_size " << basis.size() << "\n";
    std::cout << "basis_certificate " << basis_path << "\n";

    bool found=false;
    for(size_t i=0;i<4;i++) {
        std::array<long,4> degrees={-1,-1,-1,-1};
        for(size_t j=0;j<4;j++) for(size_t k=0;k<basis.size();k++)
            if(basis.get(i,j,k)) degrees[j]=static_cast<long>(k);
        std::cout << "row " << i << " shifted_degree " << shift[i]
                  << " component_degrees";
        for(auto x:degrees) std::cout << " " << x;
        if(shift[i] <= threshold) { found=true; std::cout << " CANDIDATE"; }
        std::cout << "\n";
    }
    rusage usage{};
    getrusage(RUSAGE_SELF,&usage);
    std::cout << "peak_rss_kib " << usage.ru_maxrss << "\n";
    if(found) {
        std::cout << "decision RED_NONZERO_COUPLED_VECTOR_DUAL\n";
    } else {
        std::cout << "decision GREEN_COUPLED_VECTOR_DUAL_INJECTIVE\n";
    }
    return 0;
}
