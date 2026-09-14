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

int main(int argc, char** argv) {
    const std::string input = argc > 1 ? argv[1] :
        "/tmp/full187_second_fringe_order_basis_data_6900.bin";
    std::ifstream in(input, std::ios::binary);
    if (!in) { std::cerr << "cannot open " << input << "\n"; return 2; }
    std::array<char,8> magic{};
    std::array<uint32_t,8> h{};
    in.read(magic.data(), magic.size());
    in.read(reinterpret_cast<char*>(h.data()), sizeof(h));
    if (std::string(magic.data(), 7) != "F187SF2" || h[7] != 4) {
        std::cerr << "bad header\n"; return 2;
    }
    const uint32_t prime=h[0], n=h[1], order=h[2], a=h[3], b=h[4], c=h[5];
    const uint32_t threshold=h[6];
    std::array<std::vector<uint32_t>,4> data;
    for (auto& x : data) {
        x.resize(order);
        in.read(reinterpret_cast<char*>(x.data()), x.size()*sizeof(uint32_t));
    }
    if (!in) { std::cerr << "truncated input\n"; return 2; }

    // int64 storage is required here.  Givaro's uint32 specialization has
    // a smaller safe-cardinality contract and silently misbehaves at this
    // 31-bit modulus; int64 products remain below 2^63.
    using Field = Givaro::Modular<int64_t>;
    using PMat = LinBox::PolynomialMatrix<Field, LinBox::PMType::polfirst>;
    Field F(prime);
    PMat series(F,4,2,order);
    for (size_t k=0;k<order;k++) {
        series.ref(0,0,k)=data[0][k]; // U^*
        series.ref(0,1,k)=data[1][k]; // (U^*)^-1
        series.ref(3,0,k)=data[2][k] ? prime-data[2][k] : 0; // -B target
        series.ref(3,1,k)=data[3][k] ? prime-data[3][k] : 0; // -A target
    }
    series.ref(1,0,0)=1;
    series.ref(2,1,0)=1;

    // Bounds at shifted degree threshold b-1:
    // deg L<=b-2, deg Q1<=b-3, deg Q2<=b-1, deg z<=0.
    const std::array<size_t,4> initial_shift={1,2,0,threshold};
    std::vector<size_t> shift(initial_shift.begin(), initial_shift.end());
    PMat basis(F,4,4,order+1);
    LinBox::OrderBasis<Field> ob(F);
    const size_t det_degree=ob.PM_Basis(basis,series,order,shift);

    std::cout << "p_N_order_A_B_C " << prime << " " << n << " " << order
              << " " << a << " " << b << " " << c << "\n";
    std::cout << "threshold " << threshold << "\n";
    std::cout << "det_degree " << det_degree << "\n";
    std::cout << "final_shift";
    for (auto x:shift) std::cout << " " << x;
    std::cout << "\n";

    // A nonzero s-leading determinant plus sum(delta)-sum(s)=2*order is a
    // compact independent basis certificate: the two identity rows in the
    // series make the approximant-module determinant ideal x^(2*order).
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
        while(pivot<4 && lead[pivot][col]==0) pivot++;
        if(pivot==4) { lead_det=0; break; }
        if(pivot!=col) { std::swap(lead[pivot],lead[col]); lead_det=lead_det?prime-lead_det:0; }
        const int64_t pv=lead[col][col];
        lead_det=static_cast<int64_t>((__int128)lead_det*pv%prime);
        int64_t inv=1, base=pv, exp=prime-2;
        while(exp) { if(exp&1) inv=static_cast<int64_t>((__int128)inv*base%prime);
                     base=static_cast<int64_t>((__int128)base*base%prime); exp>>=1; }
        for(size_t row=col+1;row<4;row++) if(lead[row][col]) {
            const int64_t factor=static_cast<int64_t>((__int128)lead[row][col]*inv%prime);
            for(size_t k=col;k<4;k++) {
                lead[row][k]=(lead[row][k]-static_cast<int64_t>((__int128)factor*lead[col][k]%prime))%prime;
                if(lead[row][k]<0) lead[row][k]+=prime;
            }
        }
    }
    size_t shift_gain=0;
    for(size_t i=0;i<4;i++) shift_gain += shift[i]-initial_shift[i];
    std::cout << "shift_gain_expected " << shift_gain << " " << 2*order << "\n";
    std::cout << "shift_leading_determinant " << lead_det << "\n";
    if(shift_gain != 2*order || lead_det==0) {
        std::cerr << "invalid shifted-basis certificate\n"; return 3;
    }

    const std::string basis_path=
        "/tmp/full187_second_fringe_order_basis_certificate_6900.bin";
    std::ofstream basis_out(basis_path,std::ios::binary);
    const std::array<char,8> basis_magic={'F','1','8','7','S','F','B','\0'};
    basis_out.write(basis_magic.data(),basis_magic.size());
    const std::array<uint32_t,3> basis_header={prime,order,
                                               static_cast<uint32_t>(basis.size())};
    basis_out.write(reinterpret_cast<const char*>(basis_header.data()),sizeof(basis_header));
    for(auto x:initial_shift) { uint32_t y=static_cast<uint32_t>(x);
        basis_out.write(reinterpret_cast<const char*>(&y),sizeof(y)); }
    for(auto x:shift) { uint32_t y=static_cast<uint32_t>(x);
        basis_out.write(reinterpret_cast<const char*>(&y),sizeof(y)); }
    for(size_t i=0;i<4;i++) for(size_t j=0;j<4;j++)
        for(size_t k=0;k<basis.size();k++) {
            uint32_t x=static_cast<uint32_t>(basis.get(i,j,k));
            basis_out.write(reinterpret_cast<const char*>(&x),sizeof(x));
        }
    basis_out.close();
    std::cout << "basis_certificate " << basis_path << "\n";

    bool found=false;
    size_t chosen=0;
    uint32_t zconstant=0;
    for (size_t i=0;i<4;i++) {
        std::array<long,4> degrees={-1,-1,-1,-1};
        for (size_t j=0;j<4;j++)
            for (size_t k=0;k<basis.size();k++)
                if (basis.get(i,j,k)) degrees[j]=static_cast<long>(k);
        std::cout << "row " << i << " shifted_degree " << shift[i]
                  << " component_degrees";
        for(auto x:degrees) std::cout << " " << x;
        std::cout << " z_terms";
        size_t zterms=0;
        for(size_t k=0;k<basis.size();k++) if(basis.get(i,3,k)) {
            zterms++;
            if(k==0) zconstant=basis.get(i,3,k);
        }
        std::cout << " " << zterms;
        if (zterms && shift[i] <= threshold) {
            found=true; chosen=i;
            std::cout << " CANDIDATE";
        }
        std::cout << "\n";
    }
    rusage usage{};
    getrusage(RUSAGE_SELF,&usage);
    std::cout << "peak_rss_kib " << usage.ru_maxrss << "\n";
    if(found) {
        std::ofstream out("/tmp/full187_second_fringe_order_basis_solution_6900.bin",
                          std::ios::binary);
        uint32_t row=chosen;
        out.write(reinterpret_cast<const char*>(&row),sizeof(row));
        out.write(reinterpret_cast<const char*>(&zconstant),sizeof(zconstant));
        for(size_t k=0;k<b;k++) {
            uint32_t x=static_cast<uint32_t>(basis.get(chosen,0,k));
            out.write(reinterpret_cast<const char*>(&x),sizeof(x));
        }
        std::cout << "decision GREEN_C1_SECOND_FRINGE_MEMBERSHIP\n";
        return 0;
    }
    std::cout << "decision STOP_C1_NOT_IN_THREE_POLYNOMIAL_SECOND_FRINGE_IMAGE\n";
    return 0;
}
