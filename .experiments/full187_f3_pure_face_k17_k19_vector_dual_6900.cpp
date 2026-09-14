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

int main(int argc,char** argv) {
    const std::string input=argc>1?argv[1]:
        "/tmp/full187_f3_pure_face_k17_k19_vector_dual_6900.bin";
    std::ifstream in(input,std::ios::binary);
    if(!in){std::cerr<<"cannot open input\n";return 2;}
    std::array<char,8> magic{}; std::array<uint32_t,12> h{};
    in.read(magic.data(),8); in.read(reinterpret_cast<char*>(h.data()),sizeof(h));
    if(std::string(magic.data(),8)!="F3K1719D"||h[9]!=7||h[10]!=5){
        std::cerr<<"bad header\n";return 2;}
    const uint32_t p=h[0],edeg=h[1],mdeg=h[2],rwidth=h[3],zwidth=h[4];
    const uint32_t outrows=h[5],lowbound=h[6],order=h[7],threshold=h[8];
    const uint32_t column_shift=h[11];
    std::array<uint32_t,5> bounds{},initial{};
    in.read(reinterpret_cast<char*>(bounds.data()),sizeof(bounds));
    in.read(reinterpret_cast<char*>(initial.data()),sizeof(initial));
    if(!in||mdeg!=19*edeg||lowbound+outrows!=mdeg||order!=edeg+outrows||
       column_shift!=57193){std::cerr<<"inconsistent dimensions\n";return 2;}

    using Field=Givaro::Modular<int64_t>;
    using PMat=LinBox::PolynomialMatrix<Field,LinBox::PMType::polfirst>;
    Field F(p); PMat series(F,5,2,order);
    std::vector<uint32_t> data(order);
    for(size_t which=0;which<7;which++){
        in.read(reinterpret_cast<char*>(data.data()),data.size()*sizeof(uint32_t));
        if(!in){std::cerr<<"truncated input\n";return 2;}
        for(size_t k=0;k<order;k++){
            const uint32_t x=data[k];
            switch(which){
            case 0:series.ref(0,0,k)=x;break;
            case 1:series.ref(1,0,k)=x;break;
            case 2:series.ref(0,1,k)=x;break;
            case 3:series.ref(1,1,k)=x;break;
            case 4:series.ref(2,1,k)=x;break;
            case 5:series.ref(3,1,k)=x;break;
            case 6:series.ref(4,1,k)=x;break;
            }
        }
    }
    std::vector<size_t> shift(initial.begin(),initial.end());
    PMat basis(F,5,5,order+1); LinBox::OrderBasis<Field> ob(F);
    const size_t det_degree=ob.PM_Basis(basis,series,order,shift);
    std::cout<<"p_E_M_R_Z_Q_B_order "<<p<<" "<<edeg<<" "<<mdeg<<" "
             <<rwidth<<" "<<zwidth<<" "<<outrows<<" "<<lowbound<<" "
             <<order<<"\nthreshold "<<threshold<<"\ndet_degree "<<det_degree;
    std::cout<<"\ninitial_shift";for(auto x:initial)std::cout<<" "<<x;
    std::cout<<"\nfinal_shift";for(auto x:shift)std::cout<<" "<<x;
    std::cout<<"\n";

    std::array<std::array<int64_t,5>,5> lead{};
    for(size_t i=0;i<5;i++)for(size_t j=0;j<5;j++)if(shift[i]>=initial[j]){
        const size_t k=shift[i]-initial[j];
        if(k<basis.size())lead[i][j]=basis.get(i,j,k);
    }
    int64_t determinant=1;
    for(size_t col=0;col<5;col++){
        size_t pivot=col;while(pivot<5&&!lead[pivot][col])pivot++;
        if(pivot==5){determinant=0;break;}
        if(pivot!=col){std::swap(lead[pivot],lead[col]);determinant=determinant?p-determinant:0;}
        const int64_t pv=lead[col][col];determinant=(__int128)determinant*pv%p;
        int64_t inv=1,base=pv,exp=p-2;
        while(exp){if(exp&1)inv=(__int128)inv*base%p;base=(__int128)base*base%p;exp>>=1;}
        for(size_t row=col+1;row<5;row++)if(lead[row][col]){
            const int64_t factor=(__int128)lead[row][col]*inv%p;
            for(size_t k=col;k<5;k++){
                lead[row][k]=(lead[row][k]-(int64_t)((__int128)factor*lead[col][k]%p))%p;
                if(lead[row][k]<0)lead[row][k]+=p;
            }
        }
    }
    size_t isum=0,fsum=0;for(size_t i=0;i<5;i++){isum+=initial[i];fsum+=shift[i];}
    const size_t gain=fsum-isum,expected=2*(size_t)order-column_shift;
    std::cout<<"shift_gain_expected "<<gain<<" "<<expected
             <<"\nshift_leading_determinant "<<determinant<<"\n";
    if(gain!=expected||!determinant){std::cerr<<"invalid basis certificate\n";return 3;}

    const std::string bpath=
        "/tmp/full187_f3_pure_face_k17_k19_vector_dual_basis_6900.bin";
    std::ofstream bout(bpath,std::ios::binary);
    const std::array<char,8> bmagic={'F','3','K','1','7','1','9','B'};
    bout.write(bmagic.data(),8);
    const std::array<uint32_t,3> bh={p,order,(uint32_t)basis.size()};
    bout.write(reinterpret_cast<const char*>(bh.data()),sizeof(bh));
    for(auto x:initial){uint32_t y=x;bout.write(reinterpret_cast<char*>(&y),4);}
    for(auto x:shift){uint32_t y=x;bout.write(reinterpret_cast<char*>(&y),4);}
    for(size_t i=0;i<5;i++)for(size_t j=0;j<5;j++)for(size_t k=0;k<basis.size();k++){
        uint32_t x=basis.get(i,j,k);bout.write(reinterpret_cast<char*>(&x),4);
    }
    bout.close();std::cout<<"basis_size "<<basis.size()<<"\nbasis_certificate "<<bpath<<"\n";
    bool found=false;
    for(size_t i=0;i<5;i++){
        std::array<long,5> degrees={-1,-1,-1,-1,-1};
        for(size_t j=0;j<5;j++)for(size_t k=0;k<basis.size();k++)if(basis.get(i,j,k))degrees[j]=k;
        std::cout<<"row "<<i<<" shifted_degree "<<shift[i]<<" component_degrees";
        for(auto x:degrees)std::cout<<" "<<x;
        if(shift[i]<=threshold){found=true;std::cout<<" CANDIDATE";}
        std::cout<<"\n";
    }
    rusage usage{};getrusage(RUSAGE_SELF,&usage);
    std::cout<<"peak_rss_kib "<<usage.ru_maxrss<<"\ndecision "
             <<(found?"RED_NONZERO_K17_K19_VECTOR_DUAL":"GREEN_K17_K19_VECTOR_DUAL_INJECTIVE")
             <<"\n";
    return 0;
}
