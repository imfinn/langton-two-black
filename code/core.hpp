#include "standard_headers.hpp"
using namespace std; typedef long long ll;
static int DUMPMOD=9;
static const int DX[4]={0,1,0,-1}, DY[4]={1,0,-1,0};
static const int GW=8192, OFF=4096;

struct Board {
  vector<uint8_t> c; vector<int> touched; vector<int> ttime; // first-touch order and time
  Board():c((size_t)GW*GW,0){}
  static int idx(int x,int y){return (y+OFF)*GW+(x+OFF);}
  static bool inb(int x,int y){return x>-OFF+4&&x<OFF-4&&y>-OFF+4&&y<OFF-4;}
  void clear(){for(int i:touched)c[i]=0;touched.clear();ttime.clear();}
  inline void touch(int i,int t){if(!(c[i]&2)){c[i]|=2;touched.push_back(i);ttime.push_back(t);}}
};
static inline int cx(int i){return i%GW-OFF;} static inline int cy(int i){return i/GW-OFF;}

struct Cert { bool ok=false; ll T=-1,s=-1; int ux=0,uy=0; ll A=0; string word; ll steps=0; bool oob=false; int fx=0,fy=0; };

struct Runner {
  Board B; vector<int> X,Y; vector<uint8_t> H,R;
  // prefix maxima over first-touched cells of the 4 diagonal functionals, indexed by touch count
  vector<ll> pm[4];
  static ll dfun(int d,ll x,ll y){static const int SX[4]={1,1,-1,-1},SY[4]={1,-1,1,-1};return SX[d]*x+SY[d]*y;}
  Runner(){X.reserve(1<<21);Y.reserve(1<<21);H.reserve(1<<21);R.reserve(1<<21);}
  // run from time 0; optional callback-free; returns first certificate (period 104 only)
  Cert certify(const vector<pair<int,int>>&cells,int h0,ll cap,ll earliest_s=0){
    B.clear(); X.clear();Y.clear();H.clear();R.clear(); for(int d=0;d<4;++d)pm[d].clear();
    auto addpm=[&](int i){int x=cx(i),y=cy(i); for(int d=0;d<4;++d){ll v=dfun(d,x,y); pm[d].push_back(pm[d].empty()?v:max(pm[d].back(),v));}};
    for(auto&p:cells){int i=Board::idx(p.first,p.second);B.touch(i,0);B.c[i]|=1;addpm(i);}
    int x=0,y=0,h=h0; Cert C;
    for(ll t=0;t<cap;++t){
      if(!Board::inb(x,y)){C.oob=true;C.steps=t;return C;}
      int i=Board::idx(x,y); size_t before=B.touched.size(); B.touch(i,(int)t); if(B.touched.size()>before)addpm(i);
      int b=B.c[i]&1; B.c[i]^=1; X.push_back(x);Y.push_back(y);H.push_back(h);R.push_back(b);
      h=(h+(b?3:1))&3; x+=DX[h]; y+=DY[h];
      ll T=t+1;
      if(T%104==0&&T>=520&&T-104>=earliest_s){
        // positions p_T, p_{T-104},... ; X[T] not stored yet -> use (x,y) for T
        auto PX=[&](ll w)->int{return w==T?x:X[w];}; auto PY=[&](ll w)->int{return w==T?y:Y[w];};
        int ux=PX(T)-PX(T-104), uy=PY(T)-PY(T-104); if(ux==0&&uy==0)continue;
        bool per=true;
        for(ll w=T-416;w<T-104&&per;++w) if(PX(w+104)-PX(w)!=ux||PY(w+104)-PY(w)!=uy||R[w+104]!=R[w]) per=false;
        if(!per)continue;
        ll s=T-104; int hT=h; if(H[s]!=hT)continue;
        // phi = u.z ; A = min phi over [s,T] - 1
        ll A=LLONG_MAX; for(ll w=s;w<=T;++w)A=min(A,(ll)ux*PX(w)+(ll)uy*PY(w)); A-=1;
        ll pu=(ll)ux*ux+(ll)uy*uy;
        // old cells (first touched before s0=T-416) must avoid {phi>A}: use diagonal prefix max if u diagonal
        ll s0=T-416; size_t nold=upper_bound(B.ttime.begin(),B.ttime.end(),(int)s0-1)-B.ttime.begin();
        // cells with ttime <= s0-1 are "old"; ttime is nondecreasing
        bool diag=abs(ux)==abs(uy);
        if(diag){int sx=ux>0?1:-1, sy=uy>0?1:-1; int d=(sx==1?(sy==1?0:1):(sy==1?2:3)); ll k=abs(ux);
          if(nold>0 && pm[d][nold-1]*k > A) continue; }   // some old cell lies in {phi>A}: not yet clean
        else { bool bad=false; for(size_t j=0;j<nold&&!bad;++j){int ii=B.touched[j]; if((ll)ux*cx(ii)+(ll)uy*cy(ii)>A)bad=true;} if(bad)continue; }
        // exact comparison over recent cells (touched at or after s0); old cells are outside {phi>A}
        unordered_map<int,int> rd; for(ll w=s;w<T;++w) rd[Board::idx(X[w],Y[w])]^=1;
        vector<pair<int,int>> S1,S2;
        for(size_t j=nold;j<B.touched.size();++j){int ii=B.touched[j]; int zx=cx(ii),zy=cy(ii); ll ph=(ll)ux*zx+(ll)uy*zy;
          int colT=B.c[ii]&1; auto it=rd.find(ii); int colS=colT^(it==rd.end()?0:it->second);
          if(colT&&ph>A+pu)S1.push_back({zx,zy}); if(colS&&ph>A)S2.push_back({zx+ux,zy+uy});}
        sort(S1.begin(),S1.end());sort(S2.begin(),S2.end());
        if(S1!=S2)continue;
        C.ok=true;C.T=T;C.s=s;C.ux=ux;C.uy=uy;C.A=A;C.steps=T;C.fx=x;C.fy=y;
        for(ll w=s;w<T;++w)C.word+=char('0'+R[w]);
        return C;
      }
    }
    C.steps=cap; return C;
  }
};

// ---------- snapshot simulation (independent board instance) ----------
static vector<vector<pair<int,int>>> snapshots(const vector<pair<int,int>>&cells,int h0,const vector<ll>&times){
  static Board B2; B2.clear(); vector<vector<pair<int,int>>> out(times.size());
  for(auto&p:cells){int i=Board::idx(p.first,p.second);B2.touch(i,0);B2.c[i]|=1;}
  ll tmax=*max_element(times.begin(),times.end()); int x=0,y=0,h=h0;
  for(ll t=0;t<=tmax;++t){
    for(size_t j=0;j<times.size();++j) if(times[j]==t){ for(int ii:B2.touched) if(B2.c[ii]&1) out[j].push_back({cx(ii),cy(ii)}); }
    if(t==tmax)break;
    int i=Board::idx(x,y); B2.touch(i,(int)t); int b=B2.c[i]&1; B2.c[i]^=1; h=(h+(b?3:1))&3; x+=DX[h]; y+=DY[h];
  }
  return out;
}
static string canon(const string&w){string b=w;for(size_t i=1;i<w.size();++i){string r=w.substr(i)+w.substr(0,i);if(r<b)b=r;}return b;}

