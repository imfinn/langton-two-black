// Highway calculus for Langton's ant: verification of parametrized families of
// finite starting configurations, and recursive enumeration "add one more cell anywhere".
//
// A FAMILY has parameters i=0..d-1, each a corridor with diagonal drift v_i (|v_i|=(2,2)),
// and blocks (black cells) b with base offset b0 and a mask of corridors they lie beyond:
//      cell_b(n) = b0 + sum_{i in mask_b} n_i v_i .
// The ant starts at the origin heading north.
//
// verify(F, n) checks, on the single run of configuration F(n), conditions under which
// every member n' >= n is eventually the standard 104-highway (see the note):
//   - certificate: exact Lemma-1 certificate with the standard 104-turn word;
//   - per corridor i (phi_i = sgn(vx)x + sgn(vy)y): every crossing of the midline happens
//     inside an exactly periodic run with displacement +-v_i ("transit"); transits alternate,
//     the first going outward; site activity separates (Dtop+40 < Cbot); at a switch time in
//     every transit the board satisfies B(m+104)(w) = B(m)(w - sigma v_i) on the whole band
//     Dtop+8 < phi < Cbot-8; relation regions hold between switches; the certified highway
//     stays in the final relation region and its half-plane transfers;
//   - corridors with parallel drifts have disjoint bands.
// The induction (note, Prop. 5) turns this into a proof for all members n' >= n.
#include "core.hpp"

static string CW;               // canonical standard highway word
static Runner RU;
static const ll CAP=40000000;
static int K=40;                // base corridor length for new tail corridors
static int LS=10;               // split threshold (periods) for corridor footprints

struct Fam { vector<array<int,2>> v; vector<array<int,3>> blk; string tag; };
static vector<pair<int,int>> cfg(const Fam&f,const vector<int>&n){
  vector<pair<int,int>> c; for(auto&b:f.blk){int x=b[0],y=b[1]; for(size_t i=0;i<f.v.size();++i)if(b[2]>>i&1){x+=n[i]*f.v[i][0];y+=n[i]*f.v[i][1];} c.push_back({x,y});}
  sort(c.begin(),c.end()); c.erase(unique(c.begin(),c.end()),c.end()); return c; }
static inline ll PHI(int vx,int vy,ll x,ll y){return (vx>0?1:-1)*x+(vy>0?1:-1)*y;}

struct PInfo { ll Dtop=0,Cbot=0,mu=0; vector<array<ll,4>> tr; /* b,e,sigma,m */ int final_side=-1; };
struct Info { bool ok=false; string why; int failp=-1; Cert c; vector<PInfo> P; ll T=0;
  vector<int> X,Y; vector<uint8_t> H; };

static Info verify(const Fam&F,const vector<int>&n){
  Info I; auto cells=cfg(F,n);
  I.c=RU.certify(cells,0,CAP);
  if(!I.c.ok){I.why=I.c.oob?"oob":"nocert";return I;}
  if(canon(I.c.word)!=CW){I.why="nonstandard";return I;}
  ll T=I.c.T; I.T=T; I.X.assign(RU.X.begin(),RU.X.begin()+T); I.Y.assign(RU.Y.begin(),RU.Y.begin()+T); I.H.assign(RU.H.begin(),RU.H.begin()+T);
  int d=F.v.size(); I.P.resize(d);
  auto PX=[&](ll w)->int{return w<T?I.X[w]:I.c.fx;}; auto PY=[&](ll w)->int{return w<T?I.Y[w]:I.c.fy;};
  int ux=I.c.ux,uy=I.c.uy;
  vector<ll> snaptimes;
  for(int i=0;i<d;++i){
    int vx=F.v[i][0],vy=F.v[i][1]; auto phi=[&](ll x,ll y){return PHI(vx,vy,x,y);};
    PInfo&P=I.P[i];
    ll D0=phi(0,0),C0=LLONG_MAX;
    for(auto&b:F.blk){ll x=b[0],y=b[1]; for(int j=0;j<d;++j)if(b[2]>>j&1){x+=(ll)n[j]*F.v[j][0];y+=(ll)n[j]*F.v[j][1];}
      if(b[2]>>i&1)C0=min(C0,phi(x,y)); else D0=max(D0,phi(x,y));}
    if(C0==LLONG_MAX||C0-D0<60){I.why="short";I.failp=i;return I;}
    P.mu=(D0+C0)/2;
    // periodic runs with displacement +-v_i
    vector<int8_t> f(T,0);
    for(ll w=0;w+104<T;++w){ if(I.H[w+104]!=I.H[w])continue; int dx=I.X[w+104]-I.X[w],dy=I.Y[w+104]-I.Y[w];
      if(dx==vx&&dy==vy)f[w]=1; else if(dx==-vx&&dy==-vy)f[w]=-1; }
    vector<array<ll,3>> runs; for(ll w=0;w+104<T;){ if(!f[w]){++w;continue;} ll b=w; int sg=f[w]; while(w+104<T&&f[w]==sg)++w; if(w-b>=520)runs.push_back({b,w-1,sg}); }
    // the certified highway itself is periodic from s to T: treat [s, T-104) as a run if along +-v_i
    // (already included by the scan, since positions up to T-1 are stored and Lemma 1 guarantees periodicity)
    // crossings of the midline
    vector<ll> cross; for(ll w=0;w<T;++w){ bool a=phi(PX(w),PY(w))<P.mu, b=phi(PX(w+1),PY(w+1))<P.mu; if(a!=b)cross.push_back(w);}
    vector<int> cnt(runs.size(),0);
    for(ll w:cross){ int which=-1; for(size_t r=0;r<runs.size();++r) if(w>=runs[r][0]&&w<runs[r][1]+104){which=r;break;}
      if(which<0){ // a crossing in the final certified stretch (beyond the scanned runs) is allowed if it is in [s,T]
        if(w>=I.c.s){ int sg=((ll)ux==vx&&(ll)uy==vy)?1:(((ll)ux==-vx&&(ll)uy==-vy)?-1:0); if(sg){ runs.push_back({I.c.s,T-1,sg}); cnt.push_back(0); which=runs.size()-1; } }
        if(which<0){I.why="cross_outside_transit";I.failp=i;return I;} }
      cnt[which]++; }
    int side=-1; vector<array<ll,3>> trs;
    for(size_t r=0;r<runs.size();++r){ if(!cnt[r])continue; if(cnt[r]%2==0){I.why="even_crossings";I.failp=i;return I;}
      trs.push_back(runs[r]); }
    sort(trs.begin(),trs.end());
    for(auto&t:trs){ if(t[2]!=-side){I.why="transit_direction";I.failp=i;return I;} side=-side; }
    P.final_side=side;
    // switch times: closest approach to mu inside the run, with room for +104.
    // Transit span = the part of the periodic run, around the switch, with D0-16 <= phi <= C0+16
    // (a single highway may traverse several parallel corridors in series; each corridor owns only its stretch).
    for(auto&t:trs){ ll best=-1,bd=LLONG_MAX; for(ll w=max(t[0],(ll)0);w<=t[1]&&w+104<T;++w){ll dd=llabs(phi(PX(w),PY(w))-P.mu); if(dd<bd){bd=dd;best=w;}}
      if(best<0){I.why="no_switch";I.failp=i;return I;}
      auto inr=[&](ll w){ll p=phi(PX(w),PY(w)); return p>=D0-16&&p<=C0+16;};
      ll b2=best; while(b2-1>=t[0]&&inr(b2-1))--b2;
      ll end=t[1]+104; ll e2=best; while(e2+1<=end&&inr(e2+1))++e2;
      if(e2<best+104){I.why="short_transit";I.failp=i;return I;}
      P.tr.push_back({b2,e2-104,t[2],best}); }
    // site zones from non-transit reads
    auto intransit=[&](ll w){for(auto&t:P.tr) if(w>=t[0]&&w<=t[1]+104) return true; return false;};
    ll Dtop=D0,Cbot=C0; { int sd=-1; size_t k=0;
      for(ll w=0;w<T;++w){ while(k<P.tr.size()&&w>P.tr[k][1]+104){sd=-sd;++k;} if(intransit(w))continue;
        ll p=phi(PX(w),PY(w)); if(sd<0)Dtop=max(Dtop,p); else Cbot=min(Cbot,p);} }
    P.Dtop=Dtop;P.Cbot=Cbot;
    if(!(Dtop+40<Cbot)){I.why="zones_overlap";I.failp=i;return I;}
    for(auto&t:P.tr){ll pm=phi(PX(t[3]),PY(t[3])); if(!(pm>Dtop+16&&pm<Cbot-16)){I.why="switch_outside_band";I.failp=i;return I;}
      if(PX(t[3]+104)!=PX(t[3])+t[2]*vx||PY(t[3]+104)!=PY(t[3])+t[2]*vy||I.H[t[3]+104]!=I.H[t[3]]){I.why="switch_pose";I.failp=i;return I;}
      snaptimes.push_back(t[3]); snaptimes.push_back(t[3]+104);}
    // relation regions: relation r_0 = identity (near) from t=0; switch j flips it. Relation r_j must hold on
    // [m_j, m_{j+1}+104) (m_0 = 0, last interval runs to T).
    { vector<ll> M={0}; for(auto&t:P.tr)M.push_back(t[3]);
      for(size_t j=0;j<M.size();++j){ int r=(j%2==0)?-1:1; ll from=M[j], to=(j+1<M.size())?M[j+1]+104:T;
        for(ll w=from;w<to&&w<T;++w){ ll p=phi(PX(w),PY(w)); if(r<0? !(p<Cbot-16) : !(p>Dtop+16)){I.why="relation_region";I.failp=i;return I;} } } }
    // certified highway: drift and range in the final relation region
    { ll du=phi(ux,uy); ll mx=LLONG_MIN,mn=LLONG_MAX; for(ll w=I.c.s;w<T;++w){ll p=phi(PX(w),PY(w));mx=max(mx,p);mn=min(mn,p);}
      if(side<0&&(du>0||mx>=Cbot-16)){I.why="final_highway_region";I.failp=i;return I;}
      if(side>0&&(du<0||mn<=Dtop+16)){I.why="final_highway_region";I.failp=i;return I;}
      bool perp=(du==0), par=(ux==vx&&uy==vy), anti=(ux==-vx&&uy==-vy);
      if(side<0&&!(perp||(anti&&-I.c.A<=(ll)abs(ux)*(Cbot-16)))){I.why="cert_transfer";I.failp=i;return I;}
      if(side>0&&!(perp||(par&&I.c.A>=(ll)abs(ux)*(Dtop+16)))){I.why="cert_transfer";I.failp=i;return I;} }
  }
  // ---- H1: transits of different corridors have disjoint read spans [b, e+104]
  // (H1') the insertion window [m, m+104] of every corridor-i switch is disjoint from every corridor-j transit span
  for(int i=0;i<d;++i)for(int j=0;j<d;++j){ if(i==j)continue; for(auto&a:I.P[i].tr)for(auto&b:I.P[j].tr){
    ll a0=a[3],a1=a[3]+104,b0=b[0],b1=b[1]+104; if(!(a1<b0||b1<a0)){I.why="H1_window_in_transit";I.failp=i;return I;} } }
  // ---- H3: parallel corridor pairs (ordered): side, foreign material, extremum attainment
  for(int i=0;i<d;++i)for(int j=0;j<d;++j){ if(i==j)continue;
    int vix=F.v[i][0],viy=F.v[i][1],vjx=F.v[j][0],vjy=F.v[j][1];
    int same=(vix==vjx&&viy==vjy), opp=(vix==-vjx&&viy==-vjy); if(!same&&!opp)continue;
    auto phii=[&](ll x,ll y){return PHI(vix,viy,x,y);}; auto phij=[&](ll x,ll y){return PHI(vjx,vjy,x,y);};
    PInfo&Pi=I.P[i]; PInfo&Pj=I.P[j]; int Delta=same?4:-4;
    ll blo=same?Pj.Dtop:-Pj.Cbot, bhi=same?Pj.Cbot:-Pj.Dtop;      // band_j in phi_i coordinates
    int sigma; if(blo>=Pi.Cbot)sigma=1; else if(bhi<=Pi.Dtop)sigma=-1; else {I.why="H3_side";I.failp=i;return I;}
    int rho=(sigma<0)?Delta:-Delta;
    // side of corridor i after each insertion window; reads inside a window are stretched (foreign)
    auto sideI=[&](ll t){int sd=-1; for(auto&tr:Pi.tr) if(t>tr[3]+104)sd=-sd; return sd;};
    auto inTrI=[&](ll t){for(auto&tr:Pi.tr) if(t>=tr[3]&&t<=tr[3]+104)return true; return false;};
    auto inTrJ=[&](ll t){for(auto&tr:Pj.tr) if(t>=tr[0]&&t<=tr[1]+104)return true; return false;};
    // j-transits lie in i-phases of side sigma
    for(auto&tr:Pj.tr) for(ll t=tr[0];t<=tr[1]+104&&t<T;++t) if(inTrI(t)||sideI(t)!=sigma){I.why="H3_jtransit_side";I.failp=i;return I;}
    // foreign items and zone/extremum conditions
    ll fmin=LLONG_MAX,fmax=LLONG_MIN; auto addF=[&](ll v){fmin=min(fmin,v);fmax=max(fmax,v);};
    ll nfFarMin=LLONG_MAX,nfNearMax=LLONG_MIN, nfFarBlk=LLONG_MAX,nfNearBlk=LLONG_MIN, fFarBlk=LLONG_MAX,fNearBlk=LLONG_MIN;
    { int sdj=-1; size_t kk=0;
      for(ll t=0;t<T;++t){ while(kk<Pj.tr.size()&&t>Pj.tr[kk][1]+104){sdj=-sdj;++kk;}
        ll pj=phij(PX(t),PY(t)); bool foreign=inTrI(t)||sideI(t)!=sigma;
        if(foreign){addF(pj);continue;}
        if(inTrJ(t))continue; if(sdj<0)nfNearMax=max(nfNearMax,pj); else nfFarMin=min(nfFarMin,pj);} }
    // the certified future repeats [s,T) shifted by multiples of u
    int finalSideI=Pi.final_side; ll duj=phij(ux,uy);
    if(finalSideI!=sigma){ if((rho>0&&duj<0)||(rho<0&&duj>0)){I.why="H3_foreign_future";I.failp=i;return I;} }
    // blocks (origin counts as a fixed near item)
    { ll o=phij(0,0); bool oForeign=(sigma>0); if(oForeign){addF(o); fNearBlk=max(fNearBlk,o);} else nfNearBlk=max(nfNearBlk,o); }
    for(auto&b:F.blk){ ll x=b[0],y=b[1]; for(int q=0;q<d;++q)if(b[2]>>q&1){x+=(ll)n[q]*F.v[q][0];y+=(ll)n[q]*F.v[q][1];}
      bool beyondI=b[2]>>i&1, beyondJ=b[2]>>j&1; bool foreign=(sigma>0)?!beyondI:beyondI; ll pj=phij(x,y);
      if(foreign){addF(pj); if(beyondJ)fFarBlk=min(fFarBlk,pj); else fNearBlk=max(fNearBlk,pj);}
      else { if(beyondJ){nfFarBlk=min(nfFarBlk,pj); nfFarMin=min(nfFarMin,pj);} else {nfNearBlk=max(nfNearBlk,pj); nfNearMax=max(nfNearMax,pj);} } }
    if(fmin!=LLONG_MAX){
      if(rho>0){ if(fmin<Pj.Cbot){I.why="H3_foreign_zone";I.failp=i;return I;}
        if(nfFarMin!=Pj.Cbot){I.why="H3_extremum";I.failp=i;return I;}
        if(fFarBlk<nfFarBlk){I.why="H3_mu_block";I.failp=i;return I;} }
      else { if(fmax>Pj.Dtop){I.why="H3_foreign_zone";I.failp=i;return I;}
        if(max(nfNearMax,nfNearBlk)!=Pj.Dtop){I.why="H3_extremum";I.failp=i;return I;}
        if(fNearBlk>nfNearBlk){I.why="H3_mu_block";I.failp=i;return I;} } }
  }
  // parallel corridors: disjoint bands
  for(int i=0;i<d;++i)for(int j=i+1;j<d;++j){
    int s=0; if(F.v[i]==F.v[j])s=1; else if(F.v[i][0]==-F.v[j][0]&&F.v[i][1]==-F.v[j][1])s=-1; if(!s)continue;
    ll a0=I.P[i].Dtop,a1=I.P[i].Cbot,b0=s>0?I.P[j].Dtop:-I.P[j].Cbot,b1=s>0?I.P[j].Cbot:-I.P[j].Dtop;
    if(!(a1<=b0||b1<=a0)){I.why="parallel_bands";I.failp=i;return I;} }
  // B-checks at all switch times
  if(!snaptimes.empty()){
    auto snaps=snapshots(cells,0,snaptimes); size_t q=0;
    for(int i=0;i<d;++i){ int vx=F.v[i][0],vy=F.v[i][1]; auto phi=[&](ll x,ll y){return PHI(vx,vy,x,y);}; PInfo&P=I.P[i];
      for(auto&t:P.tr){ set<pair<int,int>> A0(snaps[q].begin(),snaps[q].end()),A1(snaps[q+1].begin(),snaps[q+1].end()); q+=2; int sg=t[2];
        auto inS=[&](ll p){return p>P.Dtop+8&&p<P.Cbot-8;};
        for(auto&w:A1){ if(!inS(phi(w.first,w.second)))continue; if(!A0.count({w.first-sg*vx,w.second-sg*vy})){I.why="Bcheck";I.failp=i;return I;} }
        for(auto&w0:A0){ pair<int,int> w={w0.first+sg*vx,w0.second+sg*vy}; if(!inS(phi(w.first,w.second)))continue; if(!A1.count(w)){I.why="Bcheck";I.failp=i;return I;} } } } }
  I.ok=true; return I;
}
static int ntrans(const Info&I,int i){return I.P[i].tr.size();}

// --------- run a configuration recording first-read times (for enumeration) ----------
struct Rec { vector<int> X,Y; unordered_map<long long,ll> first; };
static long long KEY(int x,int y){return (long long)(((unsigned long long)(uint32_t)x<<32)|(uint32_t)y);}
static Rec record(const vector<pair<int,int>>&cells,ll Tmax){
  static Board B3; B3.clear(); Rec R; R.X.reserve(Tmax);R.Y.reserve(Tmax);
  for(auto&p:cells){int i=Board::idx(p.first,p.second);B3.touch(i,0);B3.c[i]|=1;}
  int x=0,y=0,h=0; for(ll t=0;t<Tmax;++t){ if(!Board::inb(x,y))break; R.X.push_back(x);R.Y.push_back(y); long long k=KEY(x,y); if(!R.first.count(k))R.first[k]=t;
    int i=Board::idx(x,y); B3.touch(i,(int)t); int b=B3.c[i]&1; B3.c[i]^=1; h=(h+(b?3:1))&3; x+=DX[h]; y+=DY[h]; }
  return R; }

// --------- statistics ----------
struct Stats { ll fam_ok=0, fam_fail=0, direct_ok=0, direct_fail=0, slabs=0, xval=0, xval_bad=0, updates=0; map<string,ll> why; map<int,ll> ntr; };
static Stats ST; static FILE* LOG=stdout; static vector<pair<Fam,vector<int>>>* COLLECT=nullptr; static int RSP=0; static bool XVAL=false; static FILE* DUMP=nullptr; static ll dumpctr=0;

static void dump(const vector<pair<int,int>>&cells){ if(DUMP&&(++dumpctr%DUMPMOD==0)){fprintf(DUMP,"%zu",cells.size());for(auto&q:cells)fprintf(DUMP," %d %d",q.first,q.second);fprintf(DUMP,"\n");} }

// verify a family for all members n >= n0 (adaptive base; slabs below an increased base handled recursively).
// On success returns true and the base actually used (nb) and its Info.
static bool prove(const Fam&F,const vector<int>&n0,vector<int>&nb,Info&I,int depth=0){
  int d=F.v.size();
  if(d==0){ auto cells=cfg(F,n0); Cert c=RU.certify(cells,0,CAP); ST.updates+=c.steps; dump(cells);
    bool ok=c.ok&&canon(c.word)==CW; if(ok)ST.direct_ok++; else {ST.direct_fail++; fprintf(LOG,"DIRECT FAIL %s cells:",F.tag.c_str()); for(auto&q:cells)fprintf(LOG," (%d,%d)",q.first,q.second); fprintf(LOG,"\n");}
    nb=n0; I=Info(); I.ok=ok; I.c=c; if(ok&&COLLECT)COLLECT->push_back({F,n0}); return ok; }
  vector<int> n=n0; string firstwhy;
  int MAXATT=getenv("MAXATT")?atoi(getenv("MAXATT")):60;
  for(int attempt=0;attempt<MAXATT;++attempt){
    I=verify(F,n); ST.updates+=I.c.steps; if(attempt==0)firstwhy=I.why+"/p"+to_string(I.failp);
    if(I.ok){
      dump(cfg(F,n));
      static ll xvc=0; static int XRATE=getenv("XRATE")?atoi(getenv("XRATE")):1;
      if(XVAL&&(xvc++%XRATE==0)){ for(int i=0;i<d;++i) for(int dd:{1,5}){ vector<int> m=n; m[i]+=dd; Cert c=RU.certify(cfg(F,m),0,CAP); ST.updates+=c.steps; ST.xval++;
          ll pred=I.T+104LL*ntrans(I,i)*(m[i]-n[i]); if(!c.ok||canon(c.word)!=CW||c.T!=pred){ST.xval_bad++; fprintf(LOG,"XVAL MISMATCH %s param %d T=%lld pred=%lld\n",F.tag.c_str(),i,c.T,pred);} } }
      // slabs: members with some n_i in [n0_i, n_i)
      for(int i=0;i<d;++i) for(int val=n0[i];val<n[i];++val){ ST.slabs++;
        Fam G; G.tag=F.tag+"|slab"+to_string(i)+"="+to_string(val); vector<int> m;
        for(int j=0;j<d;++j) if(j!=i){G.v.push_back(F.v[j]); m.push_back(n0[j]);}
        for(auto&b:F.blk){ array<int,3> c=b; if(b[2]>>i&1){c[0]+=val*F.v[i][0];c[1]+=val*F.v[i][1];}
          int nm=0,k2=0; for(int j=0;j<d;++j){ if(j==i)continue; if(b[2]>>j&1)nm|=1<<k2; ++k2;} c[2]=nm; G.blk.push_back(c);}
        // other params: members below n but >= n0 in other coordinates are covered because the slab family itself is proved from n0
        vector<int> nb2; Info I2; if(!prove(G,m,nb2,I2,depth+1))return false; }
      nb=n; ST.fam_ok++; for(int i=0;i<d;++i)ST.ntr[ntrans(I,i)]++; if(COLLECT)COLLECT->push_back({F,n});
      { static FILE* FD=getenv("FAMDUMP")?fopen(getenv("FAMDUMP"),"w"):nullptr; static int FM=getenv("FAMMOD")?atoi(getenv("FAMMOD")):100; static ll fc=0;
        static int FMIN=getenv("FAMMIND")?atoi(getenv("FAMMIND")):0; if(FD&&d>=FMIN&&(fc++%FM==0)){ fprintf(FD,"%d",d); for(auto&vv:F.v)fprintf(FD," %d %d",vv[0],vv[1]); fprintf(FD," %zu",F.blk.size()); for(auto&b:F.blk)fprintf(FD," %d %d %d",b[0],b[1],b[2]);
          for(int x:n)fprintf(FD," %d",x); fprintf(FD," | %lld",I.T); for(int i=0;i<d;++i)fprintf(FD," %d",ntrans(I,i)); for(int i=0;i<d;++i)fprintf(FD," %lld %lld",I.P[i].Dtop,I.P[i].Cbot);
          for(int i=0;i<d;++i)for(auto&t:I.P[i].tr)fprintf(FD," %lld",t[3]); fprintf(FD,"\n"); fflush(FD);} }
      if(getenv("SHOWBASE")&&n!=n0){fprintf(LOG,"BASE RAISED %s d=%d:",F.tag.c_str(),d); for(int i=0;i<d;++i)fprintf(LOG," %d->%d",n0[i],n[i]); fprintf(LOG," first_fail=%s\n",firstwhy.c_str());}
      return true;
    }
    if(I.failp<0) break;               // certificate failure: increasing parameters will not help directly
    n[I.failp]+=4;
  }
  ST.fam_fail++; ST.why[I.why]++; fprintf(LOG,"FAMILY FAIL %s why=%s param=%d n=",F.tag.c_str(),I.why.c_str(),I.failp); for(int x:n)fprintf(LOG," %d",x);
  fprintf(LOG," | v:"); for(auto&vv:F.v)fprintf(LOG," (%d,%d)",vv[0],vv[1]); fprintf(LOG," blk:"); for(auto&b:F.blk)fprintf(LOG," (%d,%d,%d)",b[0],b[1],b[2]); fprintf(LOG," n0:"); for(int x:n0)fprintf(LOG," %d",x); fprintf(LOG,"\n");
  return false;
}

// --------- extension: all ways to add one cell, classified by the phase that first reads it ----------

// sparse filter: true if EVERY member of the family has two cells (or a cell and the ant's start)
// closer than RSP in the Chebyshev metric. Cells with equal masks keep a constant offset.
static bool allViolate(const Fam&F,const vector<int>&n){
  if(RSP<=0)return false; auto pos=[&](const array<int,3>&b){int x=b[0],y=b[1]; for(size_t i=0;i<F.v.size();++i)if(b[2]>>i&1){x+=n[i]*F.v[i][0];y+=n[i]*F.v[i][1];} return make_pair(x,y);};
  for(size_t a=0;a<F.blk.size();++a){ auto p=pos(F.blk[a]); if(F.blk[a][2]==0&&max(abs(p.first),abs(p.second))<RSP)return true;
    for(size_t b=a+1;b<F.blk.size();++b){ if(F.blk[a][2]!=F.blk[b][2])continue; auto q=pos(F.blk[b]); if(max(abs(p.first-q.first),abs(p.second-q.second))<RSP)return true; } }
  return false; }
struct Child { Fam F; vector<int> n0; };
static vector<Child> extend(const Fam&F,const vector<int>&n,const Info&I){
  vector<Child> out; int d=F.v.size();
  auto cells=cfg(F,n);
  ll Text=I.T+104LL*(K+16);
  Rec R=record(cells,Text); ST.updates+=R.X.size();
  ll Tr=R.X.size();
  // divergence: last first-read among the family's blocks (blocks never read are ignored)
  ll tdiv=-1; set<long long> blockset; for(auto&p:cells){blockset.insert(KEY(p.first,p.second)); auto it=R.first.find(KEY(p.first,p.second)); if(it!=R.first.end())tdiv=max(tdiv,it->second);}
  // side of each corridor at time t (outside transits) and transit membership
  auto sideAt=[&](int i,ll t){int sd=-1; for(auto&tr:I.P[i].tr) if(t>tr[3])sd=-sd; return sd;};
  auto transitOf=[&](ll t)->int{for(int i=0;i<d;++i)for(auto&tr:I.P[i].tr) if(t>=tr[0]&&t<=tr[1]+104) return i; return -1;};
  auto maskAt=[&](ll t){int m=0; for(int i=0;i<d;++i) if(sideAt(i,t)>0)m|=1<<i; return m;};
  // block offset at n=0 baseline for a cell z seen at time t with mask m
  auto base0=[&](int zx,int zy,int m){array<int,3> b={zx,zy,m}; for(int i=0;i<d;++i)if(m>>i&1){b[0]-=n[i]*F.v[i][0];b[1]-=n[i]*F.v[i][1];} return b;};
  // tail geometry
  int ux=I.c.ux,uy=I.c.uy; ll s=I.c.s; auto psu=[&](ll x,ll y){return PHI(ux,uy,x,y);};
  ll psipre=LLONG_MIN; for(ll w=0;w<s&&w<Tr;++w)psipre=max(psipre,psu(R.X[w],R.Y[w]));
  for(auto&p:cells)psipre=max(psipre,psu(p.first,p.second));
  ll L=1; bool Lok=false; while(s+104*(L+2)<Tr){ ll mn=LLONG_MAX; for(ll w=s+104*L;w<s+104*(L+1);++w)mn=min(mn,psu(R.X[w],R.Y[w])); if(mn>psipre+4){Lok=true;break;} ++L; }
  if(!Lok){fprintf(LOG,"EXTEND: no tail margin %s\n",F.tag.c_str()); return out;}
  ll t1=s+104*L, T2=t1+104LL*K; if(T2+104*6>=Tr){fprintf(LOG,"EXTEND: run too short %s\n",F.tag.c_str()); return out;}
  int Mf=maskAt(I.T);
  // ---- F1: footprint periodicity for transits after tdiv (needed for the split partition, Lemma 4)
  auto fdiv=[](ll a,ll b){ll q=a/b; if((a%b!=0)&&((a<0)!=(b<0)))--q; return q;};
  for(int i=0;i<d;++i){ int vx=F.v[i][0],vy=F.v[i][1]; ll Dt=I.P[i].Dtop;
    auto ell=[&](int x,int y){return fdiv(PHI(vx,vy,x,y)-Dt,4);};
    ll lhi=LLONG_MIN; for(auto&tr:I.P[i].tr) lhi=max(lhi,ell(I.X[tr[3]],I.Y[tr[3]])+1);
    for(auto&tr:I.P[i].tr){ ll b=tr[0], e=min(tr[1]+104,Tr-1); if(e<=tdiv)continue;
      set<pair<int,int>> Ff,Fn; for(ll t=max(b,tdiv+1);t<=e;++t){ Ff.insert({R.X[t],R.Y[t]}); auto it=R.first.find(KEY(R.X[t],R.Y[t])); if(it!=R.first.end()&&it->second==t&&!blockset.count(KEY(R.X[t],R.Y[t])))Fn.insert({R.X[t],R.Y[t]}); }
      // the part of the span before tdiv cannot carry new cells; full footprint periodicity is checked on the post-tdiv part only
      for(auto*S:{&Ff,&Fn}) for(auto&z:*S){ ll l=ell(z.first,z.second);
        if(l>=LS&&l<=lhi-1&&!S->count({z.first+vx,z.second+vy})){ if(S==&Fn||(b>tdiv)){ST.why["F1_footprint"]++; fprintf(LOG,"EXTEND F1 FAIL %s param %d index %lld\n",F.tag.c_str(),i,l); return out;} }
        if(l>=LS+1&&l<=lhi&&!S->count({z.first-vx,z.second-vy})){ if(S==&Fn||(b>tdiv)){ST.why["F1_footprint"]++; fprintf(LOG,"EXTEND F1 FAIL %s param %d index %lld\n",F.tag.c_str(),i,l); return out;} } }
    } }
  // classify every cell first read after tdiv
  map<pair<int,int>,int> seenSplit; ll nsplit=0;
  for(auto&kv:R.first){ ll t=kv.second; if(t<=tdiv)continue; if(blockset.count(kv.first))continue;
    int zx=(int)(kv.first>>32), zy=(int)(uint32_t)kv.first;
    if(t>=t1) continue;                                  // tail classes handled below (t in [t1,t1+104) reps; later ones are class members)
    if(t>=s){ Child c; c.F=F; c.F.blk.push_back(base0(zx,zy,Mf)); c.F.tag=F.tag+"+tailnear"; c.n0=n; out.push_back(c); continue; }
    int ti=transitOf(t);
    { int owners=0; for(int i=0;i<d;++i)for(auto&tr:I.P[i].tr) if(t>=tr[0]&&t<=tr[1]+104){owners++;break;}
      if(owners>1){ST.why["span_overlap"]++; fprintf(LOG,"EXTEND SPAN OVERLAP %s at t=%lld\n",F.tag.c_str(),t); return {};} }
    if(ti<0){ Child c; c.F=F; c.F.blk.push_back(base0(zx,zy,maskAt(t))); c.F.tag=F.tag+"+site"; c.n0=n; out.push_back(c); continue; }
    // first read during a transit of corridor ti: near / far attachment or split
    int vx=F.v[ti][0],vy=F.v[ti][1]; ll ph=PHI(vx,vy,zx,zy); ll idx=fdiv(ph-I.P[ti].Dtop,4);
    int mo=maskAt(t)&~(1<<ti);
    if(idx<LS){ Child c; c.F=F; c.F.blk.push_back(base0(zx,zy,mo)); c.F.tag=F.tag+"+transnear"; c.n0=n; out.push_back(c); continue; }
    if(idx>LS){ Child c; c.F=F; c.F.blk.push_back(base0(zx,zy,mo|(1<<ti))); c.F.tag=F.tag+"+transfar"; c.n0=n; out.push_back(c); continue; }
    // idx == LS : representative of a footprint class -> split corridor ti into (near part, far part)
    nsplit++;
    Child c; c.F.tag=F.tag+"+split"; c.F.v=F.v; c.F.v.push_back(F.v[ti]); int a=ti, bnew=d; // param a = near length t, bnew = far length
    for(auto&b:F.blk){ array<int,3> q=b; if(b[2]>>ti&1)q[2]|=1<<bnew; c.F.blk.push_back(q);}  // far blocks move with both
    // S at index LS when param a = LS: b0 = z - LS*v - (other masked params)*v
    array<int,3> S=base0(zx,zy,mo); S[0]-=LS*vx; S[1]-=LS*vy; S[2]|=1<<a; c.F.blk.push_back(S);
    // far blocks: old position used n[ti] = t + s; with t=LS, s = n[ti]-LS ; their b0 already includes -n[ti]*v via base; adjust:
    // in the parent, far block cell = b0 + n_ti v ; in the child, cell = b0 + (t + s) v -> same b0, bits a and bnew.
    c.n0=n; c.n0[a]=LS; c.n0.push_back(n[ti]-LS); out.push_back(c);
  }
  // tail classes: reps first read in [t1, t1+104) after s, not blocks, new corridor along u beyond the final frame
  for(auto&kv:R.first){ ll t=kv.second; if(t<t1||t>=t1+104)continue; if(blockset.count(kv.first))continue;
    int zx=(int)(kv.first>>32), zy=(int)(uint32_t)kv.first;
    // class check on this run: first read of z + j u is t + 104 j
    bool okc=true; for(int j=1;j<=K+4;++j){ auto it=R.first.find(KEY(zx+j*ux,zy+j*uy)); if(it==R.first.end()||it->second!=t+104LL*j){okc=false;break;} }
    if(!okc){fprintf(LOG,"EXTEND: tail class structure fails %s\n",F.tag.c_str()); continue;}
    Child c; c.F.tag=F.tag+"+tail"; c.F.v=F.v; c.F.v.push_back({ux,uy}); c.F.blk=F.blk;
    array<int,3> S=base0(zx,zy,Mf); S[2]|=1<<d; c.F.blk.push_back(S); c.n0=n; c.n0.push_back(K); out.push_back(c);
  }
  // tail cells first read in [t1, T2) are members j in [0, K) of the tail classes: attach them directly (final frame)
  for(auto&kv:R.first){ ll t=kv.second; if(t<t1||t>=T2)continue; if(blockset.count(kv.first))continue;
    int zx=(int)(kv.first>>32), zy=(int)(uint32_t)kv.first; Child c; c.F=F; c.F.blk.push_back(base0(zx,zy,Mf)); c.F.tag=F.tag+"+tailnear"; c.n0=n; out.push_back(c); }
  if(nsplit)fprintf(LOG,"EXTEND %s: %lld split families\n",F.tag.c_str(),nsplit);
  return out;
}

int main(int argc,char**argv){
  string mode=argc>1?argv[1]:"level1";
  if(getenv("K"))K=atoi(getenv("K")); if(getenv("XVAL"))XVAL=true;
  if(getenv("DUMP")){DUMP=fopen(getenv("DUMP"),"w"); if(getenv("DUMPMOD"))DUMPMOD=atoi(getenv("DUMPMOD")); else DUMPMOD=1000;}
  { Cert cb=RU.certify({},0,200000); CW=canon(cb.word); }
  Fam blank; blank.tag="blank";
  vector<int> nb; Info Ib; if(!prove(blank,{},nb,Ib)){puts("blank failed");return 1;}
  Ib=verify(blank,{});   // full info (d=0) for extension
  auto L1=extend(blank,{},Ib);
  ll l1_direct=0,l1_fam=0; for(auto&c:L1){ if(c.F.v.empty())l1_direct++; else l1_fam++; }
  fprintf(LOG,"level 1: %lld concrete single-cell configurations, %lld one-parameter families\n",l1_direct,l1_fam);
  if(mode=="level1"){
    for(auto&c:L1){ vector<int> nb2; Info I2; prove(c.F,c.n0,nb2,I2); }
    fprintf(LOG,"LEVEL1 families ok=%lld fail=%lld direct ok=%lld fail=%lld slabs=%lld xval=%lld bad=%lld updates=%lld\n",ST.fam_ok,ST.fam_fail,ST.direct_ok,ST.direct_fail,ST.slabs,ST.xval,ST.xval_bad,ST.updates);
    for(auto&w:ST.why)fprintf(LOG,"  fail reason %s: %lld\n",w.first.c_str(),w.second);
    for(auto&w:ST.ntr)fprintf(LOG,"  corridors with %d transits: %lld\n",w.first,w.second);
    return 0;
  }
  if(mode=="inspect"){
    int d; cin>>d; Fam F; F.tag="inspect"; F.v.resize(d); for(auto&x:F.v)cin>>x[0]>>x[1]; int nb; cin>>nb; F.blk.resize(nb); for(auto&b:F.blk)cin>>b[0]>>b[1]>>b[2];
    vector<int> n(d); for(auto&x:n)cin>>x;
    Info I=verify(F,n); printf("verify: ok=%d why=%s failp=%d T=%lld cert u=(%d,%d) s=%lld\n",(int)I.ok,I.why.c_str(),I.failp,I.T,I.c.ux,I.c.uy,I.c.s);
    for(int i=0;i<(int)I.P.size();++i){ auto&P=I.P[i]; printf(" param %d v=(%d,%d) mu=%lld D=%lld C=%lld final_side=%d transits:",i,F.v[i][0],F.v[i][1],P.mu,P.Dtop,P.Cbot,P.final_side);
      for(auto&t:P.tr)printf(" [b=%lld e=%lld sg=%lld m=%lld]",t[0],t[1],t[2],t[3]); printf("\n"); }
    return 0; }
  if(mode=="covertest"){
    // Lemma 4 surjectivity test: for each level-1 entry (family or concrete), extend at its proved base, then for
    // several larger members n' run the configuration and check that EVERY cell first read after the blocks is a
    // member of some child family (with parameters >= that child's base), or never read.
    int reps=getenv("REPS")?atoi(getenv("REPS")):6; mt19937 rng(12345); ll tested=0,cells_checked=0,gaps=0,ambig=0;
    int stride=getenv("STRIDE")?atoi(getenv("STRIDE")):1; ll idx=0;
    for(auto&c:L1){ if((idx++)%stride)continue; vector<int> nb1; Info I1; if(!prove(c.F,c.n0,nb1,I1))continue; Info IP=verify(c.F,nb1); auto ch=extend(c.F,nb1,IP);
      int d=c.F.v.size();
      for(int r=0;r<(d?reps:1);++r){ vector<int> np=nb1; for(int i=0;i<d;++i)np[i]+=1+rng()%60;
        auto cells=cfg(c.F,np); Info In=verify(c.F,np); if(!In.ok){printf("member reverify fail %s\n",c.F.tag.c_str());continue;}
        Rec R=record(cells,In.T+104LL*(K+16)); set<long long> bs; ll tdiv=-1; for(auto&p:cells){bs.insert(KEY(p.first,p.second)); auto it=R.first.find(KEY(p.first,p.second)); if(it!=R.first.end())tdiv=max(tdiv,it->second);}
        // limit to cells first read before the tail margin region of the member (tail cells beyond are class members by descent)
        tested++;
        for(auto&kv:R.first){ if(kv.second<=tdiv||bs.count(kv.first))continue; int zx=(int)(kv.first>>32), zy=(int)(uint32_t)kv.first; cells_checked++;
          int hits=0;
          for(auto&cc:ch){ int dc=cc.F.v.size(); const array<int,3>&S=cc.F.blk.back();
            // parent blocks must coincide: child keeps parent's blocks first (possibly with extra bits for split)
            if(dc==d){ // attachment: same params
              int x=S[0],y=S[1]; for(int i=0;i<d;++i)if(S[2]>>i&1){x+=np[i]*cc.F.v[i][0];y+=np[i]*cc.F.v[i][1];}
              bool ok=(x==zx&&y==zy); for(int i=0;i<d&&ok;++i) if(np[i]<cc.n0[i])ok=false; if(ok)hits++; }
            else if(dc==d+1){ int nx=cc.F.v[d][0],ny=cc.F.v[d][1];
              bool isSplit=cc.F.tag.size()>=6&&cc.F.tag.substr(cc.F.tag.size()-6)=="+split";
              if(!isSplit){ // tail: S = S0 + sum np_i v_i (mask) + j*u
                int x=S[0],y=S[1]; for(int i=0;i<d;++i)if(S[2]>>i&1){x+=np[i]*cc.F.v[i][0];y+=np[i]*cc.F.v[i][1];}
                int dx=zx-x,dy=zy-y; if(nx!=0&&dx%nx==0){int j=dx/nx; if(j*ny==dy&&j>=cc.n0[d]){bool ok=true; for(int i=0;i<d;++i)if(np[i]<cc.n0[i])ok=false; if(ok)hits++;}} }
              else { // split of corridor ti (param a=ti near length t, param d far length s), t+s = np[ti]
                int ti=-1; for(int i=0;i<d;++i) if((S[2]>>i&1)&&cc.F.v[i]==cc.F.v[d]) ti=i;  // S moves with near part
                if(ti<0)continue; int vx=cc.F.v[ti][0],vy=cc.F.v[ti][1];
                int x=S[0],y=S[1]; for(int i=0;i<d;++i)if(i!=ti&&(S[2]>>i&1)){x+=np[i]*cc.F.v[i][0];y+=np[i]*cc.F.v[i][1];}
                int dx=zx-x,dy=zy-y; if(dx%vx==0){int t=dx/vx; if(t*vy==dy){int sfar=np[ti]-t; if(t>=cc.n0[ti]&&sfar>=cc.n0[d])hits++;}} } } }
          if(hits==0){ gaps++; if(gaps<=10)printf("GAP %s member n'=",c.F.tag.c_str()),[&]{for(int x:np)printf(" %d",x);}(),printf(" cell (%d,%d) first read %lld\n",zx,zy,kv.second); }
          if(hits>1)ambig++; } } }
    printf("COVERTEST: members tested %lld, new cells checked %lld, uncovered %lld, multiply covered %lld\n",tested,cells_checked,gaps,ambig);
    return 0; }
  if(mode=="leandump"){
    // For every concrete level-1 entry F (blank first-read order): Lean hints for check0 [F] with its 22 tail families.
    Rec RB=record({},200000); int periods=getenv("PERIODS")?atoi(getenv("PERIODS")):6000;
    auto Amin=[&](const vector<pair<int,int>>&cells,ll s,int ux,int uy){ Rec R=record(cells,s+106); ll mn=LLONG_MAX; for(ll w=s;w<=s+104;++w)mn=min(mn,(ll)ux*R.X[w]+(ll)uy*R.Y[w]); return mn-1; };
    vector<pair<ll,const decltype(L1)::value_type*>> conc;
    for(auto&c:L1) if(c.F.v.empty()){ auto cells=cfg(c.F,{}); auto it=RB.first.find(KEY(cells[0].first,cells[0].second)); conc.push_back({it==RB.first.end()?-1:it->second,&c}); }
    sort(conc.begin(),conc.end(),[](auto&a,auto&b){return a.first<b.first;});
    for(auto&pc:conc){ auto&c=*pc.second; auto cells=cfg(c.F,{}); vector<int> nb1; Info I1; if(!prove(c.F,{},nb1,I1)){fprintf(stderr,"PROVE FAIL\n");continue;}
      Info IP=verify(c.F,{}); ll s=IP.c.s; int ux=IP.c.ux,uy=IP.c.uy;
      Rec R=record(cells,IP.T+104LL*(K+16)); ll Tr=R.X.size(); auto psu=[&](ll x,ll y){return PHI(ux,uy,x,y);};
      ll psipre=LLONG_MIN; for(ll w=0;w<s&&w<Tr;++w)psipre=max(psipre,psu(R.X[w],R.Y[w])); for(auto&q:cells)psipre=max(psipre,psu(q.first,q.second));
      ll L=1; while(true){ ll mn=LLONG_MAX; for(ll w=s+104*L;w<s+104*(L+1);++w)mn=min(mn,psu(R.X[w],R.Y[w])); if(mn>psipre+4)break; ++L; }
      ll t1=s+104*L;
      printf("F %d %d %lld | %lld %d %d %lld %lld %lld %lld %d |",cells[0].first,cells[0].second,pc.first,s,ux,uy,Amin(cells,s,ux,uy),t1,psipre,pc.first+1,periods);
      auto ch=extend(c.F,{},IP);
      for(auto&cc:ch){ if(cc.F.tag.size()<5||cc.F.tag.substr(cc.F.tag.size()-5)!="+tail")continue;
        vector<int> nb2; Info I2; if(!prove(cc.F,cc.n0,nb2,I2)){fprintf(stderr,"FAM PROVE FAIL\n");continue;}
        Info I3=verify(cc.F,nb2); auto mc=cfg(cc.F,nb2);
        const auto&S=cc.F.blk.back();
        printf(" %d %d %d %d %d %d %lld %lld [",S[0],S[1],cc.F.v[0][0],cc.F.v[0][1],nb2[0],(int)I3.P.size()?0:0,I3.P[0].Dtop,I3.P[0].Cbot);
        bool first=true; for(auto&t:I3.P[0].tr){printf("%s%lld",first?"":",",t[3]);first=false;}
        printf("] %lld %d %d %lld ;",I3.c.s,I3.c.ux,I3.c.uy,Amin(mc,I3.c.s,I3.c.ux,I3.c.uy)); }
      printf("\n"); fflush(stdout); }
    return 0; }
  if(mode=="chandump"){
    // For each level-1 family (channel parent) in L1 order: every child of the extension at the proved base,
    // with checker hints for one-parameter children.
    auto Amin=[&](const vector<pair<int,int>>&cells,ll s,int ux,int uy){ Rec R=record(cells,s+106); ll mn=LLONG_MAX; for(ll w=s;w<=s+104;++w)mn=min(mn,(ll)ux*R.X[w]+(ll)uy*R.Y[w]); return mn-1; };
    for(auto&c:L1){ if(c.F.v.empty())continue;
      vector<int> nb1; Info I1; if(!prove(c.F,c.n0,nb1,I1))continue; Info IP=verify(c.F,nb1); auto ch=extend(c.F,nb1,IP);
      printf("P %d %d %d\n",c.F.blk[0][0],c.F.blk[0][1],nb1[0]);
      for(auto&cc:ch){ int d=cc.F.v.size(); printf("C %d",d); for(auto&vv:cc.F.v)printf(" %d %d",vv[0],vv[1]);
        printf(" %zu",cc.F.blk.size()); for(auto&b:cc.F.blk)printf(" %d %d %d",b[0],b[1],b[2]); printf(" |"); for(int x:cc.n0)printf(" %d",x);
        if(d==1){ vector<int> nb2; Info I2; if(!prove(cc.F,cc.n0,nb2,I2)){printf(" | FAIL\n");continue;}
          Info I3=verify(cc.F,nb2); auto mc=cfg(cc.F,nb2);
          printf(" | %d %lld %lld [",nb2[0],I3.P[0].Dtop,I3.P[0].Cbot); bool first=true; for(auto&t:I3.P[0].tr){printf("%s%lld",first?"":",",t[3]);first=false;}
          printf("] %lld %d %d %lld",I3.c.s,I3.c.ux,I3.c.uy,Amin(mc,I3.c.s,I3.c.ux,I3.c.uy)); }
        printf("\n"); }
      printf("E\n"); fflush(stdout); }
    return 0; }
  if(mode=="perpinfo"){
    for(auto&c:L1){ if(c.F.v.empty())continue;
      vector<int> nb1; Info I1; if(!prove(c.F,c.n0,nb1,I1))continue; Info IP=verify(c.F,nb1); auto ch=extend(c.F,nb1,IP);
      for(auto&cc:ch){ if(cc.F.v.size()!=2)continue; bool perp=(cc.F.v[0][0]*cc.F.v[1][0]+cc.F.v[0][1]*cc.F.v[1][1])==0;
        ll s0=ST.slabs; vector<int> nb2; Info I2; bool ok=prove(cc.F,cc.n0,nb2,I2);
        printf("%s ok=%d n0=(%d,%d) nb=(%d,%d) slabs=%lld\n",perp?"perp":"par",(int)ok,cc.n0[0],cc.n0[1],nb2.size()?nb2[0]:-1,nb2.size()?nb2[1]:-1,ST.slabs-s0); } }
    return 0; }
  if(mode=="perpdump"||mode=="pardump"){ bool wantPar=(mode=="pardump");
    // perpendicular two-parameter children of the channel parents: hints at the proved base + slab families
    auto Amin=[&](const vector<pair<int,int>>&cells,ll s,int ux,int uy){ Rec R=record(cells,s+106); ll mn=LLONG_MAX; for(ll w=s;w<=s+104;++w)mn=min(mn,(ll)ux*R.X[w]+(ll)uy*R.Y[w]); return mn-1; };
    auto prTr=[&](const PInfo&P){ printf(" %lld %lld [",P.Dtop,P.Cbot); bool f=true; for(auto&t:P.tr){printf("%s%lld",f?"":",",t[3]);f=false;} printf("]"); };
    int pi=-1;
    for(auto&c:L1){ if(c.F.v.empty())continue; ++pi;
      vector<int> nb1; Info I1; if(!prove(c.F,c.n0,nb1,I1))continue; Info IP=verify(c.F,nb1); auto ch=extend(c.F,nb1,IP);
      int kj=-1;
      for(auto&cc:ch){ if(cc.F.v.size()!=2)continue; ++kj;
        bool perp=(cc.F.v[0][0]*cc.F.v[1][0]+cc.F.v[0][1]*cc.F.v[1][1])==0; if(perp==wantPar)continue;
        vector<int> nb2; Info I2; if(!prove(cc.F,cc.n0,nb2,I2)){printf("FAIL\n");continue;}
        Info I3=verify(cc.F,nb2); auto mc=cfg(cc.F,nb2);
        printf("K %d %d | %d %d |",pi,kj,nb2[0],nb2[1]); prTr(I3.P[0]); printf(" |"); prTr(I3.P[1]);
        printf(" | %lld %d %d %lld\n",I3.c.s,I3.c.ux,I3.c.uy,Amin(mc,I3.c.s,I3.c.ux,I3.c.uy));
        // slabs, exactly as in prove(): freeze param i at val in [n0_i, nb_i), the other param from n0
        for(int i=0;i<2;++i) for(int val=cc.n0[i];val<nb2[i];++val){
          Fam G; G.tag="slab"; int o=1-i; G.v.push_back(cc.F.v[o]);
          for(auto&b:cc.F.blk){ array<int,3> q=b; if(b[2]>>i&1){q[0]+=val*cc.F.v[i][0];q[1]+=val*cc.F.v[i][1];} q[2]=(b[2]>>o&1)?1:0; G.blk.push_back(q);}
          vector<int> nbG; Info IG; if(!prove(G,{cc.n0[o]},nbG,IG)){printf("SLABFAIL\n");continue;}
          Info IG3=verify(G,nbG); auto gc=cfg(G,nbG);
          printf("S %d %d %d %d | %d %d",i,val,G.v[0][0],G.v[0][1],cc.n0[o],nbG[0]);
          printf(" | %zu",G.blk.size()); for(auto&b:G.blk)printf(" %d %d %d",b[0],b[1],b[2]);
          printf(" |"); prTr(IG3.P[0]); printf(" | %lld %d %d %lld\n",IG3.c.s,IG3.c.ux,IG3.c.uy,Amin(gc,IG3.c.s,IG3.c.ux,IG3.c.uy)); }
      } }
    return 0; }
  if(mode=="childdump"){
    // dump level-1 parents (all families, every STRIDE-th concrete entry) with their proved base and the children
    // produced by extend at that base, for the independent Python coverage test
    int stride=getenv("STRIDE")?atoi(getenv("STRIDE")):16; ll idx=0;
    auto pf=[&](const char*tag,const Fam&F,const vector<int>&n){ printf("%s %zu",tag,F.v.size()); for(auto&vv:F.v)printf(" %d %d",vv[0],vv[1]); printf(" %zu",F.blk.size());
      for(auto&b:F.blk)printf(" %d %d %d",b[0],b[1],b[2]); printf(" |"); for(int x:n)printf(" %d",x); printf("\n"); };
    for(auto&c:L1){ bool isfam=!c.F.v.empty(); if(!isfam&&((idx++)%stride))continue;
      vector<int> nb1; Info I1; if(!prove(c.F,c.n0,nb1,I1))continue; Info IP=verify(c.F,nb1); auto ch=extend(c.F,nb1,IP);
      pf("P",c.F,nb1); for(auto&cc:ch)pf("C",cc.F,cc.n0); printf("E\n"); }
    return 0; }
  if(mode=="shapes"){
    int BOX=getenv("BOX")?atoi(getenv("BOX")):3;
    vector<vector<pair<int,int>>> shapes; set<vector<pair<int,int>>> seen;
    for(int m=1;m<(1<<(BOX*BOX));++m){vector<pair<int,int>> sh; for(int j=0;j<BOX*BOX;++j)if(m>>j&1)sh.push_back({j%BOX,j/BOX});
      int mx=INT_MAX,my=INT_MAX; for(auto&p:sh){mx=min(mx,p.first);my=min(my,p.second);} for(auto&p:sh){p.first-=mx;p.second-=my;} sort(sh.begin(),sh.end());
      if(seen.insert(sh).second)shapes.push_back(sh);}
    // blank run data
    Rec R=record({},60000); ll s=Ib.c.s; int ux=Ib.c.ux,uy=Ib.c.uy; auto psu=[&](ll x,ll y){return PHI(ux,uy,x,y);};
    ll psipre=LLONG_MIN; for(ll w=0;w<s;++w)psipre=max(psipre,psu(R.X[w],R.Y[w]));
    ll L=1; while(true){ll mn=LLONG_MAX; for(ll w=s+104*L;w<s+104*(L+1);++w)mn=min(mn,psu(R.X[w],R.Y[w])); if(mn>psipre+4)break; ++L;}
    ll t1=s+104*L; fprintf(LOG,"blank: s=%lld u=(%d,%d) psipre=%lld t1=%lld\n",s,ux,uy,psipre,t1);
    auto TAU=[&](int x,int y)->ll{auto it=R.first.find(KEY(x,y));return it==R.first.end()?LLONG_MAX:it->second;};
    ll nfam=0; map<int,ll> perK;
    for(auto&P:shapes){
      set<pair<int,int>> reps; for(ll w=t1;w<t1+104;++w)for(auto&q:P){int ox=R.X[w]-q.first,oy=R.Y[w]-q.second; ll m=LLONG_MAX; for(auto&q2:P)m=min(m,TAU(q2.first+ox,q2.second+oy)); if(m>=t1&&m<t1+104)reps.insert({ox,oy});}
      for(auto&o:reps){ Fam F; F.tag="shape"; F.v.push_back({ux,uy}); for(auto&q:P)F.blk.push_back({q.first+o.first,q.second+o.second,1});
        vector<int> nb2; Info I2; nfam++; if(prove(F,{K},nb2,I2))perK[nb2[0]]++; } }
    fprintf(LOG,"SHAPES box=%d: shapes=%zu families=%lld ok=%lld fail=%lld concrete(slab members) ok=%lld fail=%lld slabs=%lld xval=%lld bad=%lld updates=%lld\n",BOX,shapes.size(),nfam,ST.fam_ok,ST.fam_fail,ST.direct_ok,ST.direct_fail,ST.slabs,ST.xval,ST.xval_bad,ST.updates);
    for(auto&w:ST.ntr)fprintf(LOG,"  corridors with %d transits: %lld\n",w.first,w.second);
    ll nonbase=0; for(auto&p:perK) if(p.first!=K) nonbase+=p.second; fprintf(LOG,"  families needing base > %d: %lld\n",K,nonbase);
    return 0;
  }
  if(mode=="sparse"){
    RSP=getenv("RSP")?atoi(getenv("RSP")):160; int depth=getenv("DEPTH")?atoi(getenv("DEPTH")):3;
    vector<pair<Fam,vector<int>>> cur; cur.push_back({blank,{}});
    vector<ll> lvlcount;
    for(int lv=1;lv<=depth;++lv){
      vector<pair<Fam,vector<int>>> proved; COLLECT=&proved; ll nch=0,npruned=0;
      int shard=getenv("SHARD")?atoi(getenv("SHARD")):0, nshard=getenv("NSHARD")?atoi(getenv("NSHARD")):1; ll resume=getenv("RESUME")?atoll(getenv("RESUME")):0;
      bool last=(lv==depth); ll idx=-1; auto t0=chrono::steady_clock::now();
      for(auto&pp:cur){ ++idx; if(last&&(idx%nshard!=shard||idx<resume))continue;
        if(allViolate(pp.first,pp.second))continue; Info IP=verify(pp.first,pp.second); if(!IP.ok){fprintf(LOG,"PARENT REVERIFY FAIL %s\n",pp.first.tag.c_str());continue;}
        auto ch=extend(pp.first,pp.second,IP); ll k0=nch, f0=ST.fam_fail+ST.direct_fail;
        for(auto&cc:ch){ if(allViolate(cc.F,cc.n0)){npruned++;continue;} nch++; vector<int> nb2; Info I2; prove(cc.F,cc.n0,nb2,I2); }
        if(last){ long rss=0; {FILE*f=fopen("/proc/self/statm","r"); long a,b; if(f&&fscanf(f,"%ld %ld",&a,&b)==2)rss=b*4/1024; if(f)fclose(f);}
          double sec=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
          fprintf(LOG,"L%d parent %lld/%zu (d=%zu) kept %lld new fails %lld | cum fam ok %lld fail %lld conc ok %lld fail %lld xval %lld bad %lld | %.0fs rss %ldMB\n",lv,idx,cur.size(),pp.first.v.size(),nch-k0,ST.fam_fail+ST.direct_fail-f0,ST.fam_ok,ST.fam_fail,ST.direct_ok,ST.direct_fail,ST.xval,ST.xval_bad,sec,rss); fflush(LOG);} }
      COLLECT=nullptr;
      fprintf(LOG,"SPARSE level %d (R=%d): children kept %lld, pruned %lld; proved entries %zu; cumulative families ok=%lld fail=%lld concrete ok=%lld fail=%lld slabs=%lld xval=%lld bad=%lld updates=%lld\n",
              lv,RSP,nch,npruned,proved.size(),ST.fam_ok,ST.fam_fail,ST.direct_ok,ST.direct_fail,ST.slabs,ST.xval,ST.xval_bad,ST.updates); fflush(LOG);
      map<int,ll> dims; for(auto&p:proved)dims[p.first.v.size()]++; for(auto&dd:dims)fprintf(LOG,"   proved entries with %d parameters: %lld\n",dd.first,dd.second);
      for(auto&w:ST.why)fprintf(LOG,"   fail reason %s: %lld\n",w.first.c_str(),w.second);
      cur.swap(proved);
    }
    for(auto&w:ST.ntr)fprintf(LOG,"  corridors with %d transits: %lld\n",w.first,w.second);
    return 0;
  }
  if(mode=="level2"){
    // optional sharding over level-1 entries
    int shard=getenv("SHARD")?atoi(getenv("SHARD")):0, nshard=getenv("NSHARD")?atoi(getenv("NSHARD")):1;
    int only=getenv("ONLY")?atoi(getenv("ONLY")):-1;   // -1 all, 0 = only families, 1 = only concrete
    ll idx=0, nl1=0, nchildren=0;
    for(auto&c:L1){ ll me=idx++; if(me%nshard!=shard)continue;
      bool isfam=!c.F.v.empty(); if(only==0&&!isfam)continue; if(only==1&&isfam)continue;
      vector<int> nb1; Info I1; if(!prove(c.F,c.n0,nb1,I1)){fprintf(LOG,"LEVEL1 FAIL %s\n",c.F.tag.c_str()); continue;}
      nl1++;
      // children of the proved family at its base, and of every slab below the base (slabs are concrete for 1-param families)
      vector<pair<Fam,vector<int>>> parents; parents.push_back({c.F,nb1});
      if(isfam) for(int val=c.n0[0];val<nb1[0];++val){ Fam G; G.tag=c.F.tag+"|slab="+to_string(val); for(auto&b:c.F.blk){array<int,3> q=b; if(b[2]&1){q[0]+=val*c.F.v[0][0];q[1]+=val*c.F.v[0][1];} q[2]=0; G.blk.push_back(q);} parents.push_back({G,{}}); }
      for(auto&pp:parents){ Info IP=verify(pp.first,pp.second); if(!IP.ok){fprintf(LOG,"PARENT REVERIFY FAIL %s\n",pp.first.tag.c_str());continue;}
        auto ch=extend(pp.first,pp.second,IP); nchildren+=ch.size();
        for(auto&cc:ch){ vector<int> nb2; Info I2; prove(cc.F,cc.n0,nb2,I2); } }
      if(nl1%50==0){fprintf(LOG,"progress: level-1 entries %lld, children %lld, fam ok %lld fail %lld, direct ok %lld fail %lld, updates %lld\n",nl1,nchildren,ST.fam_ok,ST.fam_fail,ST.direct_ok,ST.direct_fail,ST.updates); fflush(LOG);}
    }
    fprintf(LOG,"LEVEL2 shard %d/%d: level-1 entries %lld, children %lld; families ok=%lld fail=%lld; concrete ok=%lld fail=%lld; slabs=%lld; xval=%lld bad=%lld; updates=%lld\n",shard,nshard,nl1,nchildren,ST.fam_ok,ST.fam_fail,ST.direct_ok,ST.direct_fail,ST.slabs,ST.xval,ST.xval_bad,ST.updates);
    for(auto&w:ST.why)fprintf(LOG,"  fail reason %s: %lld\n",w.first.c_str(),w.second);
    for(auto&w:ST.ntr)fprintf(LOG,"  corridors with %d transits: %lld\n",w.first,w.second);
    return 0;
  }
}
