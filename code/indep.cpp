// Independent stress test of the finite-prefix crossing certificate (Theorem 2).
// Written from the note's statement only; shares no code with the workbench.
//
// Differences from the workbench detector, on purpose:
//  * cut families are half-planes {n.p > c} for 8 normals n (4 axis + 4 diagonal),
//    not 4 coordinate rotations; crossing records carry heading and transverse coord;
//  * generalized ants (any L/R rule string, k colors) are supported;
//  * EVERY guarded match event is recorded (not just the first) and its consequences
//    (no return past cut a, translated periodicity from t_a) are checked on a long horizon;
//  * the first event additionally gets a full half-plane board comparison by re-simulation;
//  * an optional unguarded / off-by-one-guard mode counts false certificates.
#include "standard_headers.hpp"
using namespace std;
typedef long long ll; typedef unsigned long long ull;

static const int DX[4]={0,1,0,-1}, DY[4]={1,0,-1,0}; // 0=N 1=E 2=S 3=W

struct Grid { // sparse open-addressing map from cell -> color (0 = background)
  vector<ull> keys; vector<uint8_t> vals; size_t mask, used=0;
  static ull key(int x,int y){return ((ull)(uint32_t)(x+(1<<30))<<32)|(uint32_t)(y+(1<<30));} // biased: never equals the ~0 sentinel for |x|,|y|<2^30
  Grid(){keys.assign(1<<16,~0ULL);vals.assign(1<<16,0);mask=(1<<16)-1;}
  static size_t h(ull k){k^=k>>33;k*=0xff51afd7ed558ccdULL;k^=k>>33;k*=0xc4ceb9fe1a85ec53ULL;k^=k>>33;return k;}
  size_t slot(ull k){size_t i=h(k)&mask;while(keys[i]!=~0ULL&&keys[i]!=k)i=(i+1)&mask;return i;}
  void grow(){vector<ull> ok=keys;vector<uint8_t> ov=vals;keys.assign(ok.size()*2,~0ULL);vals.assign(ok.size()*2,0);mask=keys.size()-1;
    for(size_t i=0;i<ok.size();++i)if(ok[i]!=~0ULL){size_t j=slot(ok[i]);keys[j]=ok[i];vals[j]=ov[i];}}
  uint8_t get(int x,int y){size_t i=slot(key(x,y));return keys[i]==~0ULL?0:vals[i];}
  uint8_t& ref(int x,int y){ull k=key(x,y);size_t i=slot(k);if(keys[i]==~0ULL){if(2*(used+1)>keys.size()){grow();i=slot(k);}keys[i]=k;vals[i]=0;++used;}return vals[i];}
  template<class F> void each(F f){for(size_t i=0;i<keys.size();++i)if(keys[i]!=~0ULL&&vals[i])f((int)(keys[i]>>32)-(1<<30),(int)(uint32_t)keys[i]-(1<<30),vals[i]);}
};

struct Config { string name; string rule; vector<array<int,3>> cells; int h0; };

struct Rec { int head; ll psi; };
struct CutData { vector<Rec> recs; vector<ll> times; ull hash=0; };
struct Event { int fam; ll a,b,ta,tb; ll vx,vy; };

static const int NX[8]={1,-1,0,0,1,1,-1,-1}, NY[8]={0,0,1,-1,1,-1,1,-1};

struct Family {
  int id,nx,ny; ll guard; bool diag;
  unordered_map<ll,CutData> cuts;
  unordered_map<ull,vector<ll>> active;
  ll phi(ll x,ll y)const{return nx*x+ny*y;}
  ll psi(ll x,ll y)const{return -ny*x+nx*y;}
};
static const ull HB=0x9E3779B97F4A7C15ULL;
static ull enc(int head,ll dpsi){ull z=(ull)(dpsi+(1LL<<40))*0x100000001B3ULL+(ull)head*0xC2B2AE3D27D4EB4FULL;z^=z>>29;return z|1;}
static bool same_shape(const CutData&A,const CutData&B){
  if(A.recs.size()!=B.recs.size())return false;
  for(size_t i=0;i<A.recs.size();++i){
    if(A.recs[i].head!=B.recs[i].head)return false;
    if(A.recs[i].psi-A.recs[0].psi!=B.recs[i].psi-B.recs[0].psi)return false;}
  return true;}

struct Result { bool detected=false; ll first_detect=-1; Event first{}; vector<Event> events; ll horizon=0;
  ll checked_events=0, failed_events=0, short_window=0; bool board_ok=false; int period=0, primitive=0; string word; };

// guard_shift: 0 = correct guard; negative values deliberately weaken it (unsound control).
Result run(const Config&C, ll cap, ll extra_factor_num, ll extra_min, bool all_events, int guard_shift,
           bool diag_families, vector<int>*famcount=nullptr){
  int k=C.rule.size(); vector<int> turn(k); for(int i=0;i<k;++i)turn[i]=C.rule[i]=='R'?1:3;
  Grid g; for(auto&c:C.cells)g.ref(c[0],c[1])=(uint8_t)c[2];
  vector<Family> fam; int nf=diag_families?8:4;
  for(int f=0;f<nf;++f){Family F;F.id=f;F.nx=NX[f];F.ny=NY[f];F.diag=f>=4;
    ll gm=F.phi(0,0); for(auto&c:C.cells)if(c[2])gm=max(gm,F.phi(c[0],c[1]));
    ll p0=F.phi(0,0); F.guard = guard_shift<=-1000000 ? p0 : max(p0, gm+guard_shift); fam.push_back(std::move(F));}
  vector<int> X,Y; vector<uint8_t> H,B; X.reserve(1<<20);
  int x=0,y=0,h=C.h0; Result R; ll horizon=cap;
  for(ll t=0;t<horizon;++t){
    uint8_t &cell=g.ref(x,y); int c=cell; X.push_back(x);Y.push_back(y);H.push_back(h);B.push_back(c);
    cell=(uint8_t)((c+1)%k); h=(h+turn[c])&3; int nx=x+DX[h], ny=y+DY[h];
    for(auto&F:fam){
      ll p0=F.phi(x,y),p1=F.phi(nx,ny); if(p0==p1)continue; ll cut=min(p0,p1); if(cut<F.guard)continue;
      CutData&D=F.cuts[cut]; bool wasodd=D.recs.size()%2;
      if(wasodd){auto it=F.active.find(D.hash);auto&v=it->second;v.erase(find(v.begin(),v.end(),cut));if(v.empty())F.active.erase(it);}
      bool fwd=p1>p0; if(fwd!=(D.recs.size()%2==0)){fprintf(stderr,"alternation violated\n");exit(3);}
      ll ps=F.psi(nx,ny); ll d0=D.recs.empty()?0:ps-D.recs[0].psi;
      D.recs.push_back({h,ps}); D.times.push_back(t+1); D.hash=D.hash*HB+enc(h,d0);
      if(D.recs.size()%2==0)continue;
      auto &bucket=F.active[D.hash];
      ll best_hi=LLONG_MIN, best_lo=LLONG_MAX;
      for(ll o:bucket){ if(!same_shape(D,F.cuts[o]))continue; best_hi=max(best_hi,o); best_lo=min(best_lo,o);}
      for(ll o:{best_hi,best_lo}){ if(o==LLONG_MIN||o==LLONG_MAX)continue;
        ll a=min(o,cut),b=max(o,cut); if(b!=cut){fprintf(stderr,"new cut not outer\n");exit(4);}
        CutData&A=F.cuts[a],&Bc=F.cuts[b];
        Event e{F.id,a,b,A.times.back(),Bc.times.back(),0,0};
        // displacement from last forward-crossing destinations
        e.vx=(ll)nx-X[e.ta]; e.vy=(ll)ny-Y[e.ta];
        if(e.tb!=t+1){fprintf(stderr,"tb mismatch\n");exit(5);}
        if(!R.detected){R.detected=true;R.first_detect=t+1;R.first=e;
          if(famcount)(*famcount)[F.id]++;
          horizon=min(cap, max(t+1+extra_min, (t+1)*extra_factor_num));}
        if(all_events)R.events.push_back(e); else if(R.events.empty())R.events.push_back(e);
        if(best_hi==best_lo)break;
      }
      bucket.push_back(cut);
    }
    x=nx;y=ny;
  }
  R.horizon=horizon; ll T=X.size();
  // Check consequences of every recorded event on the stored horizon.
  map<int,vector<ll>> sufmin; map<array<ll,3>,ll> lastbad;
  for(auto&e:R.events){
    Family&F=fam[e.fam]; ll P=e.tb-e.ta; bool ok=P>0;
    if(F.phi(e.vx,e.vy)!=e.b-e.a)ok=false;                 // displacement crosses b-a cuts
    auto it=sufmin.find(e.fam);
    if(it==sufmin.end()){vector<ll> s(T+1); s[T]=F.phi(x,y); for(ll u=T-1;u>=0;--u)s[u]=min(s[u+1],F.phi(X[u],Y[u])); it=sufmin.emplace(e.fam,std::move(s)).first;}
    if(it->second[e.ta]<=e.a)ok=false;                      // never returns past cut a, through the horizon
    array<ll,3> key{P,e.vx,e.vy}; auto jt=lastbad.find(key);
    if(jt==lastbad.end()){ll L=-1; for(ll u=T-1-P;u>=0;--u) if(X[u+P]!=X[u]+e.vx||Y[u+P]!=Y[u]+e.vy||H[u+P]!=H[u]||B[u+P]!=B[u]){L=u;break;}
      jt=lastbad.emplace(key,L).first;}
    if(jt->second>=e.ta)ok=false;                           // translated periodicity from t_a to the horizon
    if(T-e.tb<P)R.short_window++;                           // fewer than one extra period verified (reported, not a failure)
    R.checked_events++; if(!ok)R.failed_events++;
  }
  if(R.detected){
    // Full half-plane board comparison for the first event, by an independent re-simulation.
    Event e=R.first; Family&F=fam[e.fam];
    Grid g2; for(auto&c:C.cells)g2.ref(c[0],c[1])=(uint8_t)c[2];
    int x2=0,y2=0,h2=C.h0; vector<array<ll,3>> SA,SB; int ha=-1,hb=-1; ll pax=0,pay=0,pbx=0,pby=0;
    for(ll t=0;t<=e.tb;++t){
      if(t==e.ta){g2.each([&](int px,int py,int col){if(F.phi(px,py)>e.a)SA.push_back({px,py,col});});ha=h2;pax=x2;pay=y2;}
      if(t==e.tb){g2.each([&](int px,int py,int col){if(F.phi(px,py)>e.b)SB.push_back({px-e.vx,py-e.vy,col});});hb=h2;pbx=x2;pby=y2;break;}
      uint8_t&cell=g2.ref(x2,y2);int c=cell;cell=(uint8_t)((c+1)%k);h2=(h2+turn[c])&3;x2+=DX[h2];y2+=DY[h2];
    }
    sort(SA.begin(),SA.end());sort(SB.begin(),SB.end());
    R.board_ok = SA==SB && ha==hb && pbx-pax==e.vx && pby-pay==e.vy;
    R.period=e.tb-e.ta; string w; for(ll u=e.ta;u<e.tb;++u)w+=char('0'+B[u]); R.word=w;
    for(int p=1;p<=R.period;++p) if(R.period%p==0){bool ok=true;for(int i=0;i<R.period&&ok;++i)if(w[i]!=w[i%p])ok=false; if(ok){R.primitive=p;break;}}
  }
  return R;
}

static string canon(const string&w){ // least cyclic rotation
  string best=w; for(size_t i=1;i<w.size();++i){string r=w.substr(i)+w.substr(0,i); if(r<best)best=r;} return best;}

int main(int argc,char**argv){
  string mode=argc>1?argv[1]:"main";
  if(mode=="detail"){
    string rule=argv[2]; int N=atoi(argv[3]); mt19937_64 rng(99);
    // replay the exact RNG sequence used by mode general for this rule
    vector<pair<string,int>> rules={{"LLLR",0},{"LLRRRL",0},{"LLRLRLL",0},{"RRLLLRLLLRRR",0},{"LRRRRRLLR",0},{"RLR",0},{"LLRR",0}};
    for(auto&rr:rules){int NN=rr.first.size()>=9?40:200;
      for(int rep=0;rep<NN;++rep){Config c;c.rule=rr.first;c.h0=rng()%4;int s=rep==0?0:1+rng()%6;
        for(int xx=0;xx<s;++xx)for(int yy=0;yy<s;++yy)if(rng()%2)c.cells.push_back({xx-s/2,yy-s/2,(int)(1+rng()%(c.rule.size()-1))});
        if(rr.first!=rule)continue;
        Result r=run(c,1000000,2,40000,false,0,true); if(!r.detected)continue;
        Result r2=run(c,(ll)N,1000000,0,false,0,true);
        printf("rep=%d h0=%d cells=%zu period=%d prim=%d v=(%lld,%lld) fam=%d ta=%lld | long run: horizon=%lld events=%lld failed=%lld board_ok=%d\n  cells:",rep,c.h0,c.cells.size(),r.period,r.primitive,r.first.vx,r.first.vy,r.first.fam,r.first.ta,r2.horizon,r2.checked_events,r2.failed_events,(int)r2.board_ok);
        for(auto&q:c.cells)printf(" (%d,%d,%d)",q[0],q[1],q[2]); printf("\n");}}
    return 0;
  }
  if(mode=="file"){
    Config blank;blank.rule="RL";blank.h0=0;blank.name="blank"; Result rb=run(blank,2000000,1,1,false,0,true); string cw=canon(rb.word);
    FILE*f=fopen(argv[2],"r"); int n; ll cnt=0,bad=0,steps=0;
    while(fscanf(f,"%d",&n)==1){Config c;c.rule="RL";c.h0=0; for(int i=0;i<n;++i){int x,y;if(fscanf(f,"%d %d",&x,&y)!=2)return 9;c.cells.push_back({x,y,1});}
      Result r=run(c,6000000,1,1,false,0,true); cnt++; steps+=r.horizon;
      if(!r.detected||!r.board_ok||canon(r.word)!=cw){bad++; printf("MISMATCH config %lld detected=%d board=%d\n",cnt,(int)r.detected,(int)r.board_ok);} }
    printf("independent detector: %lld configs, %lld simulated updates, %lld mismatches (all must be standard 104-highway)\n",cnt,steps,bad); return 0; }
  if(mode=="sanity"){
    vector<Config> cs; Config b;b.rule="RL";b.h0=0;b.name="blank";cs.push_back(b);
    Config f=b;f.name="3x3 full";for(int xx=-1;xx<=1;++xx)for(int yy=-1;yy<=1;++yy)f.cells.push_back({xx,yy,1});cs.push_back(f);
    Config L=b;L.name="three-cell";L.cells={{-235,-212,1},{-234,-212,1},{-235,-211,1}};cs.push_back(L);
    Config S=b;S.name="seven-cell";S.cells={{-235,-212,1},{-234,-212,1},{-635,-612,1},{-634,-612,1},{-634,-611,1},{-1034,-1012,1},{-1034,-1011,1}};cs.push_back(S);
    for(auto&c:cs)for(bool dg:{false,true}){Result r=run(c,3000000,2,60000,true,0,dg);
      printf("%-11s %s fam=%d cuts=%lld,%lld ta=%lld tb=%lld v=(%lld,%lld) period=%d prim=%d board_ok=%d events=%lld failed=%lld short=%lld horizon=%lld\n",
        c.name.c_str(),dg?"8fam":"axis",r.first.fam,r.first.a,r.first.b,r.first.ta,r.first.tb,r.first.vx,r.first.vy,r.period,r.primitive,(int)r.board_ok,r.checked_events,r.failed_events,r.short_window,r.horizon);}
    return 0;
  }
  if(mode=="main"||mode=="langton"){
    // Langton RL. Families of starts, none taken from the workbench's 13x13 seeds.
    vector<Config> cs; mt19937_64 rng(20261004);
    for(int hd=0;hd<4;++hd) for(int m=0;m<512;++m){Config c;c.rule="RL";c.h0=hd;c.name="3x3/h"+to_string(hd)+"/"+to_string(m);
      int j=0; for(int xx=-1;xx<=1;++xx)for(int yy=-1;yy<=1;++yy,++j) if(m>>j&1)c.cells.push_back({xx,yy,1}); cs.push_back(c);}
    int sizes[]={4,5,6,8,10,16,24,32};
    for(int s:sizes) for(int rep=0;rep<(s<=8?600:(s<=16?200:60));++rep){
      Config c;c.rule="RL";c.h0=rng()%4; double dens=0.05+0.9*((rng()%1000)/1000.0);
      c.name="rand"+to_string(s)+"/"+to_string(rep);
      int ox=(int)(rng()%41)-20, oy=(int)(rng()%41)-20; // box not necessarily containing the ant
      for(int xx=0;xx<s;++xx)for(int yy=0;yy<s;++yy) if((rng()%1000)/1000.0<dens) c.cells.push_back({ox+xx-s/2,oy+yy-s/2,1});
      cs.push_back(c);}
    // sparse far-flung obstacles (exercise the guard)
    for(int rep=0;rep<300;++rep){Config c;c.rule="RL";c.h0=rng()%4;c.name="sparse/"+to_string(rep);
      int n=1+rng()%6; for(int i=0;i<n;++i){int R=50+rng()%400; c.cells.push_back({(int)(rng()%(2*R+1))-R,(int)(rng()%(2*R+1))-R,1});}
      cs.push_back(c);}
    // canonical word from blank
    Config blank;blank.rule="RL";blank.h0=0;blank.name="blank";
    Result rb=run(blank,2000000,2,50000,false,0,true); string cw=canon(rb.word);
    ll shortw=0; ll steps=0, ev=0, bad=0, nodetect=0, boardbad=0, nonstd=0; map<int,int> per; vector<int> famc(8,0);
    ll diag_earlier=0; ll maxdet=0; string maxname;
    for(auto&c:cs){
      Result r=run(c,3000000,2,60000,true,0,true,&famc);
      steps+=r.horizon; ev+=r.checked_events; bad+=r.failed_events; shortw+=r.short_window;
      if(!r.detected){nodetect++; printf("NO DETECTION %s\n",c.name.c_str()); continue;}
      if(!r.board_ok)boardbad++; per[r.primitive]++; if(canon(r.word)!=cw)nonstd++;
      if(r.first_detect>maxdet){maxdet=r.first_detect;maxname=c.name;}
    }
    // axis-only detection on the same starts, to compare onset of diagonal vs axis certificates
    ll sum_axis=0,sum_all=0; int cnt=0;
    for(size_t i=0;i<cs.size();i+=7){Result ra=run(cs[i],3000000,1,1,false,0,false); Result rd=run(cs[i],3000000,1,1,false,0,true);
      if(ra.detected&&rd.detected){sum_axis+=ra.first_detect;sum_all+=rd.first_detect;cnt++; if(rd.first_detect<ra.first_detect)diag_earlier++;}}
    printf("{\"starts\":%zu,\"simulated_updates\":%lld,\"no_detection\":%lld,\"events_checked\":%lld,\"events_failed\":%lld,"
           "\"short_window_events\":%lld,\"first_event_board_failures\":%lld,\"nonstandard_words\":%lld,\"max_first_detection\":%lld,\"max_case\":\"%s\"}\n",
           cs.size(),steps,nodetect,ev,bad,shortw,boardbad,nonstd,maxdet,maxname.c_str());
    printf("primitive periods:"); for(auto&p:per)printf(" %d:%d",p.first,p.second); printf("\n");
    printf("first-certificate family counts (x+,x-,y+,y-,d++,d+-,d-+,d--):"); for(int v:famc)printf(" %d",v); printf("\n");
    printf("axis-only vs all-8 mean first detection over %d starts: %.1f vs %.1f; diagonal strictly earlier in %lld\n",
           cnt,(double)sum_axis/cnt,(double)sum_all/cnt,diag_earlier);
    printf("blank: first detection %lld, period %d, family %d, cuts %lld,%lld, entry %lld\n",rb.first_detect,rb.period,rb.first.fam,rb.first.a,rb.first.b,rb.first.ta);
  }
  if(mode=="unguarded"){
    // Negative control at scale: weaken the guard and count false certificates.
    mt19937_64 rng(77); for(int shift:{-1,-3,-1000000}){
      ll total=0,fails=0,cases=0;
      for(int rep=0;rep<300;++rep){Config c;c.rule="RL";c.h0=rng()%4;
        int n=1+rng()%5; for(int i=0;i<n;++i){int R=20+rng()%300; c.cells.push_back({(int)(rng()%(2*R+1))-R,(int)(rng()%(2*R+1))-R,1});}
        Result r=run(c,1500000,3,100000,true,shift,true); total+=r.checked_events; fails+=r.failed_events; cases++;}
      printf("guard shift %d: %lld starts, %lld events checked, %lld FALSE certificates\n",shift,cases,total,fails);
    }
  }
  if(mode=="general"){
    // Theorem 2's proof never uses Langton-specific facts. Try generalized ants.
    vector<pair<string,int>> rules={{"LLLR",0},{"LLRRRL",0},{"LLRLRLL",0},{"RRLLLRLLLRRR",0},{"LRRRRRLLR",0},{"RLR",0},{"LLRR",0}};
    mt19937_64 rng(99);
    for(auto&rr:rules){ map<pair<int,pair<ll,ll>>,int> kinds; ll ev=0,bad=0,nod=0,boardbad=0; int N=rr.first.size()>=9?40:200;
      for(int rep=0;rep<N;++rep){Config c;c.rule=rr.first;c.h0=rng()%4;int s=rep==0?0:1+rng()%6;
        for(int xx=0;xx<s;++xx)for(int yy=0;yy<s;++yy)if(rng()%2)c.cells.push_back({xx-s/2,yy-s/2,(int)(1+rng()%(c.rule.size()-1))});
        Result r=run(c,1000000,2,40000,true,0,true); ev+=r.checked_events; bad+=r.failed_events;
        if(!r.detected){nod++;continue;} if(!r.board_ok)boardbad++;
        ll D=llabs(r.first.vx),E=llabs(r.first.vy); kinds[{r.primitive,{max(D,E),min(D,E)}}]++;}
      printf("%-13s starts=%d no_detect(<=1e6)=%lld events=%lld failed=%lld board_fail=%lld kinds(period,|drift|):",rr.first.c_str(),N,nod,ev,bad,boardbad);
      for(auto&kk:kinds)printf(" [%d,(%lld,%lld)]x%d",kk.first.first,kk.first.second.first,kk.first.second.second,kk.second); printf("\n");
    }
  }
  return 0;
}
