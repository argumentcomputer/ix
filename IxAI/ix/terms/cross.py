"""Held-out-library test of the training-free rankers. Usage statistics come
from the Mathlib environment only; queries are the theorems a second library
adds. Everything is read from the term dumps: labels are the theorems a proof
term refers to, and a library's own theorem is a candidate when its dependency
depth inside the library is below the query's."""
import numpy as np, scipy.sparse as sp, sys, time, random, collections
T0=time.time()
def log(*a): print('[%6.1fs]'%(time.time()-T0),*a,flush=True)
R='/opt/dlami/nvme/ix-ai/terms/'
LIB=sys.argv[1]; NTEST=int(sys.argv[2]) if len(sys.argv)>2 else 2000
def load(s):
    addr=[];kind=[]
    for line in open(R+s+'/consts.tsv'):
        f=line.split('\t',3); addr.append(f[1]); kind.append(f[2])
    def refs(name):
        d={}
        for line in open(R+s+'/'+name):
            a,b=line.rstrip('\n').split('\t'); d[int(a)]=[int(x) for x in b.split()] if b else []
        return d
    return addr,kind,refs('trefs.tsv'),refs('vrefs.tsv')
maddr,mkind,mt,mv=load('mathlib-d13f23b'); NM=len(maddr)
AM={a:i for i,a in enumerate(maddr)}
saddr,skind,st,sv=load(LIB)
pid=[]; newc=[]
for i,a in enumerate(saddr):
    j=AM.get(a)
    if j is None: j=NM+len(newc); newc.append(i)
    pid.append(j)
NP=NM+len(newc)
kind=mkind+[skind[i] for i in newc]
tref=[mt.get(i,[]) for i in range(NM)]+[[pid[r] for r in st.get(i,[])] for i in newc]
vref=[mv.get(i,[]) for i in range(NM)]+[[pid[r] for r in sv.get(i,[])] for i in newc]
# dependency depth among the library's own constants
depth=np.zeros(NP,dtype=np.int64)
state=np.zeros(NP,dtype=np.int8)
for c0 in range(NM,NP):
    if state[c0]: continue
    stack=[(c0,0)]; state[c0]=1
    while stack:
        c,k=stack[-1]
        rs=[r for r in tref[c]+vref[c] if r>=NM]
        if k<len(rs):
            stack[-1]=(c,k+1); r=rs[k]
            if state[r]==0: state[r]=1; stack.append((r,0))
        else:
            depth[c]=1+max([depth[r] for r in rs if state[r]==2],default=0); state[c]=2; stack.pop()
thm=np.array([k=='thm' for k in kind])
rows=np.nonzero(thm)[0]; NR=rows.size; row_of=np.full(NP,-1,dtype=np.int64); row_of[rows]=np.arange(NR)
NMR=int(thm[:NM].sum())
log(LIB,'pooled constants',NP,'theorems',NR,'of which new',NR-NMR)
ri=[];ci=[]
for r,c in enumerate(rows):
    for x in tref[c]: ri.append(r); ci.append(x)
M=sp.coo_matrix((np.ones(len(ri),dtype=np.float32),(ri,ci)),shape=(NR,NP)).tocsr(); M.data[:]=1
df=np.asarray(M.sum(axis=0)).ravel().astype(np.int64)
idf=np.array([max((NR**4//max(int(x),1)**4).bit_length()-1,0) for x in df],dtype=np.float32)
Pm=M.multiply(idf[None,:]).tocsr(); mass=np.asarray(Pm.sum(axis=1)).ravel().astype(np.int64); PT=Pm.T.tocsr()
prem=[np.array(sorted(set(int(row_of[x]) for x in vref[c] if thm[x] and x!=c)),dtype=np.int64) for c in rows]
use=np.zeros(NR,dtype=np.int64)
for r in range(NMR):
    use[prem[r]]+=1
rdepth=depth[rows]; isnew=np.arange(NR)>=NMR
tests=[r for r in range(NMR,NR) if prem[r].size]
random.seed(7); random.shuffle(tests); tests=sorted(tests[:NTEST])
log('test theorems',len(tests),'mean premises %.1f'%np.mean([prem[r].size for r in tests]))
names=['idf','frequency','knn frozen','knn online']
cls=['own library','Mathlib, used there','Mathlib, unused there']
hit={n:np.zeros(3,dtype=np.int64) for n in names}; rr={n:0 for n in names}; tot=np.zeros(3,dtype=np.int64); ncand=0
idx=np.arange(NR,dtype=np.int64)
def votes(sim):
    order=np.argpartition(-sim,64)[:64]; order=order[np.argsort(-sim[order])]
    v=np.zeros(NR)
    for nb in order:
        if sim[nb]<=0: break
        if prem[nb].size: np.add.at(v,prem[nb],sim[nb])
    return v
for s0 in range(0,len(tests),64):
    chunk=tests[s0:s0+64]
    O=(M[chunk]@PT).toarray().astype(np.int64)
    for k,t in enumerate(chunk):
        ov=O[k]; score=(1024*ov)//(mass+1)+ov
        cand=(~isnew)|(rdepth<rdepth[t]); cand[t]=False
        ncand+=int(cand.sum())
        g=prem[t]; gc=np.where(g>=NMR,0,np.where(use[g]>0,1,2))
        for c in gc: tot[c]+=1
        sim=ov/np.sqrt((mass+1.0)*(mass[t]+1.0))
        vf=votes(np.where(isnew,0.0,sim)); vo=votes(np.where(cand,sim,0.0))
        keys={'idf':score*NR+(NR-1-idx),'frequency':use*NR+(NR-1-idx),
              'knn frozen':(vf*1e6).astype(np.int64)*4096+np.minimum(score,4095),
              'knn online':(vo*1e6).astype(np.int64)*4096+np.minimum(score,4095)}
        for n,key in keys.items():
            key=np.where(cand,key,-1)
            top=set(int(j) for j in np.argpartition(-key,10)[:10] if key[j]>=0)
            for x,c in zip(g,gc):
                if int(x) in top: hit[n][c]+=1
            gg=g[cand[g]]
            if gg.size: rr[n]+=1000000//(int((key>key[gg].max()).sum())+1)
G=int(tot.sum()); n=len(tests)
print('== %s: %d queries, %d candidates on average, gold: %s'%(LIB,n,ncand//n,', '.join('%s %.1f%%'%(cls[c],100*tot[c]/G) for c in range(3))))
print('%-12s %7s %12s %12s %12s %7s'%('R@10','all','own','Mathlib used','unused','MRR'))
for nm in names:
    h=hit[nm]
    print('%-12s %6.1f%% %11.1f%% %11.1f%% %11.1f%% %7.3f'%(nm,100*h.sum()/G,100*h[0]/max(tot[0],1),100*h[1]/max(tot[1],1),100*h[2]/max(tot[2],1),rr[nm]/n/1e6))
