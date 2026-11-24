"""Training-free test of whether a statement's structure carries retrieval
signal: the recorded IDF baseline, with constants replaced or joined by
depth-bounded patterns of the statement's term graph."""
import numpy as np, scipy.sparse as sp, sys, time, math
T0=time.time()
def log(*a): print('[%6.1fs]'%(time.time()-T0),*a,flush=True)
D='/opt/dlami/nvme/ix-ai/terms/mathlib-full'
DS='/home/sam/repos/ix-ai-pipeline/.truthmines/datasets'
U=np.uint64
def mix(a,b):
    x=(a*U(0x9E3779B97F4A7C15))^(b+U(0xBF58476D1CE4E5B9))
    x^=x>>U(31); x=x*U(0x94D049BB133111EB); x^=x>>U(29)
    return x

# ---- constants
addr2id={}; start=[]; count=[]; owner=[]; troot=[]
for line in open(D+'/consts.tsv'):
    f=line.split('\t'); addr2id[f[1]]=int(f[0]); owner.append(int(f[5])); start.append(int(f[8])); count.append(int(f[9])); troot.append(int(f[10]))
start=np.array(start,dtype=np.int64); count=np.array(count,dtype=np.int64); owner=np.array(owner); troot=np.array(troot,dtype=np.int64)
NC=len(start)
name2addr={}
for line in open(DS+'/mathlib-full/names.tsv'):
    n,a=line.rstrip('\n').split('\t'); name2addr[n]=a
# ---- library
mods=[]; lib_name=[]; lib_mod=[]; lib_decl=[]; lib_consts=[]
for line in open(DS+'/mathlib-full/decls.tsv'):
    if line.startswith('mod\t'):
        f=line.rstrip('\n').split('\t'); mods.append((f[2],[int(x) for x in f[3].split(',') if x] if len(f)>3 else []))
    elif line.startswith('lib\t'):
        f=line.rstrip('\n').split('\t'); lib_name.append(f[1]); lib_mod.append(int(f[2])); lib_decl.append(int(f[3]))
        lib_consts.append([c.rsplit('*',1)[0] for c in f[4].split(',') if c])
NL=len(lib_name); NM=len(mods)
lib_mod=np.array(lib_mod); lib_decl=np.array(lib_decl)
lib_addr=[name2addr.get(n) for n in lib_name]
lib_cid=np.array([addr2id.get(a,-1) if a else -1 for a in lib_addr])
log('library',NL,'modules',NM,'unaddressed',int((lib_cid<0).sum()))
reach=np.zeros((NM,NM),dtype=bool)
for i,(n,imps) in enumerate(mods):
    for j in imps:
        assert j<i
        reach[i]|=reach[j]; reach[i,j]=True
modidx={n:i for i,(n,_) in enumerate(mods)}
# ---- items (module split)
first_lib={}
for j in range(NL):
    first_lib.setdefault(int(lib_cid[j]),j)
tests=[]
for line in open(DS+'/mathlib-full.items.tsv'):
    f=line.rstrip('\n').split('\t')
    if f[0]!='test': continue
    c=addr2id[f[1]]; gold=[addr2id[p] for p in f[3].split(',') if p]
    tests.append((first_lib[c],c,gold))
log('test items',len(tests),'gold',sum(len(g) for _,_,g in tests))


nodes=np.memmap(D+'/nodes.bin',dtype='<u4',mode='r').reshape(-1,4)
# constants of each library statement, from the term graphs
valid=lib_cid>=0
lst=start[lib_cid]; lct=count[lib_cid]
rowrep=np.repeat(np.arange(NL),lct)
nodeidx=np.concatenate([np.arange(s,s+c) for s,c in zip(lst,lct)])
tg=np.array(nodes[:,0],dtype=np.uint8)[nodeidx]; fa=np.array(nodes[:,1])[nodeidx]
m=(tg==2)|(tg==3)
uniq,inv=np.unique(fa[m],return_inverse=True)
M=sp.coo_matrix((np.ones(m.sum(),dtype=np.float32),(rowrep[m],inv)),shape=(NL,uniq.size)).tocsr(); M.data[:]=1
df=np.asarray(M.sum(axis=0)).ravel().astype(np.int64)
idf=np.array([max((NL**4//max(int(x),1)**4).bit_length()-1,0) for x in df],dtype=np.float32)
Pm=M.multiply(idf[None,:]).tocsr(); mass=np.asarray(Pm.sum(axis=1)).ravel().astype(np.int64); PT=Pm.T.tocsr()
log('matrix',M.shape)
# training usage
cid2rows={}
for j in range(NL): cid2rows.setdefault(int(lib_cid[j]),[]).append(j)
train_row=np.zeros(NL,dtype=bool); prem_of={}; use=np.zeros(NL,dtype=np.int64)
for line in open(DS+'/mathlib-full.items.tsv'):
    f=line.rstrip('\n').split('\t')
    if f[0]!='train': continue
    r=first_lib[addr2id[f[1]]]; train_row[r]=True
    ps=[first_lib[addr2id[p]] for p in f[3].split(',') if p and addr2id[p] in first_lib]
    prem_of[r]=np.array(ps,dtype=np.int64)
    for p in ps: use[p]+=1
log('training items',int(train_row.sum()),'premises ever used in training',int((use>0).sum()),'of',NL)
idxN=np.arange(NL,dtype=np.int64)
rankers=['idf','frequency','knn16','knn64','knn64+idf']
cls=['same module','imported, used in training','imported, never used in training']
hit={r:np.zeros(3,dtype=np.int64) for r in rankers}; rr={r:0 for r in rankers}; tot=np.zeros(3,dtype=np.int64)
generic=0; top10oracle=0
rows=np.array([t[0] for t in tests])
for s0 in range(0,len(tests),96):
    chunk=tests[s0:s0+96]
    O=(M[rows[s0:s0+96]]@PT).toarray().astype(np.int64)
    for r,(tl,tc,gold) in enumerate(chunk):
        ov=O[r]; score=(1024*ov)//(mass+1)+ov
        tm=lib_mod[tl]; td=lib_decl[tl]
        cand=(reach[tm][lib_mod]|((lib_mod==tm)&(lib_decl<td)))&(lib_cid!=tc)
        grow=np.array([first_lib[g] for g in gold if g in first_lib],dtype=np.int64)
        gcls=np.where(lib_mod[grow]==tm,0,np.where(use[grow]>0,1,2))
        for c in gcls: tot[c]+=1
        generic+=int((use[grow]>=1000).sum())
        # neighbours among training theorems, by cosine of IDF mass
        sim=np.where(train_row,ov/np.sqrt((mass+1.0)*(mass[tl]+1.0)),0.0)
        order=np.argpartition(-sim,64)[:64]; order=order[np.argsort(-sim[order])]
        v16=np.zeros(NL); v64=np.zeros(NL)
        for k,nb in enumerate(order):
            if sim[nb]<=0: break
            ps=prem_of.get(int(nb))
            if ps is None or ps.size==0: continue
            np.add.at(v64,ps,sim[nb])
            if k<16: np.add.at(v16,ps,sim[nb])
        keys={'idf':score*NL+(NL-1-idxN),
              'frequency':use*NL+(NL-1-idxN),
              'knn16':(v16*1e6).astype(np.int64)*4096+np.minimum(score,4095),
              'knn64':(v64*1e6).astype(np.int64)*4096+np.minimum(score,4095),
              'knn64+idf':(v64*1e6).astype(np.int64)+score*20000}
        for name,key in keys.items():
            key=np.where(cand,key,-1)
            top=np.argpartition(-key,10)[:10]
            top=set(int(j) for j in top if key[j]>=0)
            for g,c in zip(grow,gcls):
                if int(g) in top: hit[name][c]+=1
            gc=grow[cand[grow]]
            if gc.size:
                best=key[gc].max(); rr[name]+=1000000//(int((key>best).sum())+1)
n=len(tests); G=int(tot.sum())
print('gold premises',G,'per theorem %.2f'%(G/n))
for c in range(3): print('  %-34s %6d  %4.1f%%'%(cls[c],tot[c],100*tot[c]/G))
print('  used by >=1000 training theorems   %6d  %4.1f%%'%(generic,100*generic/G))
print('%-12s %8s %8s %8s %8s %7s'%('R@10','all','same-mod','imp-seen','imp-new','MRR'))
for name in rankers:
    h=hit[name]
    print('%-12s %7.1f%% %7.1f%% %7.1f%% %7.1f%% %7.3f'%(name,100*h.sum()/G,100*h[0]/max(tot[0],1),100*h[1]/max(tot[1],1),100*h[2]/max(tot[2],1),rr[name]/n/1e6))
