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

# ---- term graphs
nodes=np.memmap(D+'/nodes.bin',dtype='<u4',mode='r').reshape(-1,4)
N=nodes.shape[0]
tag=np.array(nodes[:,0],dtype=np.uint8); fa=np.array(nodes[:,1]); fb=np.array(nodes[:,2]); fc=np.array(nodes[:,3])
own=np.nonzero(count>0)[0]
base=np.repeat(start[own],count[own])
assert base.shape[0]==N
A=base+fa; B=base+fb; C=base+fc
isapp=tag==7; isbind=(tag==8)|(tag==9); islet=tag==10; isprj=tag==4
leaf=~(isapp|isbind|islet|isprj)
WILD=U(0x1234567887654321)
tok=np.zeros(N,dtype=U)
m=tag==2; tok[m]=mix(np.full(m.sum(),2,dtype=U),fa[m].astype(U))
m=tag==3; tok[m]=mix(np.full(m.sum(),3,dtype=U),fa[m].astype(U))
m=tag==1; tok[m]=U(0x1111)
m=tag==0; tok[m]=mix(np.full(m.sum(),10,dtype=U),np.minimum(fa[m],2).astype(U))
m=tag==6; tok[m]=mix(np.full(m.sum(),6,dtype=U),np.minimum(fa[m],16).astype(U))
m=tag==5; tok[m]=U(0x5555)
# spine position of every application
ai=np.nonzero(isapp)[0]
sl=np.zeros(N,dtype=np.uint8)
f_of=A[ai]
first=~isapp[f_of]
sl[ai[first]]=1
rest=ai[~first]; levels=[ai[first]]
L=1
while rest.size and L<64:
    L+=1
    ok=sl[A[rest]]==L-1
    sl[rest[ok]]=L; levels.append(rest[ok]); rest=rest[~ok]
log('applications',ai.size,'longest spine',L,'left over',rest.size)
# nodes used as a whole term: an argument, a binder part, or a root
whole=np.zeros(N,dtype=bool)
whole[B[ai]]=True
for msk,cols in ((isbind,(A,B)),(islet,(A,B,C)),(isprj,(C,))):
    idx=np.nonzero(msk)[0]
    for col in cols: whole[col[idx]]=True
roots=np.nonzero(troot>=0)[0]
whole[start[owner[roots]]+troot[roots]]=True
featnode=(isapp&whole)|isbind|islet|isprj
log('feature nodes',int(featnode.sum()))

def patterns(DMAX):
    out=[]
    prev=np.full(N,WILD,dtype=U)
    for d in range(1,DMAX+1):
        cur=np.full(N,WILD,dtype=U)
        cur[leaf]=tok[leaf]
        S=np.zeros(N,dtype=U)
        l1=levels[0]; h=A[l1]
        head=np.where(leaf[h],tok[h],prev[h])
        S[l1]=mix(mix(np.full(l1.size,7,dtype=U),head),prev[B[l1]])
        for lv in levels[1:]:
            S[lv]=mix(S[A[lv]],prev[B[lv]])
        cur[ai]=mix(S[ai],U(0x77))
        idx=np.nonzero(isbind)[0]
        cur[idx]=mix(mix(tag[idx].astype(U),prev[A[idx]]),prev[B[idx]])
        idx=np.nonzero(islet)[0]
        cur[idx]=mix(mix(mix(np.full(idx.size,10,dtype=U),prev[A[idx]]),prev[B[idx]]),prev[C[idx]])
        idx=np.nonzero(isprj)[0]
        cur[idx]=mix(mix(mix(np.full(idx.size,4,dtype=U),fa[idx].astype(U)),fb[idx].astype(U)),prev[C[idx]])
        out.append(cur); prev=cur
        log('patterns depth',d)
    return out
DMAX=int(sys.argv[1]) if len(sys.argv)>1 else 3
P=patterns(DMAX)

# ---- feature matrices over library theorems
valid=lib_cid>=0
lst=start[np.where(valid,lib_cid,0)]; lct=np.where(valid,count[np.where(valid,lib_cid,0)],0)
rowrep=np.repeat(np.arange(NL),lct)
nodeidx=np.concatenate([np.arange(s,s+c) for s,c in zip(lst,lct) if c]) if NL else None
log('library statement nodes',nodeidx.size)
def matrix(hashes_rows):
    """rows, hashes -> binary CSR over distinct hashes"""
    rows=np.concatenate([r for r,_ in hashes_rows]); hs=np.concatenate([h for _,h in hashes_rows])
    uniq,inv=np.unique(hs,return_inverse=True)
    M=sp.coo_matrix((np.ones(rows.size,dtype=np.float32),(rows,inv)),shape=(NL,uniq.size)).tocsr()
    M.data[:]=1
    return M
def const_feats_ixon():
    m=(tag[nodeidx]==2)|(tag[nodeidx]==3)
    return (rowrep[m],tok[nodeidx[m]])
def const_feats_lean():
    ids={}; rows=[]; hs=[]
    for j,cs in enumerate(lib_consts):
        for c in cs:
            a=name2addr.get(c); k=addr2id.get(a,None) if a else None
            if k is None: k=ids.setdefault(c,NC+len(ids))
            rows.append(j); hs.append(k)
    return (np.array(rows),mix(np.full(len(hs),2,dtype=U),np.array(hs,dtype=U)))
def pat_feats(d):
    m=featnode[nodeidx]
    return (rowrep[m],mix(P[d-1][nodeidx[m]],U(1000+d)))


def build(feats):
    M=matrix(feats)
    df=np.asarray(M.sum(axis=0)).ravel().astype(np.int64)
    idf=np.array([max((NL**4//max(int(x),1)**4).bit_length()-1,0) for x in df],dtype=np.float32)
    Pm=M.multiply(idf[None,:]).tocsr()
    return M,np.asarray(Pm.sum(axis=1)).ravel().astype(np.int64),Pm.T.tocsr()
ci=const_feats_ixon()
Mc,massc,PTc=build([ci])
Mp,massp,PTp=build([ci,pat_feats(1),pat_feats(2)])
log('matrices',Mc.shape,Mp.shape)
train_row=np.zeros(NL,dtype=bool); prem_of={}; use=np.zeros(NL,dtype=np.int64)
for line in open(DS+'/mathlib-full.items.tsv'):
    f=line.rstrip('\n').split('\t')
    if f[0]!='train': continue
    r=first_lib[addr2id[f[1]]]; train_row[r]=True
    ps=[first_lib[addr2id[p]] for p in f[3].split(',') if p and addr2id[p] in first_lib]
    prem_of[r]=np.array(ps,dtype=np.int64)
    for p in ps: use[p]+=1
idxN=np.arange(NL,dtype=np.int64)
names=['idf consts','idf patterns','knn consts','knn patterns','rrf knn+idf consts','rrf knn+idf patterns','rrf knn consts+idf patterns']
hit={r:np.zeros(3,dtype=np.int64) for r in names}; h1={r:0 for r in names}; h5={r:0 for r in names}; rr={r:0 for r in names}; tot=np.zeros(3,dtype=np.int64)
def votes(ov,mass,tl):
    sim=np.where(train_row,ov/np.sqrt((mass+1.0)*(mass[tl]+1.0)),0.0)
    order=np.argpartition(-sim,64)[:64]; order=order[np.argsort(-sim[order])]
    v=np.zeros(NL)
    for nb in order:
        if sim[nb]<=0: break
        ps=prem_of.get(int(nb))
        if ps is not None and ps.size: np.add.at(v,ps,sim[nb])
    return v
def ranks(key):
    o=np.argsort(-key,kind='stable'); r=np.empty(NL,dtype=np.int64); r[o]=np.arange(NL); return r
rows=np.array([t[0] for t in tests])
for s0 in range(0,len(tests),96):
    chunk=tests[s0:s0+96]
    Oc=(Mc[rows[s0:s0+96]]@PTc).toarray().astype(np.int64)
    Op=(Mp[rows[s0:s0+96]]@PTp).toarray().astype(np.int64)
    for r,(tl,tc,gold) in enumerate(chunk):
        tm=lib_mod[tl]; td=lib_decl[tl]
        cand=(reach[tm][lib_mod]|((lib_mod==tm)&(lib_decl<td)))&(lib_cid!=tc)
        grow=np.array([first_lib[g] for g in gold if g in first_lib],dtype=np.int64)
        gcls=np.where(lib_mod[grow]==tm,0,np.where(use[grow]>0,1,2))
        for c in gcls: tot[c]+=1
        sc=(1024*Oc[r])//(massc+1)+Oc[r]; sp_=(1024*Op[r])//(massp+1)+Op[r]
        vc=votes(Oc[r],massc,tl); vp=votes(Op[r],massp,tl)
        k={'idf consts':sc*NL+(NL-1-idxN),'idf patterns':sp_*NL+(NL-1-idxN),
           'knn consts':(vc*1e6).astype(np.int64)*4096+np.minimum(sc,4095),
           'knn patterns':(vp*1e6).astype(np.int64)*4096+np.minimum(sp_,4095)}
        k={a:np.where(cand,b,-1) for a,b in k.items()}
        rk={a:ranks(b) for a,b in k.items()}
        def rrf(a,b): return np.where(cand,(1e9/(60+rk[a])+1e9/(60+rk[b])).astype(np.int64),-1)
        k['rrf knn+idf consts']=rrf('knn consts','idf consts')
        k['rrf knn+idf patterns']=rrf('knn patterns','idf patterns')
        k['rrf knn consts+idf patterns']=rrf('knn consts','idf patterns')
        gc=grow[cand[grow]]
        for name in names:
            key=k[name]
            top=np.argpartition(-key,10)[:10]; top=top[np.argsort(-key[top],kind='stable')]
            top=[int(j) for j in top if key[j]>=0]
            t10=set(top); t5=set(top[:5]); t1=set(top[:1])
            for g,c in zip(grow,gcls):
                g=int(g)
                if g in t10: hit[name][c]+=1
                if g in t5: h5[name]+=1
                if g in t1: h1[name]+=1
            if gc.size:
                best=key[gc].max(); rr[name]+=1000000//(int((key>best).sum())+1)
    if s0%960==0: log('items',s0)
n=len(tests); G=int(tot.sum())
print('%-30s %6s %6s %6s | %8s %8s %8s | %6s'%('ranker','R@1','R@5','R@10','same-mod','imp-seen','imp-new','MRR'))
for name in names:
    h=hit[name]
    print('%-30s %5.1f%% %5.1f%% %5.1f%% | %7.1f%% %7.1f%% %7.1f%% | %6.3f'%(name,100*h1[name]/G,100*h5[name]/G,100*h.sum()/G,100*h[0]/max(tot[0],1),100*h[1]/max(tot[1],1),100*h[2]/max(tot[2],1),rr[name]/n/1e6))
