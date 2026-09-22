import re, struct, math, statistics as st
import numpy as np
PROF="/home/sam/benchdata/flt/anthropic-flt.ixprof"; IXES="/home/sam/benchdata/flt/anthropic-flt-572.ixes"
ERR="/home/sam/benchdata/flt/runs/flt572-lanes4-exec3/lanes.err"; ERR256="/home/sam/benchdata/flt/runs/flt572-lanes4-exec3/lanes-resume256.err"
b=open(PROF,"rb").read(); n=struct.unpack_from("<I",b,12)[0]; p=16; prof={}
for _ in range(n):
    a=b[p:p+32].hex(); prof[a]=struct.unpack_from("<QIIQQQQQ",b,p+32); p+=88
m=open(IXES,"rb").read(); q=8+16; nl=struct.unpack_from("<I",m,q)[0]; q+=4; leaves=[]
for i in range(nl):
    q+=4; hb,own,cross=struct.unpack_from("<QQQ",m,q); q+=24; tag=m[q]; q+=1+(32 if tag==1 else 0)
    blen=struct.unpack_from("<I",m,q)[0]; q+=4; bl=[m[q+32*k:q+32*k+32].hex() for k in range(blen)]; q+=32*blen
    flen=struct.unpack_from("<I",m,q)[0]; q+=4+32*flen; leaves.append((bl,own,cross))
rec={}
for path in (ERR,ERR256):
    for line in open(path,errors="replace"):
        mm=re.search(r"claim (\d+) executed in [\d.]+s, record (\d+) B",line)
        if mm and int(mm.group(1))<572: rec[int(mm.group(1))]=int(mm.group(2))/2**30
names=["bytes","frontier","blocks","bytes^1.5","heartbeats","subst","whnf","def_eq","nat_arith","intern"]
X=[];y=[]
for i,(bl,own,cross) in enumerate(leaves):
    if i not in rec: continue
    P=[prof[a] for a in bl if a in prof]
    X.append([sum(x[1] for x in P), cross, len(bl), sum(x[1]**1.5 for x in P), sum(x[0] for x in P), sum(x[3] for x in P), sum(x[4] for x in P), sum(x[5] for x in P), sum(x[6] for x in P), sum(x[7] for x in P)]); y.append(rec[i])
X=np.array(X,float); y=np.array(y); ids=[i for i in range(nl) if i in rec]
def fit(cols, nonneg=False):
    A=X[:,cols]
    if nonneg:
        from itertools import count
        # simple projected least squares: iterate dropping negative coefficients
        keep=list(range(len(cols)))
        while True:
            c,*_=np.linalg.lstsq(A[:,keep],y,rcond=None)
            if (c>=0).all() or len(keep)==1: break
            keep=[k for k,ci in zip(keep,c) if ci>0]
        coef=np.zeros(len(cols)); coef[keep]=c; return coef
    c,*_=np.linalg.lstsq(A,y,rcond=None); return c
def loo(cols, nonneg=False):
    preds=np.zeros(len(y))
    for k in range(len(y)):
        mask=np.arange(len(y))!=k; A=X[mask][:,cols]
        if nonneg:
            keep=list(range(len(cols)))
            while True:
                c,*_=np.linalg.lstsq(A[:,keep],y[mask],rcond=None)
                if (c>=0).all() or len(keep)==1: break
                keep=[kk for kk,ci in zip(keep,c) if ci>0]
            coef=np.zeros(len(cols)); coef[keep]=c
        else: coef,*_=np.linalg.lstsq(A,y[mask],rcond=None)
        preds[k]=X[k,cols]@coef
    r=np.corrcoef(preds,y)[0,1]; err=np.abs(preds-y)
    top=np.argsort(-y)[:8]; toprank=[int((preds>preds[t]).sum())+1 for t in top]
    return r, np.median(err), np.percentile(err,90), toprank, preds
sets={"bytes":[0],"bytes+nat":[0,8],"bytes+nat+whnf":[0,8,6],"bytes+frontier+nat+whnf":[0,1,8,6],"all 10":list(range(10)),"all 10 nonneg":list(range(10))}
print("leave-one-out over 572 leaves: r, median |err|, p90 |err| (GiB); ranks of the 8 heaviest measured leaves")
for nm,cols in sets.items():
    r,me,p90,tr,_=loo(cols, nonneg=nm.endswith("nonneg"))
    print(f"  {nm:26s} r={r:.3f}  med {me:4.1f}  p90 {p90:4.1f}  ranks {tr}")
coef=fit(list(range(10)),nonneg=True)
print("\nnon-negative fit on all leaves, record bytes per unit:")
for nm,c in zip(names,coef): print(f"  {nm:10s} {c*2**30:12.1f}")
r,me,p90,tr,preds=loo(list(range(10)),nonneg=True)
print("\nheaviest measured leaves under the LOO all-10 nonneg model:")
for t in np.argsort(-y)[:8]: print(f"  leaf {ids[t]:3d} measured {y[t]:6.1f} predicted {preds[t]:6.1f}")

# Delta graph: CSR after the block records. Features per leaf: bytes of producer bodies unfolded by the
# leaf's consumers (all, and only foreign producers), and delta edge counts.
p=16+88*n; ne=struct.unpack_from("<Q",b,p)[0]; p+=8
row=np.frombuffer(b,dtype="<u8",count=n+1,offset=p); p+=8*(n+1)
col=np.frombuffer(b,dtype="<u4",count=ne,offset=p)
addrs=list(prof.keys()); sizes=np.array([prof[a][1] for a in addrs],float); idx={a:i for i,a in enumerate(addrs)}
X2=[]
for i,(bl,own,cross) in enumerate(leaves):
    if i not in rec: continue
    mem=set(idx[a] for a in bl if a in idx); unf=0.0; funf=0.0; edges=0; fedges=0
    for a in bl:
        c=idx.get(a)
        if c is None: continue
        prods=col[row[c]:row[c+1]]; edges+=len(prods); s=sizes[prods].sum(); unf+=s
        f=[pp for pp in prods if pp not in mem]; fedges+=len(f); funf+=sizes[f].sum()
    X2.append([unf,funf,edges,fedges])
X2=np.array(X2,float); Xa=np.hstack([X,X2]); names2=names+["unfolded_bytes","foreign_unfolded_bytes","delta_edges","foreign_delta_edges"]
X=Xa
def loo2(cols):
    preds=np.zeros(len(y))
    for k in range(len(y)):
        mask=np.arange(len(y))!=k; A=X[mask][:,cols]; keep=list(range(len(cols)))
        while True:
            c,*_=np.linalg.lstsq(A[:,keep],y[mask],rcond=None)
            if (c>=0).all() or len(keep)==1: break
            keep=[kk for kk,ci in zip(keep,c) if ci>0]
        coef=np.zeros(len(cols)); coef[keep]=c; preds[k]=X[k,cols]@coef
    r=np.corrcoef(preds,y)[0,1]; err=np.abs(preds-y); top=np.argsort(-y)[:8]
    return r,np.median(err),np.percentile(err,90),[int((preds>preds[t]).sum())+1 for t in top],preds
print("\nwith delta-graph features (nonneg, LOO):")
for nm,cols in {"prev 10":list(range(10)),"all 14":list(range(14)),"5 terms + unfolded":[0,1,5,6,8,10,11]}.items():
    r,me,p90,tr,preds=loo2(cols); print(f"  {nm:22s} r={r:.3f}  med {me:4.1f}  p90 {p90:4.1f}  ranks {tr}")
A=X; keep=list(range(14))
while True:
    c,*_=np.linalg.lstsq(A[:,keep],y,rcond=None)
    if (c>=0).all() or len(keep)==1: break
    keep=[kk for kk,ci in zip(keep,c) if ci>0]
print("  surviving terms:", {names2[k]: round(float(ci*2**30),1) for k,ci in zip(keep,c)})
r,me,p90,tr,preds=loo2(list(range(14)))
for t in np.argsort(-y)[:8]: print(f"  leaf {ids[t]:3d} measured {y[t]:6.1f} predicted {preds[t]:6.1f}")
