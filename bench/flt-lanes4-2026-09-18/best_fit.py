import numpy as np, itertools, sys
exec(open("/tmp/claude-30033/-home-sam-repos-ix/7a750869-d86c-440e-8a5f-69578352a576/scratchpad/record_model.py").read().split("def fit(")[0])  # builds X (10 cols), y, ids
# add delta-graph features (same code as before)
p=16+88*n; ne=struct.unpack_from("<Q",b,p)[0]; p+=8
row=np.frombuffer(b,dtype="<u8",count=n+1,offset=p); p+=8*(n+1); col=np.frombuffer(b,dtype="<u4",count=ne,offset=p)
addrs=list(prof.keys()); sizes=np.array([prof[a][1] for a in addrs],float); idx={a:i for i,a in enumerate(addrs)}
X2=[]
for i,(bl,own,cross) in enumerate(leaves):
    if i not in rec: continue
    mem=set(idx[a] for a in bl if a in idx); unf=funf=0.0; edges=fedges=0
    for a in bl:
        c=idx.get(a)
        if c is None: continue
        prods=col[row[c]:row[c+1]]; edges+=len(prods); unf+=sizes[prods].sum(); fp=[pp for pp in prods if pp not in mem]; fedges+=len(fp); funf+=sizes[fp].sum()
    X2.append([unf,funf,edges,fedges])
X=np.hstack([X,np.array(X2,float)]); names=names+["unfolded","foreign_unfolded","edges","foreign_edges"]
try:
    from scipy.optimize import nnls
except ImportError:
    nnls=None
def nnfit(A,yy):
    if nnls: return nnls(A,yy)[0]
    keep=list(range(A.shape[1]))
    while True:
        c,*_=np.linalg.lstsq(A[:,keep],yy,rcond=None)
        if (c>=0).all() or len(keep)==1: break
        keep=[k for k,ci in zip(keep,c) if ci>0]
    coef=np.zeros(A.shape[1]); coef[keep]=c; return coef
def loo(cols):
    A=X[:,cols]; preds=np.zeros(len(y))
    for k in range(len(y)):
        mask=np.arange(len(y))!=k; preds[k]=A[k]@nnfit(A[mask],y[mask])
    return preds
def score(preds):
    r=np.corrcoef(preds,y)[0,1]; err=np.abs(preds-y)
    top20=set(np.argsort(-y)[:20]); ptop40=set(np.argsort(-preds)[:40]); recall=len(top20&ptop40)/20
    return r, float(np.median(err)), float(np.percentile(err,90)), recall
results=[]
for k in (1,2,3,4):
    for cols in itertools.combinations(range(len(names)),k):
        preds=loo(list(cols)); results.append((score(preds),cols))
results.sort(key=lambda t:-t[0][0])
print("best subsets by leave-one-out correlation (r, median err, p90 err, recall of the 20 heaviest within predicted top 40):")
for (r,me,p90,rc),cols in results[:8]:
    print(f"  r={r:.3f} med {me:4.1f} p90 {p90:4.1f} recall {rc:.2f}  " + " + ".join(names[c] for c in cols))
print("best by top-20 recall, then r:")
for (r,me,p90,rc),cols in sorted(results,key=lambda t:(-t[0][3],-t[0][0]))[:5]:
    print(f"  recall {rc:.2f} r={r:.3f} med {me:4.1f}  " + " + ".join(names[c] for c in cols))
best=results[0][1]; coef=nnfit(X[:,best],y)
print("\nchosen model (all leaves, non-negative), record bytes per unit:")
for c,ci in zip(best,coef): print(f"  {names[c]:16s} {ci*2**30:12.1f}")
preds=X[:,best]@coef
print("\nheaviest 12 measured leaves under it (measured, predicted, predicted rank):")
order=np.argsort(-preds)
for t in np.argsort(-y)[:12]: print(f"  leaf {ids[t]:3d}  {y[t]:6.1f}  {preds[t]:6.1f}  rank {int(np.where(order==t)[0][0])+1}")
print("\npredicted top 12 (leaf, predicted, measured):")
for t in order[:12]: print(f"  leaf {ids[t]:3d}  {preds[t]:6.1f}  {y[t]:6.1f}")
