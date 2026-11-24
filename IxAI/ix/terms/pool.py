import numpy as np, collections
R='/opt/dlami/nvme/ix-ai/terms/'
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
maddr,mkind,mt,mv=load('mathlib-d13f23b')
AM={a:i for i,a in enumerate(maddr)}
use=collections.Counter(); stmt=collections.Counter()
nthm=0
for i,k in enumerate(mkind):
    if k!='thm': continue
    nthm+=1
    for r in mv.get(i,[]):
        if mkind[r]=='thm': use[maddr[r]]+=1
    for r in mt.get(i,[]): stmt[maddr[r]]+=1
top=[a for a,_ in stmt.most_common()]
top4=set(top[:4000]); top65=set(top[:65536])
print('mathlib env: constants',len(maddr),'theorems',nthm,'theorems used as a premise',len(use),'constants in statements',len(stmt))
tot_new_thm=0; tot_new=0
print('%-18s %9s %9s %9s %9s | %7s %8s %8s %8s | %8s %8s %8s'%('library','constants','new','new thm','new def','prem/thm','lib own','M used','M unused','top4k','top65k','own const'))
for s in ['core-v4.34.1','cslib-v4.34.0','flt-v4.34.0','physlean-v4.34.1']:
    addr,kind,t,v=load(s)
    new=[i for i,a in enumerate(addr) if a not in AM]
    nt=[i for i in new if kind[i]=='thm']; nd=[i for i in new if kind[i]=='def']
    pc=collections.Counter(); np_=0; sc=collections.Counter(); withp=0
    for i in nt:
        ps=[r for r in v.get(i,[]) if kind[r]=='thm']
        if ps: withp+=1
        for r in ps:
            a=addr[r]; np_+=1
            pc['own' if a not in AM else ('used' if a in use else 'unused')]+=1
        for r in t.get(i,[]):
            a=addr[r]
            sc['own' if a not in AM else ('t4' if a in top4 else ('t65' if a in top65 else 'rest'))]+=1
    ns=max(sum(sc.values()),1); n_=max(np_,1)
    print('%-18s %9d %9d %9d %9d | %7.2f %7.1f%% %7.1f%% %7.1f%% | %7.1f%% %7.1f%% %7.1f%%'%(s,len(addr),len(new),len(nt),len(nd),np_/max(len(nt),1),100*pc['own']/n_,100*pc['used']/n_,100*pc['unused']/n_,100*sc['t4']/ns,100*(sc['t4']+sc['t65'])/ns,100*sc['own']/ns))
    tot_new+=len(new); tot_new_thm+=len(nt)
print('pooled: new constants',tot_new,'new theorems',tot_new_thm,'(not deduplicated across the four)')
