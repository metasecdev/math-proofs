# Computed numerics (NOT Lean): proved guard depths vs. the least sufficient depth piNeed(n).
import math, json
from mpmath import mp
def nlog16(x):
    k=0
    while 16**(k+1) <= x: k+=1
    return k
def need(n):
    mp.prec = 4*n + 400
    x = mp.mpf(16)**n * mp.pi
    d = abs(x - mp.nint(x))
    g = 0
    while not (mp.mpf(16)**g * d > 2*(4*(n+g+1)+2)): g += 1
    return g
rows=[]
for n in [0,1,10,100,1000,10**4,10**5,10**6]:
    L=nlog16(n+1)+1
    rows.append(dict(n=n, A=569*n+L+2273495, B=569*n+L+1795710, Bsimple=570*n+1795711, M658=657*n+L+430009, need=need(n)))
    print(rows[-1], flush=True)
json.dump(rows, open('guardtable.json','w'), indent=1)
