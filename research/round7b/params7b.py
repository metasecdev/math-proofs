"""Exact constants for MahlerSharp7 spec: m=141, n=4k+n0, lcm<=exp(1.4063n+11000), tail 8.55/(m+1),
log(n+1) <= (n+1)/2^17 - 1 + 17 log2, log m, log(m+1) <= 8 log2, log3 <= 2log2,
log(8.55/142) <= -(81/20) log2. Uses worst-case log2 in [0.6931471803, 0.6931471808], pi<3.1416."""
from fractions import Fraction as F
from math import log, ceil
lo,hi=F(6931471803,10**10),F(6931471808,10**10); PI=F(31416,10**4)
m=141; c=F(14063,10**4); K=8760; d=F(1,2**17); s=F(81,20)
assert (F(855,100)/142)**20 <= F(1,2**81)
def lsucc(n,L): return (n+1)*d-1+17*L   # log(n+1)
def rem(k,n0,L):  # log remainder bound minus log target (must be <=0)
    n=4*k+n0
    lhs=m*8*L + m*(c*n+K) + m*8*L + (2*m+1)*lsucc(n,L) + n*(m+1)*L - n*(m+1)*s*L + (2*n+1)*PI/2
    tgt=-(L + m*(L+4*k*L))
    return lhs-tgt
def T(k,n0,L):  # log T bound
    n=4*k+n0
    return 8*L+8*L+m*2*L+lsucc(n,L)+m*8*L+m*(c*n+K)+n*(m+1)*L+m*8*L+2*m*lsucc(n,L)
# find n0: rem linear in k; need coefficient<=0 and value at k=0 <=0 for both L extremes
for n0 in [12600]:
    if all(rem(0,n0,L)<=0 and rem(1,n0,L)-rem(0,n0,L)<=0 for L in (lo,hi)): break
print("n0",n0, [float(rem(1,n0,L)-rem(0,n0,L)) for L in (lo,hi)])
# T <= (B0 + B1 k) log2 : T/L per k slope and intercept (max over L)
B1=max(ceil((T(1,n0,L)-T(0,n0,L))/L) for L in (lo,hi)); B0=max(ceil(T(0,n0,L)/L) for L in (lo,hi))
B1+= (-B1)%4
print("B1",B1,"B0",B0,"mu",m+B1//4)
