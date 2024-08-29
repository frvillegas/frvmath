\\ Time-stamp: <Thu, Aug 29, 2024 - 17:29:28 - villegas>
\\
\\

\\ Basic routine for computing the hypergeometric trace. It uses the
\\ p-adic gamma function and the Gross-Koblitz formula to compute Gauss
\\ sums. One advantage of this method it that deal smoothly with the
\\ issue of individual characters of a given Gauss sum being definable
\\ only on an extension of the ground field. It does not check that
\\ the value of f is an allowable option. It should be divisible by
\\ the norm exponent of the prime above p in the field of definition
\\ of the HGM (see examples 2 and 3). 


\\ This function computes the trace of a general hypergeometric
\\ motive H. The multisets alpha and beta can actually be of different size
\\ as long as the powers of (-p) in the coefficients are integral.

hgm(z,a,b,p,f=1,bd=20)=
{
        my(C,q,r,s,sa,sb);

        q=p^f;
        z=teichmuller(z+O(p^bd));
        r=length(a);
        s=length(b);
        C=prod(i=0,f-1,
                prod(k=1,r,gamma(frac(p^i*a[k])+O(p^bd)))
                /prod(k=1,s,gamma(frac0(p^i*b[k])+O(p^bd))));
        sa=sum(i=0,f-1,
                sum(k=1,r,
                        frac(p^i*a[k])));
        sb=sum(i=0,f-1,
                sum(k=1,s,
                        frac0(p^i*b[k])));
        (1+sum(m=1,q-2,

                prod(i=0,f-1,
                prod(k=1,r,
                        gamma(frac(p^i*(a[k]-m/(q-1)))+O(p^bd)))
                /prod(k=1,s,
                        gamma(frac0(p^i*(b[k]-m/(q-1)))+O(p^bd))))
                *(-p)^sum(i=0,f-1,
                        sum(k=1,r,
                                frac(p^i*(a[k]-m/(q-1))))
                        -sum(k=1,s,
                                frac0(p^i*(b[k]-m/(q-1)))),
                                -sa+sb)
                *z^m)
                /C)/(1-q)
;}

\\ The following computes the Euler factor using the traces of powers
\\ of Frobenius. The parameter l is optional and determines the
\\ highest degree to compute. This is useful as computing the full
\\ polynomial directly is a heavy computation.

hgmfrob(t,a,b,p,f=1,l,bd=20)=
{
        my(d);

        d=max(length(a),length(b));
        if(l,d=l);

        truncate(1/exp(sum(i=1,d,

                                hgm(t,a,b,p,i*f,bd)*x^i/i,O(x^(d+1)))))
;}

\\----------------------------------------------------------------------
\\ Helper functions

\\ Recognize a p-adic number as rational
\\ Recover prime p directly from the input

recognizep(x)=
{
        my(n,m,z,np,nm);

	if(type(x) == "t_PADIC",

	      p=component(x,1);
        n=padicprec(x,p);
        m=n\2;
        z=bestappr(truncate(x)/p^n,p^m);
		z=denominator(z);
    np=truncate(x*z);
		nm=truncate(-x*z);if(np < nm, np/z,-nm/z),
        x)
;}

\\ Recognize p-adic coefficients of polynomial as rationals

polrecognizep(pol)=
{
         sum(i=0,poldegree(pol),

                recognizep(polcoeff(pol,i))*x^i)
;}

\\ The following is a simple modification of the fractional part of a
\\ real number that it is useful to have as a separate routine. 

frac0(x)=x=frac(x);if(x == 0,x=1);x;

\\----------------------------------------------------------------------
\\ Example 1

\\ Hesse family of elliptic curves
\\ a=[1/3,2/3]; b=[1,1];

\\ ? e=[1,0,t/27,0,0];

\\ Fix the specialization t = 2 and compare the trace of Frobenius on
\\ the elliptic curve with the hypergeometric trace

\\ ? e2=ellinit(subst(e,t,2));

\\ ? forprime(p=5,50,print(p,"\t ",ellap(e2,p),"\t",recognizep(hgm(2,a,b,p))))

\\ 5     -3     -3
\\ 7     -1     -1
\\ 11    3      3
\\ 13    -4     -4
\\ 17    0      0
\\ 19    2      2
\\ 23    6      6
\\ 29    -6     -6
\\ 31    5      5
\\ 37    2      2
\\ 41    6      6
\\ 43    -10    -10
\\ 47    -6     -6
```

\\----------------------------------------------------------------------
\\ Example 2

\\ Motive not defined over the rationals
\\ a=[3/8,-3/8]; b=[1/8,-1/8];

\\ The field of definition of H is the quadratic field K determined by
\\ x^2-2=0. We can compute the hypergeometric trace for t rational for a
\\ prime of K above p by choosing f = 1,2 according to whether p splits
\\ or is inert in K.

\\ For t = -1 H is the elliptic curve
\\ https://beta.lmfdb.org/EllipticCurve/Q/256/a/
\\ over the field K

\\ ? e256=ellinit("256a1")

\\ ?  test(t0,e,bd=50)=my(a,b,z);a=[3/8,-3/8];b=[1/8,-1/8];forprime(p=5,bd,s=kronecker(2,p);w=ellap(e,\
p);if(s==1,z=hgm(t0,a,b,p),z=hgm(t0,a,b,p,2);w=w^2-2*p);z*=p^((3-s)/2);print(p,"  ",s,"  ",recognizep\
(z),"  ",w))

\\ test(-1,e256)

\\ 5  -1  -10  -10
\\ 7  1  0  0
\\ 11  -1  14  14
\\ 13  -1  -26  -26
\\ 17  1  -6  -6
\\ 19  -1  -34  -34
\\ 23  1  0  0
\\ 29  -1  -58  -58
\\ 31  1  0  0
\\ 37  -1  -74  -74
\\ 41  1  6  6
\\ 43  -1  14  14
\\ 47  1  0  0

\\ A similar phenomenon also appears to hold for any specialization
\\ t = square

\\ ? e36=ellinit("36a1");
\\ ? test(9,e36)

\\ 5  -1  -10  -10
\\ 7  1  -4  -4
\\ 11  -1  -22  -22
\\ 13  -1  -22  -22
\\ 17  1  0  0
\\ 19  -1  26  26
\\ 23  1  0  0
\\ 29  -1  -58  -58
\\ 31  1  -4  -4
\\ 37  -1  26  26
\\ 41  1  0  0
\\ 43  -1  -22  -22
\\ 47  1  0  0

\\----------------------------------------------------------------------
\\ Example 3
\\ A curve of genus 2 with real multiplication by sqrt 5

\\ Take a=[1/N,-1/N];b=[1,1] for N an odd prime. Then the
\\ hypergeometric motive H is a factor of H^1 of a hyperelliptic curve
\\ C_N(t) of genus (N-1)/2. For example, for N = 5 we have

\\ C_5(t): y^2 = (x^5 - 5*x^3 + 5*x+2*(1-2*t)*(x+2)

\\ The field of definition of H is the real quadratic field F with
\\ equation x^2-5 = 0

? ex3(t0)=my(a,b,z);a=[1/5,-1/5];b=[1,1];forprime(p=7,50,s=kronecker(5,p);if(s==1,z=hgm(t0,a,b,p),z=h\
gm(t0,a,b,p,2));print(p,"  ",s,"  ",algdep(z,2)))

\\ Take t = -1 then

\\ ? ex3(-1)

\\ 7  -1  x + 10
\\ 11  1  x - 2
\\ 13  -1  x
\\ 17  -1  x - 20
\\ 19  1  x^2 - 5*x - 25
\\ 23  -1  x - 30
\\ 29  1  x^2 - 5*x - 25
\\ 31  1  x^2 + x - 31
\\ 37  -1  x + 10
\\ 41  1  x^2 + x - 31
\\ 43  -1  x + 70
\\ 47  -1  x + 70

\\ Looking in LMBDF this matches the coefficients of the Hilbert
\\ modular form

\\ HMF 500.1-b
\\ http://www.lmfdb.org/ModularForm/GL2/TotallyReal/2.2.5.1/holomorphic/2.2.5.1-500.1-b

\\ As a further check we compute with MAGMA say the Euler factor of
\\ the L-series of C_5(-1) for p = 19. We find

\\ 361*T^4 - 95*T^3 + 13*T^2 - 5*T + 1

\\ which factors over F as

\\ ? nf=nfinit(y^2-5*y-25);nffactor(nf,361*x^4 - 95*x^3 + 13*x^2 - 5*x + 1)

\\ [      x^2 + Mod(-1/19*y, y^2 - 5*y - 25)*x + 1/19 1]
\\ [x^2 + Mod(1/19*y - 5/19, y^2 - 5*y - 25)*x + 1/19 1]

\\ matching the eigenvalues given in LMFDB

\\ We can also check this Euler factor against the HGM

\\ ? L1=hgmfrob(-1,[1/5,-1/5],[1,1],19)
\\ (19 + O(19^20))*x^2 + (13 + 7*19 + 6*19^2 + 3*19^3 + 18*19^4 + 8*19^5 + 9*19^6 + 14*19^7 + 13*19^8 + 15*19^9 + 4*19^10 + 4*19^11 + 11*19^12 + 9*19^13 + 11*19^14 + 13*19^15 + 8*19^16 + 14*19^17 + 16*19^18 + 15*19^19 + O(19^20))*x + 1

\\ ? L2=hgmfrob(-1,[2/5,-2/5],[1,1],19)
\\ (19 + O(19^20))*x^2 + (1 + 11*19 + 12*19^2 + 15*19^3 + 10*19^5 + 9*19^6 + 4*19^7 + 5*19^8 + 3*19^9 + 14*19^10 + 14*19^11 + 7*19^12 + 9*19^13 + 7*19^14 + 5*19^15 + 10*19^16 + 4*19^17 + 2*19^18 + 3*19^19 + O(19^20))*x + 1

\\ ? L=L1*L2
\\ (19^2 + O(19^21))*x^4 + (14*19 + 18*19^2 + 18*19^3 + 18*19^4 + 18*19^5 + 18*19^6 + 18*19^7 + 18*19^8 + 18*19^9 + 18*19^10 + 18*19^11 + 18*19^12 + 18*19^13 + 18*19^14 + 18*19^15 + 18*19^16 + 18*19^17 + 18*19^18 + 18*19^19 + O(19^20))*x^3 + (13 + O(19^20))*x^2 + (14 + 18*19 + 18*19^2 + 18*19^3 + 18*19^4 + 18*19^5 + 18*19^6 + 18*19^7 + 18*19^8 + 18*19^9 + 18*19^10 + 18*19^11 + 18*19^12 + 18*19^13 + 18*19^14 + 18*19^15 + 18*19^16 + 18*19^17 + 18*19^18 + 18*19^19 + O(19^20))*x + 1

\\ ? polrecognizep(L)
\\ 361*x^4 - 95*x^3 + 13*x^2 - 5*x + 1
