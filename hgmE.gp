\\ Time-stamp: <Mon, Nov 18, 2024 - 09:03:40 - villegas>
\\

\\ See F. Rodriguez Villegas "Mixed Hodge numbers and factorial ratios"
\\ https://arxiv.org/pdf/1907.02722v1 whose notation we follow below.

\\----------------------------------------------------------------------
\\ The routine gives the E-polynomial of the primitive part of the
\\ middle cohomology w compact supports of the affine hypersurface in
\\ torus.

\\ Defn 3.13 Batyrev "Variations of the mixed Hodge structure
\\ of affine hypersurfaces in algebraic tori"

\\ Extension of delta by Katz-Stapledon. The same as fmla at the top
\\ of p.14 of Borisov-Mavlyutov, itself a reformulation of theorem in
\\ archive version of Batyrev-Borisov Thm 3.18 (Mirror duality and
\\ string-theoretic Hodge numbers).  We don't include the torus term. 
\\ See also  E. Katz slides: "Hodge theory of degeneration of
\\ hypersurf"

hgmE(v)=
{
	my(n,dv,z,S,s);

	n=length(v);
	s=0;for(i=1,n,if(v[i] > 0, s++));
	dv=distdiv(v);

	for(i=1,length(dv),
		z=hgmsimplex(dv[i],v);
			if(z[1]  > 0 && z[2] > 0,
				S+=b^(length(v)-z[1]-z[2])
				*((a*b)^min(z[1],z[2])-1)/(a*b-1)
				*subst(z[5],x,a/b)));

	S+=subst(hgmhodgev(v)[1],x,a/b)*b^(length(v)-1);

\\      From Cor. 3.10 in paper of Batyrev  "Variations of the MHS..."  
\\ 	we need only substract 1 from S coming from the weight
\\ 	0 part of the middle cohomology (compact supported) of the
\\ 	ambient torus by duality this is the top weight in usual
\\ 	cohomology (!?)

	S=(S-1)/a/b;

\\	Return polynomial in a,b

		return(S)
;}

hgmhodgev(v,flag=1)=
{
	my(z,u,S,dvi);
	
	u=distdiv(v);
	S=0;
	div=[];
	
	for(i=1,length(u),

 		z=hgmsimplex(u[i],v);

		if(flag == 1 && (z[1] > z[2]),

			div=concat(div,u[i]);
			S+=z[5]
			*(x^z[1]-x^z[2])/(x-1));

		if(flag == -1 && (z[2] > z[1]),

			div=concat(div,u[i]);
			S+=z[5]
			*(x^z[2]-x^z[1])/(x-1)));

	return([S,div]);
;}


\\ Term for a given simplex determined by x = */N of denominator N
\\ Output is [m^+, m^-, v^+, v^-, \delta^\#_N]

\\ m^+, m^- = number of \gamma_i's divisible by N according to its
\\ sign

\\ v^+, v^- = Location of \gamm_i's divisible by N in the input vector
\\ v according to sign (0 = divisible, 1 = not divisible)

\\ \delta^\#_N = partial Hodge polynomial as in the paper


hgmsimplex(N,v)=
{
	my(vpos,vneg,mpos,mneg,n,z,S);

	
	n=length(v);
	vpos=[];vneg=[];

	for(i=1,n,if(v[i] > 0,
			  z=v[i]%N;

			  if(z == 0,mpos++,z=1);vpos=concat(vpos,z)));
	for(i=1,n,if(v[i] < 0,
			  z=v[i]%N;

			  if(z == 0,mneg++,z=1);vneg=concat(vneg,z)));

	if(N == 1, return([mneg,mpos,vneg,vpos,1]));

	
	S=0;

	for(j=1,N-1,

		if(gcd(j,N) == 1,
			    S+=x^sum(k=1,n,frac(j/N*v[k]))));

	[mneg,mpos,vneg,vpos,S]
;}

\\----------------------------------------------------------------------
\\ Simple membership function. Returns the first index j such that
\\ g=v[j] or 0 if no such j exists.

memb(g,v)=for(k=1,length(v),if(g==v[k],return(k)));0;

\\ All distinct divisors of an entry in vector v

distdiv(v)=
{
	my(dv,w);

	w=[];

	for(i=1,length(v),

		w=concat(w,divisors(v[i])));
	dv=[];

 	for(i=1,length(w),

		k=memb(w[i],dv);
		
			if(k  == 0,
				dv=concat(dv,w[i])));
	return(vecsort(dv))
;}

\\----------------------------------------------------------------------
\\ Chebyshev example (end of section 4 in the paper)

\\ Gamma vector v = [-30,-1,6,10,15]

\\ ? hgmE([-30,-1,6,10,15])
\\ (8*a + 7)*b + (7*a + 8)

\\ ? fordiv(30,d,print(d,"  ",hgmsimplex(d,[-30,-1,6,10,15])))

\\ 1  [2, 3, [0, 0], [0, 0, 0], 1]
\\ 2  [1, 2, [0, 1], [0, 0, 1], x]
\\ 3  [1, 2, [0, 1], [0, 1, 0], 2*x]
\\ 5  [1, 2, [0, 1], [1, 0, 0], 4*x]
\\ 6  [1, 1, [0, 1], [0, 1, 1], x^2 + x]
\\ 10  [1, 1, [0, 1], [1, 0, 1], 2*x^2 + 2*x]
\\ 15  [1, 1, [0, 1], [1, 1, 0], 4*x^2 + 4*x]
\\ 30  [1, 0, [0, 1], [1, 1, 1], 8*x^2]
