declare type WittGrp;
declare attributes WittGrp: p,k, n, m, R, S, P;

/*
This file defines the type of a truncated Witt Group scheme over k
p is the characteristic of k
k is the ground field
n,m are the degree of nilpotency of F,V resp.
R is the Hopf algebra
S are the additive Witt polynomials
P are the multiplicative Witt polynomials
*/
Wittpoly:=function(k,p,n,m,poly)
d:=Rank(Parent(poly));
AlgZ:=PolynomialRing(Integers(),d*m);
w:=[[&+[p^i*AlgZ.(i+1+m*nu)^(p^(j-i)): i in [0..j]]: nu in [0..d-1]]: j in [0..m-1]];
wappl:=[Evaluate(poly, w[j]): j in [1..m]];
ret:=[wappl[1]];
for j in [1..m-1] do
      ret[j+1]:=(wappl[j+1]-&+[p^i*ret[i+1]^(p^(j-i)): i in [0..j-1]]) div p^j;
end for;
return ret;
end function;

intrinsic Print(X::WittGrp)
{Print X}
printf "Witt group scheme W_(%o,%o) over %o", X`n, X`m, X`k;
end intrinsic;



intrinsic WittGroup(k:: Fld, n::RngIntElt, m::RngIntElt )->WittGrp
{Creates a truncated Witt group scheme}
Wnm:=New(WittGrp);
Wnm`k:=k;
p:=Characteristic(k);
Wnm`p:=p;
Wnm`n:=n;
Wnm`m:=m;
Wnm`R:=quo<PolynomialRing(k,m)| [$.i^(p^n): i in [1..m]]>;
Algk:=quo<PolynomialRing(k,2*m)| [$.i^(p^n): i in [1..2*m]]>;
T:=PolynomialRing(Integers(),2);
Wnm`S:=[Evaluate(Wittpoly(k,p,n,m,T.1+T.2)[j], [Algk.nu: nu in [1..2*m]]): j in [1..m]];
Wnm`P:=Wittpoly(k,p,n,m,T.1*T.2);
return Wnm;
end intrinsic;

intrinsic MapDieu(Wnm::WittGrp, Fcoeff::SeqEnum, Vcoeff::SeqEnum)-> SeqEnum
{computes the map corresponding to the element of the Dieudonne ring sum_i Fcoeff[i]*F^(i-1)+Vcoeff[i]*V^i}
lenF:=#Fcoeff;
lenV:=#Vcoeff;
k:=Wnm`k;

p:=Wnm`p;
R:=Wnm`R;
S:=Wnm`S;
n:=Wnm`n;
m:=Wnm`m;
Algk:=PolynomialRing(k,2*m);                            
P:=[Evaluate(Wnm`P[i], [Algk.nu: nu in [1..2*m]]): i in [1..m]];
if lenF eq 0 and lenV eq 0 then
   return [R.i: i in [1..m]];
elif lenF ne 0 and lenV ne 0 then
mpdF:=MapDieu(Wnm, Fcoeff, []);
mpdV:=MapDieu(Wnm,  [],Vcoeff);

return [Evaluate(S[i], mpdF cat mpdV): i in [1..m]];
elif lenF eq 1 then
 a:=Eltseq(Fcoeff[1]);
return [Evaluate(P[i], a cat [R.nu: nu in [1..m]]): i in [1..m]];
elif lenV eq 1 then
 a:=Eltseq(Vcoeff[1]);
return  [Evaluate(P[i], a cat [R!0] cat [R.nu: nu in [1..m-1]]): i in [1..m]];
 elif lenF gt 1  then
 mpd1:=MapDieu(Wnm, Fcoeff[1..(lenF div 2)],[]);
mpd2:=MapDieu(Wnm, Fcoeff[((lenF div 2)+1)..lenF],[]);
return [Evaluate(S[i], mpd1 cat [Evaluate(mpd2[nu],[R.mu^(p^(lenF div 2)): mu in [1..m]]): nu in [1..m]]): i in [1..m]];
 else
 mpd1:=MapDieu(Wnm, [],Vcoeff[1..(lenV div 2)]);
 mpd2:=MapDieu(Wnm, [], Vcoeff[((lenV div 2)+1)..lenV]);
return [Evaluate(S[i], mpd1 cat [Evaluate(mpd2[nu],[R!0: mu in [1..(lenV div 2)]] cat [R.mu : mu in [1..(m-(lenV div 2))]]): nu in [1..m]]): i in [1..m]];
end if;




end intrinsic;

intrinsic ArtinHasse(Wnm::WittGrp) -> RngMPolResElt
{Computes the Artin-Hasse series expressing the duality of Wnm and Wmn. We assume that m>=n}
p:=Wnm`p;
n:=Wnm`n;
m:=Wnm`m;
R:=quo<PolynomialRing(Rationals(), 2*m)| [$.i^(p^n): i in [1..2*m]]>;
Rp:=quo<PolynomialRing(GF(p), 2*m)| [$.i^(p^n): i in [1..m]]>;
X:=[[R.i: i in [1..m]] cat [R!0: i in [1..n]],[R.(i+m): i in [1..m]] cat [R!0: i in [1..n]]];
w:=[[&+[p^i*X[nu][i+1]^(p^(j-i)): i in [0..j]]: nu in [1..2]]: j in [0..n+m-1]];
expAH:=&+[(-&+[w[j+1][1]*w[j+1][2]/p^j: j in [0..n+m-1]])^i/Factorial(i): i in [0..m*p^n-1]];
return Evaluate(expAH, [Rp.i: i in [1..2*m]]);


/*
P:=Wnm`P;
R:=quo<PolynomialRing(Rationals())|$.1^(p^n)>;
Rp:=quo<PolynomialRing(GF(p))|$.1^(p^n)>;
expAH:=&+[(&+[R.1^(p^j)/p^j: j in [0..n-1]])^i/Factorial(i): i in [0..p^n-1]];
expAH:=Rp![GF(p)!c: c in Coefficients(expAH)];
Alg:=quo<PolynomialRing(GF(p), n+m)|[$.i^(p^n): i in [1..m]] cat [$.i^(p^m): i in [m+1..n+m]]>;
return &*[Evaluate(expAH,Evaluate(P[i], [Alg.j: j in [1..m]] cat [Alg.j: j in [m+1..n+m]] cat [Alg!0: j in [1..m-n]])): i in [1..m]];*/
end intrinsic;
