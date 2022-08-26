AttachSpec("spec");

/*Attach("ssEllCurvEndStr.m");
Attach("MtrxWitt.m");
Attach("WittGroups.m");
//Attach("rosenhain.m");
import "rosenhain.m": RosenhainInvariantsFromThetaSquares;*/

function NewKernel(A)
	E, T := EchelonForm(A);
	r := 0;
	while r lt Nrows(E) and not IsZero(E[r + 1]) do r +:= 1; end while;
	return Rowspace(RowSubmatrix(T, r + 1, Nrows(A) - r));
end function;


padicVal:=function(r,p)
Zp:=pAdicRing(p);
return Valuation(Zp!Norm(r));
end function;


g_H:=function(Str, R, KExE, gnum,gden, alpha)
E:=Str`E;
p:=Characteristic(KExE);
y1 := KExE.1;
y2 := KExE.2;
x1 := KExE.3;
x2 := KExE.4;
zcal:=R.1;
Laurent<z>:=LaurentSeriesRing(KExE,p+3);
E_:=BaseChange(E,Laurent);
P1:=E_![x1,y1,1];
P2:=E_![x2,y2,1];
Log, P:=FormalLog(E:Precision:=p+3);
Exp:=Reverse(Log);
z1:=Evaluate(Exp, alpha[1]*zcal);
z2:=Evaluate(Exp, alpha[2]*zcal);
Sum1:=P1+E_!P;
Sum2:=P2+E_!P;
if (AbsolutePrecision(Sum1[1]) lt p or  AbsolutePrecision(Sum1[2]) lt p or  AbsolutePrecision(Sum1[3]) lt p or AbsolutePrecision(Sum2[1]) lt p or  AbsolutePrecision(Sum2[2]) lt p or  AbsolutePrecision(Sum2[3]) lt p) then
	  print "Error: Precision too low";
end if;
eval1:=[Evaluate(Coordinates(Sum1)[i], z1): i in [1..3]];
eval2:=[Evaluate(Coordinates(Sum2)[i], z2): i in [1..3]];
return [Evaluate(gnum,[eval1[2]/eval1[3],eval2[2]/eval2[3],eval1[1]/eval1[3],eval2[1]/eval2[3]]),Evaluate(gden,[eval1[2]/eval1[3],eval2[2]/eval2[3],eval1[1]/eval1[3],eval2[1]/eval2[3]])];
end function;

eval0:=function(phi, g)
phinum:=Numerator(phi);
phiden:=Denominator(phi);
AEg:=Parent(phinum);
k:=BaseRing(AEg);
R:=PolynomialRing(k, g);
phinumeval:=Evaluate(phinum, Flat([[R.i^3: i in [1..g]],[R.i^2: i in [1..g]]]));
phideneval:=Evaluate(phiden, Flat([[R.i^3: i in [1..g]],[R.i^2: i in [1..g]]]));
dnum:=TotalDegree(phinumeval);
dden:=TotalDegree(phideneval);
if dnum lt dden then
return 0;
 elif dnum gt dden then
 print "Error: Function has a pole at 0";
else
   num:=HomogeneousComponent(phinumeval, dnum);
   den:=HomogeneousComponent(phideneval, dnum);
   ret:=k!ExactQuotient(num, den);
return ret;
end if;
end function;

TwoTorsTrans:=function(Str, P, num, den, KEg, g)
E:=Str`E;
k:=BaseField(E);
a1:=Coefficients(E)[1];
a2:=Coefficients(E)[2];
a3:=Coefficients(E)[3];
a4:=Coefficients(E)[4];
a6:=Coefficients(E)[5];
xsubs:=[((E!P[nu] eq E![0,1,0]) select KEg.(nu+g) else (2*P[nu][1]^2+P[nu][1]*KEg.(nu+g)+2*P[nu][1]*a2+a4)/(KEg.(nu+g)-P[nu][1])): nu in [1..g]];
ysubs:=[((E!P[nu] eq E![0,1,0]) select KEg.(nu) else KEg.nu*(-3*P[nu][1]^2-2*P[nu][1]*a2-a4)/(KEg.(nu+g)-P[nu][1])^2): nu in [1..g]];
return Evaluate(num, Flat([ysubs, xsubs]))/Evaluate(den, Flat([ysubs, xsubs]));
end function;

GenTrans:=function(Str, P, num, den, KEg, g)
E:=Str`E;
k:=BaseField(E);
a1:=Coefficients(E)[1];
a2:=Coefficients(E)[2];
a3:=Coefficients(E)[3];
a4:=Coefficients(E)[4];
a6:=Coefficients(E)[5];
lambda:=[(E!P[i] eq E![0,1,0]) select KEg!0 else (KEg.i-P[i][2])/(KEg.(i+g)-P[i][1]): i in [1..g]];
nu:=[(E!P[i] eq E![0,1,0]) select KEg!0 else (KEg.(i+g)*P[i][2]-KEg.i*P[i][1])/(KEg.(i+g)-P[i][1]): i in [1..g]];
xsubs:=[(E!P[i] eq E![0,1,0]) select KEg.(i+g) else lambda[i]^2+a1*lambda[i]-a2-KEg.(i+g)-P[i][1]: i in [1..g]];
ysubs:=[(E!P[i] eq E![0,1,0]) select KEg.i else -(lambda[i]+a1)*xsubs[i]-nu[i]-a3   : i in [1..g]];
return Evaluate(num, Flat([ysubs, xsubs]))/Evaluate(den, Flat([ysubs, xsubs]));
end function;

PullbackMult:=function(Str, N, num, den, KEg, g)
E:=Str`E;
k:=BaseField(E);
a1:=Coefficients(E)[1];
a2:=Coefficients(E)[2];
a3:=Coefficients(E)[3];
a4:=Coefficients(E)[4];
a6:=Coefficients(E)[5];
MultNPolys:= DefiningPolynomials(Endomorphism(Str, Str`B!N));
 xsubs:=[Evaluate(MultNPolys[1], [KEg.(i+g), KEg.i,1])/Evaluate(MultNPolys[3], [KEg.(i+g), KEg.i,1]): i in [1..g]];
 ysubs:=[Evaluate(MultNPolys[2], [KEg.(i+g), KEg.i,1])/Evaluate(MultNPolys[3], [KEg.(i+g), KEg.i,1]): i in [1..g]];
return Evaluate(num, Flat([ysubs, xsubs]))/Evaluate(den, Flat([ysubs, xsubs]));
end function;


FastQuo:=function(numsubs,densubs,ratnum, ratden, degNumO,g)
  //This function computes the quotient (numsubs*ratnum)/(densubs*ratden) quickly using the degree bound degNum for the result.
  R:=Parent(numsubs);
p:=Characteristic(R);
KEg:=BaseRing(R);
densubsconst:=Numerator(TrailingCoefficient(densubs));
AEg:=Parent(densubsconst);
AA2g:=OriginalRing(AEg);
cdensubsconst, mdensubsconst:=CoefficientsAndMonomials(densubsconst);
cratden, mratden:=CoefficientsAndMonomials(ratden);
min1, arg1:=Min([[3*Degree(m, i)+ 2*Degree(m,i+g): i in [1..g]]: m in mdensubsconst]);
min2, arg2:=Min([[3*Degree(m, i)+ 2*Degree(m,i+g): i in [1..g]]: m in mratden]);
degtm:=[p^(g-1)*min1[i]+min2[i]: i in [1..g]];
idxdensubsconst:=[nu: nu in [1..#mdensubsconst]| &and[p^(g-1)*(3*Degree(mdensubsconst[nu],i)+2*Degree(mdensubsconst[nu],i+g)) le degtm[i]+degNumO[i]: i in [1..g]]];
idxratden:=[nu: nu in [1..#mratden]| &and[(3*Degree(mratden[nu],i)+2*Degree(mratden[nu],i+g)) le degtm[i]+degNumO[i]: i in [1..g]]];
densubsconstpgm1:=&+[(cdensubsconst[nu]*mdensubsconst[nu])^(p^(g-1)): nu in idxdensubsconst];
ratden:=&+[cratden[nu]*mratden[nu]: nu in idxratden];
den:=densubsconstpgm1*ratden;
degB:=[degtm[i]+degNumO[i]+1:i in [1..g]];
I:=Ideal(&cat[[AA2g.i^j*AA2g.(i+g)^(Ceiling((degB[i]-3*j) / 2) lt 0 select 0 else Ceiling((degB[i]-3*j) / 2)): j in [0..Ceiling(degB[i] / 3)]]: i in [1..g]]);

den:=NormalForm(AA2g!den,I);
ratnum:=AEg!NormalForm(AA2g!ratnum,I);
cnumsubs, mnumsubs:=CoefficientsAndMonomials(numsubs);
cdensubs, mdensubs:=CoefficientsAndMonomials(densubs);
//Notice that numsubs, densubs are in AEg[...]
numsubs:=&+[KEg!NormalForm(AA2g!Numerator(cnumsubs[nu]),I)*mnumsubs[nu]: nu in [1..#mnumsubs]];
densubs:=&+[KEg!NormalForm(AA2g!Numerator(cdensubs[nu]),I)*mdensubs[nu]: nu in [1..#mdensubs]];
bin:=Intseq(p^(g-1)-1,2);
densubspow:=[densubs];
for i in [1..#bin-1] do
      sq:=densubspow[i]^2;
      csq, msq:=CoefficientsAndMonomials(sq);
      Append(~densubspow,&+[KEg!NormalForm(AA2g!Numerator(csq[nu]),I)*msq[nu]: nu in [1..#msq]]);
end for;
num:=  KEg!ratnum*numsubs*&*[densubspow[i]^bin[i]: i in [1..#bin]];
cnum, mnum:=CoefficientsAndMonomials(num);
cnum:= [NormalForm(AA2g!Numerator(cnum[nu]),I): nu in [1..#mnum]];
if &and[IsDivisibleBy(cnum[nu], den): nu in [1..#mnum]] then
      return &+[KEg!(cnum[nu] div den) * mnum[nu]: nu in [1..#mnum]];
 else
   print "Fast quotient not implemented yet.";
print degB, cnum, den;
end if;
end function;


HyperbolicDec:=function(N,Pair,g);
fac:=Factorisation(N);
om:=#fac;
J:=DiagonalJoin([Matrix([[0,1],[-1,0]]): j in [1..g]]);
Xret:=[];
for i in [1..om] do
      pi:=fac[i][1];
V:=VectorSpace(GF(pi), 2*g, Matrix(GF(pi), Pair));
HS:=HyperbolicSplitting(V)[1];
X0:=Transpose(BlockMatrix(g,1,[Matrix(h): h in HS]));
X:=Matrix(Integers(),X0);
        for j in [1..fac[i][2]-1] do
	      Mat:=(J-Transpose(X)*Pair*X) div pi^j;
              Math:=Matrix(GF(pi),[[(mu ge nu select Mat[mu,nu] else 0): nu in [1..2*g]]: mu in [1..2*g]]);
              X1:=(Transpose(X0)*Pair)^(-1)*Math;
              X:=X+pi^j*Matrix(Integers(),X1);
	end for;
Xret[i]:=X;
end for;
ret:=Matrix([[CRT([Xret[i][mu,nu]: i in [1..om]], [fac[i][1]^fac[i][2]: i in [1..om]]): nu in [1..2*g]]: mu in [1..2*g]]);
if &and[&and[IsDivisibleBy((Transpose(ret)*Pair*ret-J)[mu,nu],  N): nu in [1..2*g]]: mu in [1..2*g]] then
    return ret;
 else
   print "Error while computing hyperbolic decomposition";
end if;
end function;



H0half:=function(Str, fij, param, rat, v, degNumO, g, KEg, Eg)
  //This function needs as an input the O-lattices ker(fij) and the isomorphism O/F = F_{p^2}.
  p:=Characteristic(KEg);
  if g eq 2 then
       AEg:=Parent(Numerator(KEg!1));
       Num:=rat[1];
       G:=rat[2];
R<z>:=quo<PolynomialRing(KEg,1)| $.1^p>;
       S<eps,eps_>:=quo<PolynomialRing(KEg,2)| $.1^2, $.2^2>;
       alpha:=[ActionOnTangentSpace(Str, Conjugate(v[1][1][1][i])): i in [1..2]];
       alpha_:=[ActionOnTangentSpace(Str, Conjugate(v[2][1][1][i])): i in [1..2]];
       y1 := KEg.1;
       y2 := KEg.2;
       x1 := KEg.3;
       x2 := KEg.4;
       gHout:=g_H(Str, R, KEg, Num, G, alpha_);
//Multiply the coefficients with G
       gH:=FastQuo(gHout[1], gHout[2],Evaluate(G,[AEg.1,AEg.2,AEg.3,AEg.4]), AEg!1, degNumO,g);
       gHcoeff:=Coefficients(gH);
       AEg:=CoordinateRing(Eg);
       f:=hom<KEg-> AEg |AEg.1,AEg.2,AEg.3,AEg.4>;
       gHMat:=HorizontalJoin(Matrix([[f(c): c in gHcoeff]]),ZeroMatrix(AEg,1,p+1-#gHcoeff));
       eva:=Matrix([Flat([[Factorial(2*i)*(-(AEg!param[1])/2)^i/Factorial(i),0]:i in [0..((p-1)/2)]  ])]);
       gtildaG:=(gHMat*Transpose(eva))[1,1];
       return KEg!gtildaG/ Evaluate(G,[y1,y2,x1,x2]);
elif g eq 3 then
       f:=&+fij[1];
       r:=#fij;
       L:=Parent(param[1]);
       p:=Characteristic(L);
       split:=Splitting(Str, fij, g);
//       c:=CommutatorPairing(Str, f, g);
       prec:=Length(Parent(split`entries[1][1]));
       E:=Str`E;
AEg:=Parent(Numerator(KEg!1));
AA2g:=OriginalRing(AEg);
       prec2:=g-1;
       W:=WittRing(L, prec);
       W2:=WittRing(L,prec2);
       R:=quo<Integers()|p^prec2>;
       split:=Matrix([[W!Eltseq(split`entries[i][j]): j in [1..split`n]]: i in [1..split`m]]);
/*c:=Matrix([[W!Eltseq(c`entries[i][j]): j in [1..c`n]]: i in [1..c`m]]);
       zero:=ZeroMatrix(W,2*g,2*g);
       shuffle:=BlockMatrix(r,r,&cat[[c: j in [1..i]] cat [zero: j in [1..r-i]]: i in [0..r-1]]);*/
//TODO: Checke, dass Kern maximal isotrop.


//This formula will only work nicely if eta is multiplication by a power of p:
h:=Transpose(Matrix([[W!([param[nu]] cat [0: i in [1..prec-1]]): nu in [1..2*g]]]));
       splith:=Mult(split, h);
/*hcoeff:=[Matrix([&cat[[W!0, W![Frobenius(param[2*nu+1],-1)]]: nu in [0..g-1]]]), Matrix([[W![Frobenius(param[nu],0)]: nu in [1..2*g]]]), Matrix([&cat[[W!0, -W![Frobenius(param[2*nu+1],1)]]: nu in [0..g-1]]])];
       if &or[Product([hcoeff[i], c, Transpose(hcoeff[i])])`entries[1][1] ne W!0: i in [1..3]] then
       print "Error: Subgroup scheme is not isotropic";
       end if;
//These formulas only work if g=3.
       modi2:=[Product([hcoeff[i],Transpose(split), shuffle, splith])`entries[1][1]: i in [1..3]];
       modiF:= [W2!(Eltseq(modi2[2]) cat [L!0]) *  W2!(Integers()!(R!(p/2))), W2!(Eltseq(modi2[3]) cat [L!0]) *  W2!(Integers()!(R!(1/2)))];
       modiV:=[W2!(Eltseq(modi2[1]) cat [L!0]) *  W2!(Integers()!(R!(1/2)))];
*/       Wnn:=WittGroup(L,g-1,g-1);
       RWnn:=Wnn`R;
//       multi:=Evaluate(ArtinHasse(Wnn), MapDieu(Wnn, modiF, modiV) cat  [RWnn.i: i in [1..g-1]]);
       Poly<t0,t1>:=PolynomialRing(KEg,g-1);
       R:=quo<Poly| [$.i^(p^(g-1)): i in [1..(g-1)]]>;
       yi:=[AEg.i: i in [1..g]];
       xi:=[AEg.i: i in [g+1..2*g]];
       Laurent<z>:=LaurentSeriesRing(KEg,p^(g-1)+3);
       E_:=BaseChange(E,Laurent);
       Log, P:=FormalLog(E:Precision:=p^(g-1)+3);
       Pi:=[E_![xi[i],yi[i],1]: i in [1..g]];
       Sumi:=[Pi[i]+E_!P: i in [1..g]];
       if &or[&or[AbsolutePrecision(Sumi[i][nu]) lt p^(g-1): nu in [1..3]]: i in [1..g]] then
             print "Error: Precision too low";
       end if;
       wittsurj:= WittSurj(Str, g-1);
mapFcoeff:=[[ [W2!(Eltseq(splith`entries[2*g*i+2*j+1][1]) cat [L!0: i in [1..g-1-prec]]), W2!(Eltseq(splith`entries[2*g*i+2*j+2][1]) cat [L!0: i in [1..g-1-prec]]) ]: j in [0..g-1]]: i in [0..r-1]];
mapW:=[[MapDieu(Wnn, mapFcoeff[i][j], []):j in [1..g]]: i in [1..r]];
evalu:=[[[Evaluate(Coordinates(Sumi[j])[nu], Evaluate(Evaluate(wittsurj, mapW[i][j]),[R.gam: gam in [1..(g-1)]])): nu in [1..3]]: j in [1..g]]: i in [1..r]];
evalu:=[[evalu[i][j][2]/evalu[i][j][3]: j in [1..g]] cat [evalu[i][j][1]/evalu[i][j][3]: j in [1..g]]: i in [1..r]];
hom1:= [[Evaluate(Evaluate(wittsurj, mapW[i][j]), Wnn`S): j in [1..g]]: i in [1..r]];
T:=Parent(hom1[1][1]);
hom2:= [[Evaluate(FormalGroupLaw(E, 2*p^(g-1)), [Evaluate(Evaluate(wittsurj, mapW[nu][j]), [T.i: i in [1..g-1]]) , Evaluate(Evaluate(wittsurj, mapW[nu][j]), [T.(i+g-1): i in [1..g-1]])]): j in [1..g]]: nu in [1..r]];

if hom1 eq hom2 then
print "Maps are group homomorphisms...Check";
 else
   print "Error: Maps are not group homomorphisms";
return false;
end if;
/*degNum:=[Ceiling((degNumO[i])/3) : i in [1..g]];
res3:=[(- degNumO[i]) mod 3: i in [1..g]];
expE:=[[a: a in Flat([[<i1,i2>: i2 in [0..degNum[i]-i1 ]]: i1 in [0..Min(2,degNum[i])]])| (a[2] ne degNum[i] or res3[i] eq  0) and (a[1] ne 1 or a[2]  ne degNum[i]-1 or res3[i] ne 1)   ]: i in [1..g]];
num:=[R!Monomial(AA2g,[j: j in Flat(e)]): e in CartesianProduct(expE) ];
dim:=#num;
den:=[R!1: i in [1..dim]];
T:=Time();
//Könnte in der ersten for-Schleife noch mit Quotienten von R arbeiten.
for i in [r..1 by -1] do
      cnum:=[Coefficients(num[nu]): nu in [1..dim]];
      mnum:=[Monomials(num[nu]): nu in [1..dim]];
      cden:=[Coefficients(den[nu]): nu in [1..dim]];
      mden:=[Monomials(den[nu]): nu in [1..dim]];
      cnumsubs:=[[Evaluate(Numerator(cnum[nu][ex]), evalu[i]): ex in [1..#cnum[nu]]]: nu in [1..dim]];
      cdensubs:=[[Evaluate(Numerator(cden[nu][ex]), evalu[i]): ex in [1..#cden[nu]]]: nu in [1..dim]];
      numsubs:=[&+[cnumsubs[nu][ex]*mnum[nu][ex]: ex in [1..#mnum[nu]]]: nu in [1..dim]];
      densubs:=[&+[cdensubs[nu][ex]*mden[nu][ex]: ex in [1..#mden[nu]]]: nu in [1..dim]];
      fun:=[FastQuo(numsubs[mu],densubs[mu],Evaluate(rat[i], [AEg.nu: nu in [1..2*g]]), Evaluate(rat[r], [AEg.nu: nu in [1..2*g]]), degNumO,g): mu in [1..dim]];
      num:=[fun[mu]* Evaluate(rat[r], [KEg.nu: nu in [1..2*g]]): mu in [1..dim]];
      den:=[R!Evaluate(rat[(i-2) mod r + 1], [KEg.nu: nu in [1..2*g]]): mu in [1..dim]];


      end for;
print [Evaluate(multi, [R.i: i in [1..g-1]])*num[mu]/den[mu]: mu in [1..dim]] ;
*/




num:=R!1;
den:=R!1;
T:=Time();
for i in [r..1 by -1] do

	      cnum, mnum:=CoefficientsAndMonomials(num);
	      cden, mden:=CoefficientsAndMonomials(den);
              cnumsubs:=[Evaluate(Numerator(cnum[ex]), evalu[i]): ex in [1..#cnum]];
              cdensubs:=[Evaluate(Numerator(cden[ex]), evalu[i]): ex in [1..#cden]];
              numsubs:=&+[cnumsubs[ex]*mnum[ex]: ex in [1..#cnum]];
              densubs:=&+[cdensubs[ex]*mden[ex]: ex in [1..#cden]];
              fun:=FastQuo(numsubs,densubs,Evaluate(rat[i], [AEg.nu: nu in [1..2*g]]), Evaluate(rat[r], [AEg.nu: nu in [1..2*g]]), degNumO,g);
              num:=fun* Evaluate(rat[r], [KEg.nu: nu in [1..2*g]]);
              den:=R!Evaluate(rat[(i-2) mod r + 1], [KEg.nu: nu in [1..2*g]]);
      end for;
num1:=num;
den1:=den;
num:=R!Evaluate(rat[r], [KEg.nu: nu in [1..2*g]]);
den:=R!Evaluate(rat[1], [KEg.nu: nu in [1..2*g]]);
T:=Time();
for i in [1..r] do
	      cnum, mnum:=CoefficientsAndMonomials(num);
	      cden, mden:=CoefficientsAndMonomials(den);
              cnumsubs:=[Evaluate(Numerator(cnum[ex]), evalu[i]): ex in [1..#cnum]];
              cdensubs:=[Evaluate(Numerator(cden[ex]), evalu[i]): ex in [1..#cden]];
              numsubs:=&+[cnumsubs[ex]*mnum[ex]: ex in [1..#cnum]];
              densubs:=&+[cdensubs[ex]*mden[ex]: ex in [1..#cden]];
              fun:=FastQuo(numsubs,densubs,Evaluate(rat[i], [AEg.nu: nu in [1..2*g]]), Evaluate(rat[r], [AEg.nu: nu in [1..2*g]]), degNumO,g);
              num:=fun* Evaluate(rat[r], [KEg.nu: nu in [1..2*g]]);
              den:=R!Evaluate(rat[i mod r + 1], [KEg.nu: nu in [1..2*g]]);
      end for;
multi2sq:=FastQuo( num*den1, num1*den, Evaluate(rat[1], [AEg.nu: nu in [1..2*g]]), Evaluate(rat[r], [AEg.nu: nu in [1..2*g]]), [0: i in [1..g]],g);
Pow:=PowerSeriesRing(Rationals(): Precision:=(g-1)*p^(g-1));
Powk:=PowerSeriesRing(GF(p): Precision:=(g-1)*p^(g-1));
sqrt:=Powk!Sqrt(1+Pow.1);
act1:=Evaluate(Evaluate(sqrt, multi2sq-1), [R.i: i in [1..g-1]])*num1/den1;
num2:=num;
den2:=den;
//Needs to be modified if g>3:
lead:=LeadingCoefficient(Evaluate(act1, [0, R.2]));
if lead eq den1 then
num:=R!MonomialCoefficient(act1, R.1^3);
den:=den1;
for i in [r..1 by -1] do

	      cnum, mnum:=CoefficientsAndMonomials(num);
	      cden, mden:=CoefficientsAndMonomials(den);
              cnumsubs:=[Evaluate(Numerator(cnum[ex]), evalu[i]): ex in [1..#cnum]];
              cdensubs:=[Evaluate(Numerator(cden[ex]), evalu[i]): ex in [1..#cden]];
              numsubs:=&+[cnumsubs[ex]*mnum[ex]: ex in [1..#cnum]];
              densubs:=&+[cdensubs[ex]*mden[ex]: ex in [1..#cden]];
              fun:=FastQuo(numsubs,densubs,Evaluate(rat[i], [AEg.nu: nu in [1..2*g]]), Evaluate(rat[r], [AEg.nu: nu in [1..2*g]]), degNumO,g);
              num:=fun* Evaluate(rat[r], [KEg.nu: nu in [1..2*g]]);
              den:=R!Evaluate(rat[(i-2) mod r + 1], [KEg.nu: nu in [1..2*g]]);
      end for;
act2:=Evaluate(Evaluate(sqrt, multi2sq-1), [R.i: i in [1..g-1]])*num/den;

return KEg!(LeadingCoefficient(act1)/den1);
 else
     num:=lead;
T:=Time();
for i in [r..1 by -1] do

	      cnum, mnum:=CoefficientsAndMonomials(num);
	      cden, mden:=CoefficientsAndMonomials(den);
              cnumsubs:=[Evaluate(Numerator(cnum[ex]), evalu[i]): ex in [1..#cnum]];
              cdensubs:=[Evaluate(Numerator(cden[ex]), evalu[i]): ex in [1..#cden]];
              numsubs:=&+[cnumsubs[ex]*mnum[ex]: ex in [1..#cnum]];
              densubs:=&+[cdensubs[ex]*mden[ex]: ex in [1..#cden]];
              fun:=FastQuo(numsubs,densubs,Evaluate(rat[i], [AEg.nu: nu in [1..2*g]]), Evaluate(rat[r], [AEg.nu: nu in [1..2*g]]), degNumO,g);
              num:=fun* Evaluate(rat[r], [KEg.nu: nu in [1..2*g]]);
              den:=R!Evaluate(rat[(i-2) mod r + 1], [KEg.nu: nu in [1..2*g]]);
      end for;
act1:=Evaluate(Evaluate(sqrt, multi2sq-1), [R.i: i in [1..g-1]])*num/den;
return KEg!(LeadingCoefficient(act1)/den);   
   end if;



Time(T);
end if;
end function;


intrinsic AuxillaryRatFun(Str::ssEllCurvEndStr, fij::SeqEnum, PQ::SeqEnum,Trans::SeqEnum,N::RngIntElt, g::RngIntElt)-> Tup
{Given a sequence of decompositions f=sum f_ij where j=1..r and N-tors points Pi,Qi and 2N-tors points Pi2, Qi2 this function computes the rational functions giving the rational equivalence between the auxillary divisors. Furthermore this function computes the rational functions coming from the N-power level groups described by Pi, Pi2,Qi, Qi2. It also returns a Z-basis of ker(fij)}
E:=Str`E;
FullEnd(Str);
a1:=Coefficients(E)[1];
a2:=Coefficients(E)[2];
a3:=Coefficients(E)[3];
a4:=Coefficients(E)[4];
a6:=Coefficients(E)[5];
B:=Str`B;
indepB:=Str`indepB;
indep:=Str`indep;
basisB:=Str`basisB;
basis:=Str`basis;
r:=#fij;
f_i:=fij[r];
f:=&+f_i;
Pi:=PQ[1];
Pi2:=PQ[2];
Qi:=PQ[3];
Qi2:=PQ[4];
FB:=Str`FB;
k:=BaseField(E);
p:=Characteristic(k);
K:=FunctionField(E);
E_:=BaseChange(E,K);
A2g:=AffineSpace(k,2*g);
A2gm2:=AffineSpace(k,2*(g-1));
//The ordering of the coordinates of P2g is x1,y1,z1,x2, y2, z2,...
P2g:=ProductProjectiveSpace(k, [2: i in [1..g]]);
//Setup an affine patch for E^(g-1), E^g. The ordering of the variables is y1, y2,...,x1, x2,... 
Eg:=Scheme(A2g,[(A2g.i)^2-((A2g.(i+g))^3+a2*(A2g.(i+g))^2+a4*(A2g.(i+g))+a6): i in [1..g]]);
EgProj:=Scheme(P2g, [(P2g.(2+3*i))^2*(P2g.(3+3*i))-((P2g.(1+3*i))^3+a2*(P2g.(1+3*i))^2*(P2g.(3+3*i))+a4*(P2g.(1+3*i))*(P2g.(3+3*i))^2+a6*(P2g.(3+3*i))^3): i in [0..g-1]]);
Egm1:=Scheme(A2gm2,[(A2gm2.i)^2-((A2gm2.(i+g-1))^3+a2*(A2gm2.(i+g-1))^2+a4*(A2gm2.(i+g-1))+a6): i in [1..g-1]]);
K:=FunctionField(E);
E_:=BaseChange(E,K);
P:=CoordinateRing(P2g);
AA2g:=CoordinateRing(A2g);
AA:=CoordinateRing(A2gm2);
AEg:=CoordinateRing(Eg);
KEg:=FieldOfFractions(AEg);
AEgm1:=CoordinateRing(Egm1);
KEgm1:=FieldOfFractions(AEgm1);
E_KEgm1:=BaseChange(E,KEgm1);

//We compute the maps E^g-> E_{I_i}
A:=Matrix([Coordinates(a): a in basisB]);
q:=DiagonalJoin([Matrix([[Integers()!Trace(Conjugate(x)*y): y in basisB]:  x in basisB]): i in [1..g]]);
imagf_:=[BlockMatrix(g,g, [[Solution(A, Matrix([Coordinates(B,basisB[j]*f_i[i][nu,mu]): j in [1..4]])): mu in [1..g]]: nu in [1..g] ]): i in [1..g] ];
imagf_:=[Matrix([[Integers()!imagf_[i][mu,nu]: nu in [1..4*g]]: mu in [1..4*g]]): i in [1..g]];
basisimagf_:=[Matrix(HermiteForm(imagf_[i])[1..4]): i in [1..g]];
basisimagf_B:=[[[ &+[basisimagf_[i][r,mu+4*j]*basisB[mu]: mu in [1..4]]: j in [0..g-1]]: r in [1..4]]: i in [1..g]];
zeroentries:=[[mu: mu in [1..g]| basisimagf_B[i][1][mu] eq 0 ]: i in [1..g]];
nonzeroentries:=[[mu: mu in [1..g]| basisimagf_B[i][1][mu] ne 0 ]: i in [1..g]];
signs:=[[[mu: mu in a]: a in CartesianPower([-1,1],g) | a ne <1: i in [1..g]> and &and[a[mu] eq 1: mu in zeroentries[i]] and a[Min(nonzeroentries[i])] eq 1 ]: i in [1..g]];
//The ith entry of inftyComps is the sequence of indeces j such that the jth component is the ith divisor at infinity
inftyComps:=[[j: j in [1..g]| nonzeroentries[j] eq [i] ]  : i in [1..g] ];
inftyCompsFl:=Sort(Flat(inftyComps));
cardinftyComps:=[IsEmpty(inftyComps[i]) select 0 else p^(Min(Flat([[padicVal(f_i[i][mu,nu],p): mu in [1..g]]: nu in [1..g]])) div 2): i in [1..g]];
if IsEmpty(inftyCompsFl) then
     ninfIn:=[1..g];
else
 ninfIn:=Flat([(inftyCompsFl[1] eq 1 select [] else [1..inftyCompsFl[1]-1]),[[inftyCompsFl[mu]+1..inftyCompsFl[mu+1]-1]  : mu in [1..#inftyCompsFl-1]| inftyCompsFl[mu] ne inftyCompsFl[mu+1]-1], (inftyCompsFl[#inftyCompsFl] eq g select [] else [inftyCompsFl[#inftyCompsFl]+1..g])]);
end if;
/*Dieser Teil des Algorithmus muss noch einmal überarbeitet werden. Bin nicht sicher, ob das macht, was es soll:
 * I_ ist ein gebrochenes Ideal mit O < I_
 * 
 */
Limag_:=[LatticeWithGram(basisimagf_[i]*q*Transpose(basisimagf_[i])): i in [1..g]];
shortimag_:=[Coordinates(ShortestVectors(Limag_[i])[1]): i in [1..g]];
simag_:=[Transpose(basisimagf_[i])*Transpose(Matrix(([shortimag_[i]]))): i in [1..g]];
vimag_:=[[ &+[simag_[i][mu+4*j, 1]*basisB[mu]: mu in [1..4]]: j in [0..g-1]]: i in [1..g]];

I_:=[];
for i in [1..g] do
      mu:=1;
      while vimag_[i][mu] eq 0 do
	 mu:=mu+1;
      end while;
      I_[i]:=[1/vimag_[i][mu]*basisimagf_B[i][nu][mu]: nu in [1..4]];
end for;
Deu:=[Deuring(Str, I_[i], false): i in [1..g]];
EI:=[Deu[i][1]: i in [1..g]];
EI_:=[BaseChange(EI[i], K): i in [1..g]];

EI_KEg:=[BaseChange(EI[i], KEg): i in [1..g]];
d:=[Degree(Deu[i][2]): i in [1..g]];
vimag_:=[[FB^(-(Min(Flat([[padicVal(f_i[i][mu,nu],p): mu in [1..g]]: nu in [1..g]])) div 2))*vimag_[i][j]: j in [1..g]]: i in [1..g]];
dphiEI:=[[Endomorphism(Str, vimag_[i][mu]) * Deu[i][2]: mu in [1..g]]: i in [1..g]];
phiEI_asPointspre:=<[ asPoint(dphiEI[i][mu], EI_[i])/d[i]: mu in [1..g]]: i in [1..g]>;
phiEIpre:=<[asMap(E,EI[i], phiEI_asPointspre[i][mu]): mu in [1..g]]: i in [1..g]>;
//The Division by N can lead to an unpleasant N-torsion point that needs to be subtracted
phiEI_asPoints:=<[ phiEI_asPointspre[i][mu] - EI_[i]!phiEIpre[i][mu]([0,1,0]) : mu in [1..g]]: i in [1..g]>;
phiEI:=<[asMap(E,EI[i], phiEI_asPoints[i][mu]): mu in [1..g]]: i in [1..g]>;
phiEIPi2:=<[&+[phiEI[i][mu](Pi2[nu][mu]): mu in [1..g]]: nu in [1..g]]: i in [1..g]>;
phiEIQi2:=<[&+[phiEI[i][mu](Qi2[nu][mu]): mu in [1..g]]: nu in [1..g]]: i in [1..g]>;
mapsEgmEI_asPoints:=<&+[EI_KEg[i]![Evaluate(DefiningPolynomials(phiEI[i][mu])[j], [KEg.(mu+g),KEg.(mu),1]): j in [1..3]]: mu in [1..g]]: i in [1..g]>;



//Compute the matrices for the maps E^g->E^(g-1)    
v:=[[Basis(NewKernel(fij[j][i])): i in [1..g]]: j in [1..r]];
Y:=[[BlockMatrix(g-1, g, Flat([[Matrix([Solution(A,Vector(Coordinates(B,basisB[mu]*v[j][i][nu][xi]))): mu in [1..4]]): xi in [1..g]]: nu in [1..g-1] ])): i in [1..g]]: j in [1..r]];
Y:=[[Denominator(Y[j][i])*Y[j][i]: i in [1..g]]: j in [1..r]];
Si:=[[]: j in [1..r]];
for i in [1..g] do
	for j in [1..r] do
	      U, Si[j][i]:= SmithForm(Matrix([[Integers()|Y[j][i][mu,nu]: mu in [1..4*(g-1)]]:nu in [1..4*g]]));
        end for;
end for;
Z:=[[ColumnSubmatrix(Si[j][i]^(-1),4*(g-1)): i in [1..g]]: j in [1..r]];
//q is 2 times the Gram matrix of quadratic form v^* v on O^g with respect to the basis basisB.
L:=[[LatticeWithGram(Transpose(Z[j][i])*q*Z[j][i]): i in [1..g]]: j in [1..r]];
//Was ist eine gute Schranke für max?
max:=[[Max(Diagonal(LLLGramMatrix(L[j][i]))): i in [1..g]]: j in [1..r]];
short:=<<ShortVectors(L[j][i], max[j][i]): i in [1..g]>: j in [1..r]>;
s:=[[[Z[j][i]*Transpose(Matrix(([Coordinates(short[j][i][1][1] )])))]: i in [1..g]]: j in [1..r]];
for j in [1..r] do
     for i in [1..g] do
        sji:=Z[j][i]*Transpose(Matrix(([Coordinates(short[j][i][1][1] )])));
        LinIndji:= Matrix(B, [[ &+[sji[mu+4*xi, 1]*basisB[mu]: mu in [1..4]]: xi in [0..g-1]]]);
	run:=2;
        for nu in [2..g-1] do
                 sji:=Z[j][i]*Transpose(Matrix(([Coordinates(short[j][i][run][1] )])));
		 //Die Überprüfung der linearen Unabhängigkeit funktioniert noch nicht.
	  while nu ne Rank(VerticalJoin(LinIndji, Matrix(B,[[ &+[sji[mu+4*xi, 1]*basisB[mu]: mu in [1..4]]: xi in [0..g-1]]]))) do
			 run:=run+1;
                         sji:=Z[j][i]*Transpose(Matrix(([Coordinates(short[j][i][run][1] )])));
                 end while;
                 s[j][i][nu]:=sji;
                 LinIndji:=VerticalJoin(LinIndji, Matrix(B,[[ &+[sji[mu+4*xi, 1]*basisB[mu]: mu in [1..4]]: xi in [0..g-1]]]));
         end for;
     end for;
end for;
v:=[[[[ &+[s[j][i][nu][mu+4*xi, 1]*basisB[mu]: mu in [1..4]]: xi in [0..g-1]]: nu in [1..g-1]]: i in [1..g]]: j in [1..r]];
v_:=v[r];
v_signed:=[[[[signs[i][sig][j]*v_[i][nu][j]: j in [1..g]]: nu in [1..g-1]]: sig in [1..#signs[i]]]: i in [1..g]];
//Setup the maps E^(g-1)->E^(g)
phi:=[[[[Endomorphism(Str, Conjugate(v[j][i][nu][mu])): mu in [1..g]]: nu in [1..g-1]]: i in [1..g]]: j in [1..r-1]];
phi_signed:=[[[[Endomorphism(Str, Conjugate(v_signed[i][sig][nu][mu])): mu in [1..g]]: nu in [1..g-1]]: sig in [1..#signs[i]]]: i in [1..g]];
// We translate the divisor D
mapsasPoints:=[[[&+[E_KEgm1![Evaluate(DefiningPolynomials(phi[j][i][nu][mu])[1],[KEgm1.(nu+g-1),KEgm1.(nu),1]), Evaluate(DefiningPolynomials(phi[j][i][nu][mu])[2],[KEgm1.(nu+g-1),KEgm1.(nu),1]),Evaluate(DefiningPolynomials(phi[j][i][nu][mu])[3],[KEgm1.(nu+g-1),KEgm1.(nu),1])]: nu in [1..g-1]]+E_KEgm1!Trans[j][mu]: mu in [1..g]]: i in [1..g]]: j in [1..r-1]];
maps_signedasPoints:=[[[&+[E_KEgm1![Evaluate(DefiningPolynomials(phi_signed[i][sig][nu][mu])[1],[KEgm1.(nu+g-1),KEgm1.(nu),1]), Evaluate(DefiningPolynomials(phi_signed[i][sig][nu][mu])[2],[KEgm1.(nu+g-1),KEgm1.(nu),1]),Evaluate(DefiningPolynomials(phi_signed[i][sig][nu][mu])[3],[KEgm1.(nu+g-1),KEgm1.(nu),1])]: nu in [1..g-1]]  : mu in [1..g]]: sig in [1..#signs[i]]]: i in [1..g]];
mapsEgm1Eg:=[[map<Egm1-> EgProj | Flat([Coordinates(mapsasPoints[j][i][mu]): mu in [1..g] ])>: i in [1..g]]: j in [1..r-1]];
maps_signedEgm1Eg:=Flat([[map<Egm1-> EgProj | Flat([Coordinates(maps_signedasPoints[i][sig][mu]): mu in [1..g] ])>: sig in [1..#signs[i]]]: i in [1..g]]);
//Compute the auxillary rational function
if IsEmpty(ninfIn) then
G:=AA2g!1;
 else 
numG:=&*[Coordinates(mapsEgmEI_asPoints[i])[1]*&*Flat([[1],[Evaluate(Coordinates(mapsEgmEI_asPoints[i])[1], [sig[mu]*KEg.mu: mu in [1..g]] ): sig in signs[i] ]]): i in ninfIn];
denG:=&*[Coordinates(mapsEgmEI_asPoints[i])[3]*&*Flat([[1],[Evaluate(Coordinates(mapsEgmEI_asPoints[i])[3], [sig[mu]*KEg.mu: mu in [1..g]] ): sig in signs[i] ]]): i in ninfIn];
Gsq:=Denominator(numG/denG);
if not IsSquare(k.1) then
     quadnon:=k.1;
else
     quadnon:=PrimitiveElement(k);
end if;
b, G:=IsSquare(AA2g!Gsq);
if not b then
   bb, G:=IsSquare(quadnon*AA2g!Gsq);
end if;
end if;
expG:=[Exponents(m): m in Monomials(G)];
degG:=[Max([e[g+i]: e in expG]): i in [1..g]];
/*The homogenization of G has multidegree degG. However G actually comes from a section of the linebundle O(2degG[1] O_E,...) because it is a pullback along E^g->(P^1)^g
Therefore the numerator of the desired rational function should have multidegree ceil(2degG/3) and should have a prescribed zero of multiplicity 2degG/3 mod 3 at infinity. */
degNumO:=[2*degG[i] + cardinftyComps[i] : i in [1..g]];
degNum:=[Ceiling((degNumO[i])/3) : i in [1..g]];
res3:=[(cardinftyComps[i] - degG[i]) mod 3: i in [1..g]];
expE:=[[a: a in Flat([[<i1,i2,degNum[i]-i1-i2>: i2 in [0..degNum[i]-i1 ]]: i1 in [0..Min(2,degNum[i])]])| (a[2] ne degNum[i] or res3[i] eq  0) and (a[1] ne 1 or a[2]  ne degNum[i]-1 or res3[i] ne 1)   ]: i in [1..g]];
Mons:=[Monomial(P,[j: j in Flat(e)]): e in CartesianProduct(expE)| IsEven(&+[e[mu][2]: mu in [1..g]]) ];
Eval:=[[[AEgm1!Evaluate(m, DefiningEquations(map)): map in mapsEgm1Eg[j]]: m in Mons]: j in [1..r-1]];
Eval_signed:=[[AEgm1!Evaluate(m, DefiningEquations(map)): map in maps_signedEgm1Eg]: m in Mons];
Equ0:=[[Flat([Eval[j][i], Eval_signed[i]]): i in [1..#Mons]]: j in [1..r-1]];
Equ:=[[[Equ0[j][mu][nu]: mu in [1..#Mons]]: nu in [1..#Equ0[j][1]]]: j in [1..r-1]];
MonsEgm1:=[[Sort([s: s in &join [ {Exponents(m) : m in  Monomials(Equ[j][i][mu])}: mu in [1..#Mons]]]): i in [1..#Equ[j]]  ]: j in [1..r-1]];
Mtrx:=[HorizontalJoin([SparseMatrix(k, #Mons, #(MonsEgm1[j][i]), Flat([[<mu, findInSortedList(MonsEgm1[j][i], Exponents(Monomials(Equ[j][i][mu])[nu])), Coefficients(Equ[j][i][mu])[nu]>: nu in [1..Length(Equ[j][i][mu])]]: mu in [1..#Mons]])): i in [1..#Equ[j]]]): j in [1..r-1]];
polys:=[[&+[Vector(v)[i]*Mons[i]: i in [1..#Mons]]: v in Basis(Kernel(Mtrx[j]))]: j in [1..r-1]];
auxThetaPrePi:=[&*[&*[( phiEIPi2[i][mu] eq EI[i]![0,1,0]) select 1 else mapsEgmEI_asPoints[i][1]/mapsEgmEI_asPoints[i][3]- ((2*j-1)*phiEIPi2[i][mu])[1]: j in [1..N div 2]]: i in [1..g]]: mu in [1..g]];
auxThetaPi:=[TwoTorsTrans(Str, Trans[r], AA2g!Numerator(auxThetaPrePi[mu]), AA2g!Denominator(auxThetaPrePi[mu]), KEg, g)/GenTrans(Str, [E!Pi[mu][nu]+Trans[r][nu]: nu in [1..g]], AA2g!Numerator(auxThetaPrePi[mu]), AA2g!Denominator(auxThetaPrePi[mu]), KEg, g): mu in [1..g]];
auxThetaPreQi:=[&*[&*[( phiEIQi2[i][mu] eq EI[i]![0,1,0]) select 1 else mapsEgmEI_asPoints[i][1]/mapsEgmEI_asPoints[i][3] - ((2*j-1)*phiEIQi2[i][mu])[1]: j in [1..N div 2]]: i in [1..g]]: mu in [1..g]];
auxThetaQi:=[TwoTorsTrans(Str, Trans[r], AA2g!Numerator(auxThetaPreQi[mu]), AA2g!Denominator(auxThetaPreQi[mu]), KEg, g)/GenTrans(Str, [E!Qi[mu][nu]+Trans[r][nu]: nu in [1..g]], AA2g!Numerator(auxThetaPreQi[mu]), AA2g!Denominator(auxThetaPreQi[mu]), KEg, g): mu in [1..g]];
if IsSquare(N) then
n:=Integers()!Sqrt(N);
DivPolyEI:=[];
for i in [1..g] do
	psi1,psi2:=DivisionPolynomial(EI[i],n);
        REI:=CoordinateRing(EI[i]);
        DivPolyEI[i]:=Evaluate(psi2, REI.1)*REI.2;
end for;
AuxThetaStand:=[&*[Evaluate(DivPolyEI[i],Coordinates(mapsEgmEI_asPoints[i])): i in [1..g]]];
return <[auxThetaPi,auxThetaQi,AuxThetaStand],Flat([[Evaluate(polys[j][1], Flat([[AA2g.(g+i), AA2g.(i),1]: i in [1..g] ])): j in [1..r-1]], [AA2g!G]]),v, Eg, degNumO>;
end if;

/*The auxillary functions for the Theta computation are already translated using the translation that gives a divisor D not containing 0. The rational functions giving the rational equivalences between the auxillary divisors are NOT translated.*/
return <[auxThetaPi,auxThetaQi],Flat([[Evaluate(polys[j][1], Flat([[AA2g.(g+i), AA2g.(i),1]: i in [1..g] ])): j in [1..r-1]], [AA2g!G]]),v, Eg, degNumO>;
end intrinsic;

intrinsic ThetaNull(Str::ssEllCurvEndStr, fij::SeqEnum,param::SeqEnum,N::RngIntElt, g::RngIntElt)->SeqEnum
{Computes the Theta nullvalues of the Divisor N*Thera on the quotient E^g/H. Here H is a maximally isotropic subgroup scheme whose Dieudonne module is described via param. If N is a square the function returns theta_a,b. If N is not a square the function returns q_x. }
E:=Str`E;
FullEnd(Str);
a1:=Coefficients(E)[1];
a2:=Coefficients(E)[2];
a3:=Coefficients(E)[3];
a4:=Coefficients(E)[4];
a6:=Coefficients(E)[5];
B:=Str`B;
indepB:=Str`indepB;
indep:=Str`indep;
basisB:=Str`basisB;
basis:=Str`basis;
r:=#fij;
f_i:=fij[r];
f:=&+f_i;
FB:=Str`FB;
k:=BaseField(E);
p:=Characteristic(k);
zetaN:=PrimitiveElement(k)^((p^Degree(k)-1) div N);
A:=Matrix([Coordinates(a): a in basisB]);
lTorsDictionary:=lTorsDict(E,N);
P1:=lTorsDictionary[1];
P2:=lTorsDictionary[2];
Weil:=Log(WeilPairing(P1,P2,N)) div Log(zetaN);
lTorsSort:=lTorsDictionary[3];
indeces:=lTorsDictionary[4];
dict:=lTorsDictionary[5];
RepN:= lTorsRep(E, basis, N, lTorsDictionary);
fZ:=Solution(A,BlockMatrix(g,1, [Matrix([Coordinates(f[mu,nu]): mu in [1..g]]): nu in [1..g]]));
fZN:=BlockMatrix(g,g, [&+[RepN[mu]*fZ[nu,mu]: mu in [1..4] ]: nu in [1..g^2]]);
fZN:=Matrix(Integers(),fZN);
Pair:=DiagonalJoin([Matrix([[0,Weil],[-Weil,0]]): i in [1..g]])*fZN;
T:=HyperbolicDec(N,Pair,g);
Pi:= [[T[2*mu+1, 2*i-1]*P1+T[2*mu+2,2*i-1]*P2: mu in [0..g-1]]: i in [1..g]];
Qi:= [[T[2*mu+1, 2*i]*P1+T[2*mu+2,2*i]*P2: mu in [0..g-1]]: i in [1..g]];
Pi2:= [[Pi[i][mu]/2: mu in [1..g]]: i in [1..g]];
Qi2:= [[Qi[i][mu]/2: mu in [1..g]]: i in [1..g]];




RepTwo:= [Matrix(Integers(2), RepN[mu]): mu in [1..4]];
fiZ2:=[[BlockMatrix(g,g, [[&+[RepTwo[xi]*Solution(A,Matrix( [Coordinates(fij[j][i][mu,nu])]))[1,xi]: xi in [1..4] ]: nu in [1..g]]: mu in [1..g]]): i in [1..g]]: j in [1..r]];

X:=Matrix([RemoveZeroRows(fiZ2[r][i])[1]:i in [1..g]]);
v_:=Solution(Transpose(X),Vector([quo<Integers()|2>|1: i in [1..g]]));
v_:=Vector([GF(2)| v_[i]: i in [1..2*g]]);
Q:=[ZeroMatrix(GF(2),2*g,2*g): j in [1..r]];
for j:=1 to r do
for nu:=1 to 2*g do
	  Q[j][nu,nu]:=GF(2)!g+&+[boolGF2(Matrix(Transpose(fiZ2[j][i])[nu]) eq 0): i in [1..g]];
end for;
end for;
for j:=1 to r do
for mu:=1 to 2*g do
	 for nu:=mu+1 to 2*g do
		   //Is this correct for odd g?
		   Q[j][mu,nu]:=GF(2)!g+Q[j][mu,mu]+Q[j][nu,nu]+&+[boolGF2(Matrix(Transpose(fiZ2[j][i])[mu]+Transpose(fiZ2[j][i])[nu]) eq 0): i in [1..g]];
         end for;
end for;
end for;
Q_:=Q[r];

d:=[Matrix([[Q[j][i,i]+Q_[i,i]: i in [1..2*g]]]): j in [1..r-1]];
v:=Flat([[Vector(Solution(Q[j]+Transpose(Q[j]),d[j])): j in [1..r-1]], [v_]]);
Trans:=[[E!lTorsSort[dict[(N div 2)*Integers()!(v[j][2*i+1])+1, (N div 2)*Integers()!(v[j][2*i+2])+1]]: i in [0..g-1]]: j in [1..r]];
rat:=AuxillaryRatFun(Str, fij, [Pi, Pi2,Qi, Qi2],Trans, N, g);
auxThetaPi:=rat[1][1];
auxThetaQi:=rat[1][2];
Eg:=rat[4];
degNumO:=rat[5];
AEg:=CoordinateRing(Eg);
KEg:=FieldOfFractions(AEg);
AA2g:=CoordinateRing(Ambient(Eg));
L:=Parent(param[1]);
EgL:=BaseChange(Eg,L);
KEgL:=FieldOfFractions(CoordinateRing(EgL));
AA2gL:=CoordinateRing(Ambient(EgL));
homo:=hom<KEg-> KEgL | [KEgL.i: i in [1..2*g]]>;

s0:=H0half(Str,fij, param,  rat[2], rat[3], degNumO, g, KEgL, EgL);

if IsSquare(N) then
//In the case N square there is no translation
v_PQ:=v_*Matrix(GF(2),T)^(-1);
v_P:=SequenceToInteger([Integers()!v_PQ[2*i-1]: i in [1..g]],2);
v_Q:=SequenceToInteger([Integers()!v_PQ[2*i]: i in [1..g]],2);

def:= Vector([(Transpose(T)*Q_*T)[j,j]: j in [1..2*g]])*DiagonalJoin([Matrix(GF(2), [[0,1],[1,0]]): i in [1..g]]);
defP:=SequenceToInteger([Integers()!def[2*i-1]: i in [1..g]],2);
defQ:=SequenceToInteger([Integers()!def[2*i]: i in [1..g]],2);
auxThetaStand:=rat[1][3][1];
l:=Integers()!Sqrt(N);
zetal:=zetaN^l;
//Uses l^g operations in the Theta group. This is optimal.
S:=[[]: i in [1..l^g]];
//Pullback of s0 along multiplication by l
ls0:=PullbackMult(Str, l, AA2gL!Numerator(s0), AA2gL!Denominator(s0), KEgL, g)*homo(auxThetaStand);
S[1][1]:=TwoTorsTrans(Str, Trans[r], AA2gL!Numerator(ls0), AA2gL!Denominator(ls0), KEgL, g);
for i:=1 to l^g-1 do
       n:=Ilog(l,i);
       S[1][i+1]:= homo(auxThetaPi[n+1])*GenTrans(Str, Pi[n+1], AA2gL!Numerator(S[1][i-l^n+1]),AA2gL!Denominator(S[1][i-l^n+1]), KEgL, g);
      
end for;
for i:=1 to l^g-1 do
       n:=Ilog(l,i);
       for j:=1 to l^g do
	     S[i+1][j]:=homo(auxThetaQi[n+1])*GenTrans(Str, Qi[n+1], AA2gL!Numerator(S[i-l^n+1][j]), AA2gL!Denominator(S[i-l^n+1][j]), KEgL, g);
       end for;
end for;
b:=[[eval0(S[i][j], g): i in [1..l^g]]: j in [1..l^g]];
//Undo translation by Trans[r]:
b:=[[zetal^&+[Intseq(i,l,g)[nu]*Intseq(v_Q,2,g)[nu]: nu in [1..g]]*zetal^&+[Intseq(j,l,g)[nu]*Intseq(v_P,2,g)[nu]: nu in [1..g]]*b[i][j]: i in [1..l^g]]: j in [1..l^g]];
ret:=[b[1+&+[((Intseq(i div l^g,l,g)[nu]+(l div 2)*Intseq(defQ,2,g)[nu]) mod l)*l^(nu-1): nu in [1..g]]][1+&+[((Intseq(i mod l^g,l,g)[nu]+(l div 2)*Intseq(defP,2,g)[nu]) mod l)*l^(nu-1): nu in [1..g]]]: i in [0..l^(2*g)-1]];
return ret;


 else
   def:= Vector([(Transpose(T)*(Q_+ DiagonalMatrix([(v_*(Q_+Transpose(Q_)))[i]: i in [1..2*g]]))*T)[j,j]: j in [1..2*g]])*DiagonalJoin([Matrix(GF(2), [[0,1],[1,0]]): i in [1..g]]);
defP:=SequenceToInteger([Integers()!def[2*i-1]: i in [1..g]],2);
defQ:=SequenceToInteger([Integers()!def[2*i]: i in [1..g]],2);
S:=[[]: i in [1..N^g]];
//Uses 2^(2g) operations in the Theta group. It would also be possible with 2^g+g or even less.
S[1][1]:=TwoTorsTrans(Str, Trans[r], AA2gL!Numerator(s0), AA2gL!Denominator(s0), KEgL, g)^N;
for i:=1 to N^g-1 do
       n:=Ilog(N,i);
       S[1][i+1]:= homo(auxThetaPi[n+1])*GenTrans(Str, Pi[n+1], AA2gL!Numerator(S[1][i-N^n+1]),AA2gL!Denominator(S[1][i-N^n+1]), KEgL, g);
       
end for;
for i:=1 to N^g-1 do
       n:=Ilog(N,i);
       for j:=1 to N^g do
	     S[i+1][j]:=homo(auxThetaQi[n+1])*GenTrans(Str, Qi[n+1], AA2gL!Numerator(S[i-N^n+1][j]), AA2gL!Denominator(S[i-N^n+1][j]), KEgL, g);
       end for;
end for;
b:=[[eval0(S[i][j], g): i in [1..N^g]]: j in [1..N^g]];
print #[a: a in Flat(b)| a eq 0];
X:=Matrix([[L|zetaN^(Matrix([Intseq(i,N,g)])*Transpose(Matrix([Intseq(j,N,g)])))[1,1] : i in [0..N^g-1]]: j in [0..N^g-1]]);
bX:=[Vector(b[i])*X: i in [1..N^g]];
bXneq0:=&cat[[ [Intseq(i-1,N,g)[nu] - Intseq(j-1,N,g)[nu]: nu in [1..g]]: i in [1..N^g]| bX[i][j] ne 0]: j in [1..N^g]];
ind:=bXneq0[1];
a:=[bX[i][&+[(ind[nu] mod N)*N^(nu-1): nu in [1..g]]+1]: i in [1..N^g]];
q:=[bX[i][&+[((ind[nu] + Intseq(i-1,N,g)[nu]) mod N)*N^(nu-1): nu in [1..g]]+1]: i in [1..N^g]];
ret:=[(-1)^&+[Intseq(i,N,g)[nu]*Intseq(defQ,2,g)[nu]: nu in [1..g]]   *q[&+[((Intseq(i,N,g)[nu]+(N div 2)*Intseq(defP,2,g)[nu]) mod N)*N^(nu-1): nu in [1..g]]  +1]: i in [0..N^g-1]];
return ret;
end if;
end intrinsic;

intrinsic ThetaNullMultiParam(Str::ssEllCurvEndStr, fij::SeqEnum,param::SeqEnum,N::RngIntElt, g::RngIntElt)->SeqEnum
{Same as ThetaNull but allows multiple parameters as a list. }
E:=Str`E;
FullEnd(Str);
a1:=Coefficients(E)[1];
a2:=Coefficients(E)[2];
a3:=Coefficients(E)[3];
a4:=Coefficients(E)[4];
a6:=Coefficients(E)[5];
B:=Str`B;
indepB:=Str`indepB;
indep:=Str`indep;
basisB:=Str`basisB;
basis:=Str`basis;
r:=#fij;
s:=#param;
f_i:=fij[r];
f:=&+f_i;
FB:=Str`FB;
k:=BaseField(E);
p:=Characteristic(k);
zetaN:=PrimitiveElement(k)^((p^Degree(k)-1) div N);
A:=Matrix([Coordinates(a): a in basisB]);
lTorsDictionary:=lTorsDict(E,N);
P1:=lTorsDictionary[1];
P2:=lTorsDictionary[2];
Weil:=Log(WeilPairing(P1,P2,N)) div Log(zetaN);
lTorsSort:=lTorsDictionary[3];
indeces:=lTorsDictionary[4];
dict:=lTorsDictionary[5];
RepN:= lTorsRep(E, basis, N, lTorsDictionary);
fZ:=Solution(A,BlockMatrix(g,1, [Matrix([Coordinates(f[mu,nu]): mu in [1..g]]): nu in [1..g]]));
fZN:=BlockMatrix(g,g, [&+[RepN[mu]*fZ[nu,mu]: mu in [1..4] ]: nu in [1..g^2]]);
fZN:=Matrix(Integers(),fZN);
Pair:=DiagonalJoin([Matrix([[0,Weil],[-Weil,0]]): i in [1..g]])*fZN;
T:=HyperbolicDec(N,Pair,g);
Pi:= [[T[2*mu+1, 2*i-1]*P1+T[2*mu+2,2*i-1]*P2: mu in [0..g-1]]: i in [1..g]];
Qi:= [[T[2*mu+1, 2*i]*P1+T[2*mu+2,2*i]*P2: mu in [0..g-1]]: i in [1..g]];
Pi2:= [[Pi[i][mu]/2: mu in [1..g]]: i in [1..g]];
Qi2:= [[Qi[i][mu]/2: mu in [1..g]]: i in [1..g]];




RepTwo:= [Matrix(Integers(2), RepN[mu]): mu in [1..4]];
fiZ2:=[[BlockMatrix(g,g, [[&+[RepTwo[xi]*Solution(A,Matrix( [Coordinates(fij[j][i][mu,nu])]))[1,xi]: xi in [1..4] ]: nu in [1..g]]: mu in [1..g]]): i in [1..g]]: j in [1..r]];

X:=Matrix([RemoveZeroRows(fiZ2[r][i])[1]:i in [1..g]]);
v_:=Solution(Transpose(X),Vector([quo<Integers()|2>|1: i in [1..g]]));
v_:=Vector([GF(2)| v_[i]: i in [1..2*g]]);
Q:=[ZeroMatrix(GF(2),2*g,2*g): j in [1..r]];
for j:=1 to r do
for nu:=1 to 2*g do
	  Q[j][nu,nu]:=GF(2)!g+&+[boolGF2(Matrix(Transpose(fiZ2[j][i])[nu]) eq 0): i in [1..g]];
end for;
end for;
for j:=1 to r do
for mu:=1 to 2*g do
	 for nu:=mu+1 to 2*g do
		   //Is this correct for odd g?
		   Q[j][mu,nu]:=GF(2)!g+Q[j][mu,mu]+Q[j][nu,nu]+&+[boolGF2(Matrix(Transpose(fiZ2[j][i])[mu]+Transpose(fiZ2[j][i])[nu]) eq 0): i in [1..g]];
         end for;
end for;
end for;
Q_:=Q[r];

d:=[Matrix([[Q[j][i,i]+Q_[i,i]: i in [1..2*g]]]): j in [1..r-1]];
v:=Flat([[Vector(Solution(Q[j]+Transpose(Q[j]),d[j])): j in [1..r-1]], [v_]]);
Trans:=[[E!lTorsSort[dict[(N div 2)*Integers()!(v[j][2*i+1])+1, (N div 2)*Integers()!(v[j][2*i+2])+1]]: i in [0..g-1]]: j in [1..r]];
rat:=AuxillaryRatFun(Str, fij, [Pi, Pi2,Qi, Qi2],Trans, N, g);
auxThetaPi:=rat[1][1];
auxThetaQi:=rat[1][2];
Eg:=rat[4];
degNumO:=rat[5];
AEg:=CoordinateRing(Eg);
KEg:=FieldOfFractions(AEg);
AA2g:=CoordinateRing(Ambient(Eg));
L:=Parent(param[1][1]);
EgL:=BaseChange(Eg,L);
KEgL:=FieldOfFractions(CoordinateRing(EgL));
AA2gL:=CoordinateRing(Ambient(EgL));
homo:=hom<KEg-> KEgL | [KEgL.i: i in [1..2*g]]>;
s0:=[H0half(Str,fij, param[xi],  rat[2], rat[3], degNumO, g, KEgL, EgL): xi in [1..s] ];

if IsSquare(N) then
//In the case N square there is no translation
v_PQ:=v_*Matrix(GF(2),T)^(-1);
v_P:=SequenceToInteger([Integers()!v_PQ[2*i-1]: i in [1..g]],2);
v_Q:=SequenceToInteger([Integers()!v_PQ[2*i]: i in [1..g]],2);

def:= Vector([(Transpose(T)*Q_*T)[j,j]: j in [1..2*g]])*DiagonalJoin([Matrix(GF(2), [[0,1],[1,0]]): i in [1..g]]);
defP:=SequenceToInteger([Integers()!def[2*i-1]: i in [1..g]],2);
defQ:=SequenceToInteger([Integers()!def[2*i]: i in [1..g]],2);
auxThetaStand:=rat[1][3][1];
l:=Integers()!Sqrt(N);
zetal:=zetaN^l;
//Uses l^g operations in the Theta group. This is optimal.
S:=[[]: i in [1..l^g]];
//Pullback of s0 along multiplication by l
ls0:=[PullbackMult(Str, l, AA2gL!Numerator(s0[xi]), AA2gL!Denominator(s0[xi]), KEgL, g)*homo(auxThetaStand) : xi in [1..s]];
S[1][1]:=[TwoTorsTrans(Str, Trans[r], AA2gL!Numerator(ls0[xi]), AA2gL!Denominator(ls0[xi]), KEgL, g): xi in [1..s]];
for i:=1 to l^g-1 do
       n:=Ilog(l,i);
S[1][i+1]:= [homo(auxThetaPi[n+1])*GenTrans(Str, Pi[n+1], AA2gL!Numerator(S[1][i-l^n+1][xi]),AA2gL!Denominator(S[1][i-l^n+1][xi]), KEgL, g): xi in [1..s]];
      
end for;
for i:=1 to l^g-1 do
       n:=Ilog(l,i);
       for j:=1 to l^g do
		S[i+1][j]:=[homo(auxThetaQi[n+1])*GenTrans(Str, Qi[n+1], AA2gL!Numerator(S[i-l^n+1][j][xi]), AA2gL!Denominator(S[i-l^n+1][j][xi]), KEgL, g): xi in [1..s]];
       end for;
end for;
b:=[[[eval0(S[i][j][xi], g): i in [1..l^g]]: j in [1..l^g]]: xi in [1..s]];
//Undo translation by Trans[r]:
b:=[[[zetal^&+[Intseq(i,l,g)[nu]*Intseq(v_Q,2,g)[nu]: nu in [1..g]]*zetal^&+[Intseq(j,l,g)[nu]*Intseq(v_P,2,g)[nu]: nu in [1..g]]*b[xi][i][j]: i in [1..l^g]]: j in [1..l^g]]: xi in [1..s]];
ret:=[[b[xi][1+&+[((Intseq(i div l^g,l,g)[nu]+(l div 2)*Intseq(defQ,2,g)[nu]) mod l)*l^(nu-1): nu in [1..g]]][1+&+[((Intseq(i mod l^g,l,g)[nu]+(l div 2)*Intseq(defP,2,g)[nu]) mod l)*l^(nu-1): nu in [1..g]]]: i in [0..l^(2*g)-1]]: xi in [1..s]];
return ret;


 else
   def:= Vector([(Transpose(T)*(Q_+ DiagonalMatrix([(v_*(Q_+Transpose(Q_)))[i]: i in [1..2*g]]))*T)[j,j]: j in [1..2*g]])*DiagonalJoin([Matrix(GF(2), [[0,1],[1,0]]): i in [1..g]]);
defP:=SequenceToInteger([Integers()!def[2*i-1]: i in [1..g]],2);
defQ:=SequenceToInteger([Integers()!def[2*i]: i in [1..g]],2);
S:=[[]: i in [1..N^g]];
//Uses 2^(2g) operations in the Theta group. It would also be possible with 2^g+g or even less.
S[1][1]:=TwoTorsTrans(Str, Trans[r], AA2gL!Numerator(s0), AA2gL!Denominator(s0), KEgL, g)^N;
for i:=1 to N^g-1 do
       n:=Ilog(N,i);
       S[1][i+1]:= homo(auxThetaPi[n+1])*GenTrans(Str, Pi[n+1], AA2gL!Numerator(S[1][i-N^n+1]),AA2gL!Denominator(S[1][i-N^n+1]), KEgL, g);
       
end for;
for i:=1 to N^g-1 do
       n:=Ilog(N,i);
       for j:=1 to N^g do
	     S[i+1][j]:=homo(auxThetaQi[n+1])*GenTrans(Str, Qi[n+1], AA2gL!Numerator(S[i-N^n+1][j]), AA2gL!Denominator(S[i-N^n+1][j]), KEgL, g);
       end for;
end for;
b:=[[eval0(S[i][j], g): i in [1..N^g]]: j in [1..N^g]];
print #[a: a in Flat(b)| a eq 0];
X:=Matrix([[L|zetaN^(Matrix([Intseq(i,N,g)])*Transpose(Matrix([Intseq(j,N,g)])))[1,1] : i in [0..N^g-1]]: j in [0..N^g-1]]);
bX:=[Vector(b[i])*X: i in [1..N^g]];
bXneq0:=&cat[[ [Intseq(i-1,N,g)[nu] - Intseq(j-1,N,g)[nu]: nu in [1..g]]: i in [1..N^g]| bX[i][j] ne 0]: j in [1..N^g]];
ind:=bXneq0[1];
a:=[bX[i][&+[(ind[nu] mod N)*N^(nu-1): nu in [1..g]]+1]: i in [1..N^g]];
q:=[bX[i][&+[((ind[nu] + Intseq(i-1,N,g)[nu]) mod N)*N^(nu-1): nu in [1..g]]+1]: i in [1..N^g]];
ret:=[(-1)^&+[Intseq(i,N,g)[nu]*Intseq(defQ,2,g)[nu]: nu in [1..g]]   *q[&+[((Intseq(i,N,g)[nu]+(N div 2)*Intseq(defP,2,g)[nu]) mod N)*N^(nu-1): nu in [1..g]]  +1]: i in [0..N^g-1]];
return ret;
end if;
end intrinsic;


intrinsic CurveFromThetaNull(q::SeqEnum, g::RngIntElt)-> Crv
{reconstructs a curve from the Theta-Nullvalue}
print q;
k:=Parent(q[1]);
if g eq 2 and q[1] ne 0 then 
     R:=PolynomialRing(k);
     X:=Matrix([[(-1)^&+Intseq(BitwiseAnd(i,p[1]),2)*q[BitwiseXor(i,p[2])+1]: i in [0..3]]: p in [[1,1],[3,1],[1,3],[2,2],[3,2],[2,3]]]);
     Y:=Matrix([[X[i,2]^2,X[i,2]*X[i,3],X[i,2]*X[i,4],X[i,3]^2,X[i,3]*X[i,4],X[i,4]^2]: i in [1..6]] );
     ker:= Basis(Kernel(Transpose(Y)))[1];
     f:=&*Flat([[R.1-(X[1,4]*X[i,2]-X[1,2]*X[i,4])/(X[1,2]*X[i,3]-X[1,3]*X[i,2]): i in [2..6]], [R.1-(X[1,2]*ker[2]+2*X[1,3]*ker[4]+X[1,4]*ker[5])/(X[1,2]*ker[3]+X[1,3]*ker[5]+2*X[1,4]*ker[6])]]);
C:=HyperellipticCurve(f);
return SimplifiedModel(C);
 elif g eq 3 then
I:=Sqrt(k!(-1));
/*theta:=[[(-1)^(-(Matrix([Intseq(a,2,g)])*Transpose(Matrix([Intseq(b,2,g)])))[1,1] div 2) * &+[ I^(&+[(Intseq(a,2,g)[nu]+2*Intseq(c,2,g)[nu])*Intseq(b,2,g)[nu]: nu in [1..g] ])   *q[&+[(Intseq(a,2,g)[nu]+2*Intseq(c,2,g)[nu])*4^(nu-1): nu in [1..g]] + 1]  : c in [0..2^g-1]] : a in [0..2^g-1]]: b in [0..2^g-1]];
  theta:=[theta[(i div 2^g) mod 2^g +1][(i mod 2^g)+1]: i in [1..4^g]];*/
theta:=[[(-1)^(-(Matrix([Intseq(a,2,g)])*Transpose(Matrix([Intseq(b,2,g)])))[1,1] div 2)   *q[1+a+b*2^g] : a in [0..2^g-1]]: b in [0..2^g-1]];
theta:=[theta[(i div 2^g) mod 2^g +1][(i mod 2^g)+1]: i in [1..4^g]];
if #[0: i in [1..4^g]| theta[i] eq 0] eq 28 then
a1:=I*theta[33]*theta[5]/(theta[40]*theta[12]);
a2:=I*theta[21]*theta[49]/(theta[28]*theta[56]);
a3:=I*theta[7]*theta[35]/(theta[14]*theta[42]);
ap1:=I*theta[5]*theta[54]/(theta[27]*theta[40]);
ap2:=I*theta[49]*theta[2]/(theta[47]*theta[28]);
ap3:=I*theta[35]*theta[16]/(theta[61]*theta[14]);
as1:=-theta[54]*theta[33]/(theta[12]*theta[27]);
as2:=theta[2]*theta[21]/(theta[56]*theta[47]);
as3:=theta[16]*theta[7]/(theta[42]*theta[61]);
P<x1,x2,x3>:=ProjectiveSpace(k,2);
k:=1;kp:=1;ks:=1;
M:=Matrix([[1,1,1],[k*a1,k*a2,k*a3],[kp*ap1,kp*ap2,kp*ap3]]);
Mb:=Matrix([[1,1,1],[1/a1,1/a2,1/a3],[1/ap1,1/ap2,1/ap3]]);
U:=-Mb^(-1)*M;
u1:=U[1];
u2:=U[2];
u3:=U[3];
u1:=u1[1]*x1+u1[2]*x2+u1[3]*x3;
u2:=u2[1]*x1+u2[2]*x2+u2[3]*x3;
u3:=u3[1]*x1+u3[2]*x2+u3[3]*x3;
f:= (x1*u1+x2*u2-x3*u3)^2-4*x1*u1*x2*u2;
C:=Curve(Scheme(P,f));

return C;

elif #[0: i in [1..4^g]| theta[i] eq 0] eq 29 then
rosens:=RosenhainInvariantsFromThetaSquares([theta[i]^2: i in [1..4^g]]);
     R<x>:=PolynomialRing(k);
print rosens;
f:=x*(x-1)*&*[x-rosens[i]: i in [1..5]];
C:=HyperellipticCurve(f);
return C;
end if;

 else
      print "Reconstruction of curve not implemented yet";
end if;
end intrinsic;



intrinsic Splitting(Str::ssEllCurvEndStr, fij::SeqEnum, g::RngIntElt) -> MtrxWitt
{Computes a splitting of M(H_1)+...+M(H_r) -> M(ker(eta)) or outputs an error message if it does not exist}
FullEnd(Str);
r:=#fij;
f:=&+(fij[1]);
B:=Str`B;
indepB:=Str`indepB;
basisB:=Str`basisB;
FB:=Str`FB;
p:=Str`p;
A:=Matrix([Coordinates(a): a in basisB]);
fiZ:=[[BlockMatrix(g,1,[Transpose(Solution(A,BlockMatrix(g,1,[Matrix([Coordinates(1/ FB^(Min(Flat([[padicVal(fij[j][i][mu,nu],p): mu in [1..g]]: nu in [1..g]])) div 2)*fij[j][i][mu,nu]*basisB[xi]): xi in [1..4]]): mu in [1..g]]))): nu in [1..g]]) : i in [1..g]]  : j in [1..r]];
fiZ:=[[Matrix([[Integers()!fiZ[j][i][mu][nu]: nu in [1..4*g]]: mu in [1..4*g]]) : i in [1..g]]  : j in [1..r]];
//Brauche M(ker(eta)) als Z-Modul und die Abbildung fij auf M(ker(eta)).
Fgm1:=Transpose(Solution(A,Matrix([Coordinates(FB^(g-1)*b): b in basisB])));
Fgm1:=Matrix([[Integers()!Fgm1[mu][nu]: nu in [1..4]]: mu in [1..4]]);
Xi:=[VerticalJoin(HorizontalJoin([Transpose(fiZ[j][i]): i in [1..g]]), DiagonalJoin([Transpose(Fgm1): nu in [1..g^2]])): j in [1..r]];
MHi:=[[[Basis(Kernel(Xi[j]))[i][nu]: nu in [1..4*g]]: i in [1..4*g]]: j in [1..r]];
phi:=VerticalJoin(Flat([[Matrix(MHi[j]): j in [1..r]],[ DiagonalJoin([Transpose(Fgm1): nu in [1..g]])]]));
LHS:=DiagonalJoin([Solution(A,Matrix([Coordinates(B!1)])): i in [1..g]]);
LHS:=Matrix([[Integers()!LHS[mu,nu]: nu in [1..4*g]]: mu in [1..g]]);
sol:= Solution(phi, LHS);
split:=VerticalJoin([ Transpose(Matrix([[sol[mu,4*g*(j-1)+nu]: nu in [1..4*g]]: mu in [1..g]])*Matrix(MHi[j])) : j in [1..r]]);
W:=WittRing(GF(p^2), g div 2);
endPadic:=EndpAdic(Str, W)`entries;
retpre:=[[  &+[W!(Integers()!split[4*((mu-1) div 2)+nu,xi]) * endPadic[(mu-1) mod 2+1][nu] : nu in [1..4]]: xi in [1..g]]: mu in [1..2*g*r]];
retpreF:=&cat[[[-W!p*FrobeniusImage(retpre[2*mu][nu ]): nu in [1..g]   ] , [FrobeniusImage(retpre[2*mu-1][nu ]): nu in [1..g]] ]: mu in [1..g*r]];
ret:=Matrix([&cat[[retpre[mu][nu], retpreF[mu][nu]]: nu in [1..g]]: mu in [1..2*g*r]]);
return ret;
end intrinsic;

intrinsic boolGF2(bool::BoolElt) -> FldFinElt
{Converts a boolean variable to GF(2)}
if bool then
     return GF(2)!1;
else
     return GF(2)!0;
end if;
end intrinsic;
