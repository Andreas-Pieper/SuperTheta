declare type ssEllCurvEndStr;
declare attributes ssEllCurvEndStr: p, E,ECMlift, B, indep, indepB, A, Tan, basis, basisB, FB, genCMB, FrobMat;

/* This file defines a new data type of a supersingular elliptic curve with an endomorphism structure. Here

E is a supersingular elliptic curve defined over GF(p) with base field containing GF(p^2).
ECMlift is a CM curve over QQ lifting E

B is a quaternion algebra isomorphic to End^0(E)
indep is a tuple of 4 Z-linearly independent elements of End(E) represented as isogenies E -> E.
indepB is a tuple of 4 Z-linearly independent elements of B, such that the map indep[i] -> indepB[i] defines an isomorphism of Q-algebras End^0(E) -> B
A is the change of basis matrix from indepB to the internal basis of B
Tan describes the action on the tangent space of the elements in indep
basis is a Z-basis of End(E) represented as isogenies E -> E
basisB the image of basis under the above isomorphism End^0(E) -> B
FB is geometric p-Frobenius
genCMB corresponds to a  generator of the image of End(ECMlift)-> End(E)
FrobeniusMatrix is the matrix of frobenius on the deRham cohomology of ECMlift
 */

intrinsic Print(X::ssEllCurvEndStr)
{Print X}
printf "Endomorphism structure on the supersingular elliptic curve %o", X`E;
end intrinsic;


intrinsic ssEllipticCurveEndStr(E::CrvEll, ECMlift::CrvEll, B::AlgQuat, indep::SeqEnum, indepB::SeqEnum, CMframe::SeqEnum)-> ssEllCurvEndStr
{Creates an elliptic curve with the given endomorphism structure.}
require forall{phi: phi in indep | ISA(Type(phi), Map)}:"Tuple entries in 3rd argument are not all isogenies";
require forall{r: r in indepB | Parent(r) eq B}: "Tuple entries in 4th argument are not all elements of B";
Str:=New(ssEllCurvEndStr);
Str`E:=E;
Str`ECMlift:=ECMlift;
Str`B:=B;
Str`indep:=indep;
Str`indepB:=indepB;
Str`FB:=CMframe[1];
Str`genCMB:=CMframe[2];
Str`A:=Matrix([Coordinates(a): a in indepB]);
k:=BaseField(E);
if #TorsionSubgroupScheme(E,4)(k) ne 16 then
     print "Error: 4 torsion needs to be defined over ground field";
end if;
Str`p:=Characteristic(k);
R<eps>:=quo<PolynomialRing(k)|$.1^2>;
/*The formula in the next line uses that the k[eps]/(eps^2)-valued point (-eps,1,0) generates the tangent space at 0 of E. 
Caution: If the rational functions defining the maps in indep are not defined at 0, there is a division by zero.*/
Str`Tan:=[-MonomialCoefficient(Evaluate(DefiningEquations(indep[i])[1],[-eps,1,0]),eps)/MonomialCoefficient(Evaluate(DefiningEquations(indep[i])[2],[-eps,1,0]),1): i in [1..4]];
return Str;
end intrinsic;

intrinsic Endomorphism(Str::ssEllCurvEndStr,r::AlgQuatElt) -> Map
{Returns the endomorphism corresponding to the element r in B}
require Parent(r) eq Str`B: "2nd argument not an element of B";
K<x,y>:=FunctionField(Str`E);
E_:=BaseChange(Str`E,K);
b:=Coordinates(Str`B,r);
x:=Solution(Str`A,Matrix([b]));
if &and[IsCoercible(Integers(),x[1][i]): i in [1..4]] then
     return asMap(Str`E, &+[Integers()![x[1][i]] * asPoint(Str`indep[i], E_): i in [1..4]]);
else
    FullEnd(Str);
    A:=Matrix([Coordinates(a): a in Str`basisB]);
    x:=Solution(A,Matrix([b]));
    if &and[IsCoercible(Integers(),x[1][i]): i in [1..4]] then
        return asMap(Str`E, &+[Integers()![x[1][i]] * asPoint(Str`basis[i], E_): i in [1..4]]);
    else
        print "Element does not define an endomorphism";
    end if;
end if;
end intrinsic;

intrinsic asPoint(phi::Map, E_::CrvEll, K::Fld) -> PtEll
{Interprets a map E->E1 as a point E1(K(E))}
x:=K.1;
y:=K.2;
P:=E_![Evaluate(DefiningPolynomials(phi)[1],[x,y,1]),Evaluate(DefiningPolynomials(phi)[2],[x,y,1]),Evaluate(DefiningPolynomials(phi)[3],[x,y,1])];
return P;
end intrinsic;

intrinsic asPoint(phi::Map, E_::CrvEll) -> PtEll
{Interprets a map E->E as a point E(K(E))}
K:=BaseField(E_);
x:=K.1;
y:=K.2;
P:=E_![Evaluate(DefiningPolynomials(phi)[1],[x,y,1]),Evaluate(DefiningPolynomials(phi)[2],[x,y,1]),Evaluate(DefiningPolynomials(phi)[3],[x,y,1])];
return P;
end intrinsic;

intrinsic asMap(E1::CrvEll, P::PtEll) -> Map
{Returns the map E->E corresponding to a point in E(K(E))}
return map<E1-> E1 | Coordinates(P)>;
end intrinsic;

intrinsic asMap(E::CrvEll, E1::CrvEll, P::PtEll) -> Map
{Returns the map E->E1 corresponding to a point in E(K(E))}
return map<E-> E1 | Coordinates(P)>;
end intrinsic;

intrinsic ActionOnTangentSpace(Str::ssEllCurvEndStr, r::AlgQuatElt) -> FinFldElt
{returns the scalar alpha such that the endomorphism corresponding to r acts by multiplication by alpha on the tangent space.}
k:=BaseField(Str`E);
b:=Coordinates(Str`B,r);
x:=Solution(Str`A,Matrix([b]));
return &+[k!(x[1][i])*Str`Tan[i]: i in [1..4] ];

end intrinsic;

intrinsic findInSortedList(L::SeqEnum, x::.) ->.
{Binary search algorithm}
  S:=#L;
  up:=#L;
  low:=1;
  mid:=Floor((low+up)/2);
  while L[mid] ne x do
       if L[mid] le x then
            low:=mid;
            mid:=Ceiling((low+up)/2);
       else
            up:=mid;
            mid:=Floor((low+up)/2);
       end if;
       if low eq up and L[mid] ne x then
       end if;
  end while;
  return mid;
end intrinsic;

intrinsic FrobeniusMat(Str::ssEllCurvEndStr, prec::RngIntElt)
{Computes the Matrix of Frobenius}
  if assigned Str`FrobMat then
        return;
   end if;
Str`FrobMat:=FrobeniusMatrix(Str`ECMlift, Str`p: Precision:=prec);
end intrinsic;

intrinsic FullEnd(Str::ssEllCurvEndStr)
{Computes the full endomorphism ring}
if assigned Str`basis and assigned Str`basisB then
     return;
end if;
B:=Str`B;
E:=Str`E;
K<x,y>:=FunctionField(E);
E_:=BaseChange(E,K);
p:=Characteristic(BaseField(E));
indep:=Str`indep;
indepB:=Str`indepB;
A:=Matrix([[Trace(Conjugate(indepB[i])*indepB[j]): i in [1..4]]: j in [1..4]]);
discrd:=IntegerRing()!Sqrt(Abs(Determinant(A)));
ind:=IntegerRing()!(discrd/p);
fac:=Factorization(ind);
//Compute the primes where the order is not maximal
primes:=[f[1]: f in fac];
indepAct:=indep;
indepBAct:=indepB;
new:=[1..4];
lTor:=[];
for l in primes do
      f:=0;
      while IsDivisibleBy(ind, l) do
        	f:=f+1;
//Compute the action of the new endomorphisms on the l-torsion
                lTorNew:=lTorsRep(E,[indepAct[i]: i in new ],l);
                for i in [1..# new] do
                    lTor[new[i]]:=lTorNew[i];
                end for;
		A:=Matrix([[(lTor[i])[Ceiling(j/2), ((j+1) mod 2)+1]: j in [1..4]]: i in [1..4]]);
                ker:=Basis(Kernel(A));
                act:= VerticalJoin(l*IdentityMatrix(IntegerRing(),4),Matrix([[IntegerRing()|v[i]: i in [1..4]]: v in ker] ));
                //Irgendetwas scheint hier falsch zu sein.
                baseNew:=Submatrix(HermiteForm(act),1,1,4,4);
                new:=[ i:i in [1..4]| (baseNew-l*IdentityMatrix(IntegerRing(),4))[i] ne 0];
                indepBdum:=indepBAct;
                indepdum:=indepAct;
//Add the new endomorphisms
                for i in new do
		      indepBdum[i]:=&+[baseNew[i,j]*indepBAct[j]: j in [1..4]]/l;

                 b, P:= IsDivisibleBy((&+[baseNew[i,j] * asPoint(indepAct[j], E_): j in [1..4]]) ,l);
                      if b then
		           map:=asMap(E, P);
                           indepdum[i]:=asMap(E, P - E_!map([0,1,0]));
                      else
                           print "something went wrong";
                           return;
                      end if;
		end for;
                indepBAct:=indepBdum;
                indepAct:=indepdum;
//Compute the index
                ind:=IntegerRing()!(ind*Determinant(baseNew)/(l^4));
      end while;
      new:=[1..4];
end for;
Str`basis:=indepAct;
Str`basisB:=indepBAct;
end intrinsic;


intrinsic lTorsDict(E::CrvEll, l::RngIntElt) -> Tup
{}
ZZl:=quo<Integers()|l>;
lTors,k := PointsOverSplittingField(TorsionSubgroupScheme(E,l));
lTorsSort := Sort([Coordinates(P): P in lTors]);
Ek:=BaseChange(E,k);
i:=1;
while  Order(Ek!lTorsSort[i]) ne l do
	    i:=i+1;
end while;
P1:=Ek!lTorsSort[i];
i:=i+1;
while  not IsLinearlyIndependent(P1, Ek!lTorsSort[i] , l) do
	   i:=i+1;
end while;
P2:= Ek!lTorsSort[i];
indeces:=[];
dict:=ZeroMatrix(Integers(), l);
for i in [0..l-1] do
	for j in [0..l-1] do
	      find:=findInSortedList(lTorsSort,Coordinates(i*P1+j*P2));
	      indeces[find]:=[ZZl|i,j];
              dict[i+1,j+1]:=find;
        end for;
end for;
return <P1,P2,lTorsSort, indeces, dict,k>;
end intrinsic;

  

intrinsic lTorsRep(E::CrvEll, Phi::SeqEnum, l::RngIntElt) -> SeqEnum
{Computes the action of a sequence of endomorphisms on the l-torsion}
ZZl:=quo<Integers()|l>;
lTorsDictionary:=lTorsDict(E,l);
P1:=lTorsDictionary[1];
P2:=lTorsDictionary[2];
lTorsSort:=lTorsDictionary[3];
indeces:=lTorsDictionary[4];
ret:=[Transpose(Matrix([ indeces[findInSortedList(lTorsSort,Coordinates(phi(Coordinates(P1))))], indeces[findInSortedList(lTorsSort,Coordinates(phi(Coordinates(P2))))]])): phi in Phi ];
return ret;
end intrinsic;

intrinsic lTorsRep(E::CrvEll, Phi::SeqEnum, l::RngIntElt, lTorsDictionary::Tup) -> SeqEnum
{Computes the action of a sequence of endomorphisms on the l-torsion}
ZZl:=quo<Integers()|l>;
P1:=lTorsDictionary[1];
P2:=lTorsDictionary[2];
lTorsSort:=lTorsDictionary[3];
indeces:=lTorsDictionary[4];
ret:=[Transpose(Matrix([ indeces[findInSortedList(lTorsSort,Coordinates(phi(P1)))], indeces[findInSortedList(lTorsSort,Coordinates(phi(P2)))]])): phi in Phi ];
return ret;
end intrinsic;


intrinsic Deuring(Str::ssEllCurvEndStr, I::SeqEnum, Minimize::BoolElt)->Tup
{Computes the elliptic curve E_I corresponding to the right ideal with Z-basis I. Also returns an isogeny E-> E_I}
p:=Str`p;
E:=Str`E;
FB:=Str`FB;
q:=Matrix([[Trace(Conjugate(x)*y): y in I]:  x in I]);
if Minimize then
     L:=LatticeWithGram(q^(-1));
     v:=ShortestVectors(L)[1];
     alpha:=Matrix([[Rationals()!Coordinates(ShortestVectors(L)[1])[i]: i in [1..4]]])*q^(-1);
     //Use J. Voight Lemma 15.6.12 to express the inverse ideal of a right ideal in terms of the dual with respect to the trace form. I^{-1}=F I^{#}
     Idum:=[&+[FB*alpha[1,i]*I[i]: i in [1..4]]*I[i]: i in [1..4]];
     I:=Idum;
     N:=Integers()!((p*(alpha*q*Transpose(alpha))[1,1]/(2))*Sqrt((Sqrt(Determinant(q))/p)));
 else
 N:=Integers()!Sqrt((Sqrt(Determinant(q))/p));
end if;
if N eq 1 then
     return <E, IdentityMap(E)> ;
end if;
if not IsDivisibleBy(N,p) then
P1,P2, lTorsSort, indeces, dict,k:=lTorsDict(E, N);
     NTors:=lTorsRep(E, [Endomorphism(Str, r): r in I], N, < P1,P2, lTorsSort, indeces, dict>);
     ind:=Basis( &meet[Kernel(A): A in NTors])[1];
     P:=lTorsSort[dict[Integers()!ind[1]+1, Integers()!ind[2]+1]];
     Ek:=BaseChange(E,k);
     R:=PolynomialRing(k);
     E_I, phi:=IsogenyFromKernel(Ek, &*{(R.1-(n*Ek!P)[1]) : n in [1..N-1]});
return <E_I,phi>;
end if;
end intrinsic;


intrinsic EndpAdic(Str::ssEllCurvEndStr, W::RngWitt)->MtrxWitt
{Computes the Isomorphism O_p with W(F_(p^2))^2 induced by the action of the Endomorphism algebra on the Dieudonne module}
prec:=Length(W);
p:=Str`p;
B:=Str`B;
genCMB:=Str`genCMB;
FB:=Str`FB;
A:=Matrix([Coordinates(a): a in Str`basisB]);
X:=Solution(Matrix([Coordinates(a): a in [B!1, genCMB, FB, FB*genCMB]]),A);
den:=Denominator(X);
R:=quo<Integers()|p^prec>;
XW:=Matrix([[W!(Integers()!(den*X[mu,nu]))*W!(Integers()!(R!(1/den))): nu in [1..4]]: mu in [1..4]]);
if (Trace(genCMB) eq 0 and Norm(genCMB) eq 1) or (Trace(genCMB) eq -1 and Norm(genCMB) eq 1) then
        //Muss man die Wirkung auf dem Tangentialraum nehmen oder das konjugierte?
	zeta:=W!Flat([[ActionOnTangentSpace(Str, genCMB)],[0: i in [1..prec-1]]]);
return Mult(Matrix([[W!1,zeta,W!0,W!0],[W!0,W!0,W!1,zeta]]),Transpose(XW));
else
	  print "Not implemented yet";
end if;

end intrinsic;

intrinsic EndpAdic(Str::ssEllCurvEndStr, W::RngWitt, seq::SeqEnum)->MtrxWitt
{Computes the Isomorphism O_p with W(F_(p^2))^2 induced by the action of the Endomorphism algebra on the Dieudonne module}
prec:=Length(W);
r:=#seq;
p:=Str`p;
B:=Str`B;
genCMB:=Str`genCMB;
FB:=Str`FB;
A:=Matrix([Coordinates(a): a in seq]);
X:=Solution(Matrix([Coordinates(a): a in [B!1, genCMB, FB, FB*genCMB]]),A);
den:=Denominator(X);
R:=quo<Integers()|p^prec>;
XW:=Matrix([[W!(Integers()!(den*X[mu,nu]))*W!(Integers()!(R!(1/den))): nu in [1.. 4]]: mu in [1.. r]]);
if (Trace(genCMB) eq 0 and Norm(genCMB) eq 1) or (Trace(genCMB) eq -1 and Norm(genCMB) eq 1) then
        //Muss man die Wirkung auf dem Tangentialraum nehmen oder das konjugierte?
	zeta:=W!Flat([[ActionOnTangentSpace(Str, genCMB)],[0: i in [1..prec-1]]]);
        return Mult(Matrix([[W!1,zeta,W!0,W!0],[W!0,W!0,W!1,zeta]]),Transpose(XW));
else
	  print "Not implemented yet";
end if;

end intrinsic;


intrinsic CommutatorPairing(Str::ssEllCurvEndStr, f::AlgMatElt, g::RngIntElt) -> MtrxWitt
{Computes the pairing on M(ker(eta)) induced from the commutator pairing}
p:=Str`p;
if IsDivisibleBy(g,2) then
   prec:=g div 2+1;
fprime:=p^(1-(g div 2))*f;
else
   prec:=(g-1) div 2;
fprime:=p^(-((g-1) div 2))*f;
end if;
W:=WittRing(GF(p^2), prec);
endfprime:=VerticalJoin([EndpAdic(Str, W, &cat[[fprime[i,j] ,fprime[i,j]*Str`FB  ] : j in [1..g]]): i in [1..g]]); 
FrobeniusMat(Str, prec);
Weil:= DiagonalJoin([Matrix([[0, -Str`FrobMat[2,1]/p],[Str`FrobMat[2,1]/p, 0]] ): i in [1..g]]);
den:=Denominator(Weil);
R:=quo<Integers()|p^prec>;
WeilW:=Matrix([[W!(Integers()!(den*Weil[mu,nu]))*W!(Integers()!(R!(1/den))): nu in [1..2*g]]: mu in [1..2*g]]);
if IsDivisibleBy(g,2) then
    M:=Mult(WeilW, endfprime);
    W1:=WittRing(GF(p^2), prec-1);
//Since k=F_p^2. Dividing by p in W is given by shifting left and applying frobenius
return Matrix( [[FrobeniusImage(W1!Remove(Eltseq(M`entries[mu][nu]),1)):  nu in [1..2*g]]: mu in [1..2*g]]);
else
    return Mult(WeilW, endfprime);
end if;
end intrinsic;

intrinsic WittSurj(Str::ssEllCurvEndStr, n::RngIntElt)-> RngMPolResElt
{Computes a surjection from the Lubin-Tate group onto the formal group of E with precision p^n}
p:=Str`p;
E:=Str`ECMlift;
LogE:=FormalLog(E:Precision:=p^n);
Pow:=Parent(LogE);
prec:=2*n;
R:=PolynomialRing(Rationals(),n);
I:=Ideal([R.i^(p^n): i in [1..n]]);
Rk:=PolynomialRing(GF(p),n);
Rkquo:=quo<Rk|[$.i^(p^n): i in [1..n]]>;
x:=[R.i: i in [1..n]] cat [R!0: i in [1..prec-n]];
w:=[&+[p^i*NormalForm(x[i+1]^(p^(j-i)),I): i in [0..j]]: j in [0..prec-1]];
y:=&+[(-1/p)^i*w[2*i+1]: i in [0..(prec-1) div 2]];
Wnn:=WittGroup(GF(p),n,n);
wittsurj:=Evaluate(NormalForm( Evaluate(Reverse(LogE), y),I), [Rkquo.i: i in [1..n]]);
hom1:= Evaluate(wittsurj, Wnn`S);
T:=Parent(hom1);
hom2:= Evaluate(FormalGroupLaw(E, 2*p^(n)), [Evaluate(wittsurj, [T.i: i in [1..n]]) , Evaluate(wittsurj, [T.(i+n): i in [1..n]])]);
if hom1 ne hom2 then
print "Error. Not a group homomorphism";
 else 
return wittsurj;
end if;
end intrinsic;
