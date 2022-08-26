declare type MtrxWitt;
declare attributes MtrxWitt: entries, m,n;

/* This file defines a new data type of a matrix with entries in a ring of witt vectors of finite length

One cannot use the system defined matrix type because the system defined rings of witt vectors are not an instance of the category of rings.
 */

intrinsic Print(A::MtrxWitt)
{Print A}
printf "%o", A`entries;
end intrinsic;


intrinsic Matrix(entries::SeqEnum[SeqEnum[RngWittElt]])-> MtrxWitt
{Creates a matrix with given entries}
require forall{a: a in entries | #a eq #entries[1]}: "Sequences do not have same length";
A:=New(MtrxWitt);
A`entries:=entries;
A`m:=#entries;
A`n:=#entries[1];
return A;
end intrinsic;

intrinsic Sum(mat::SeqEnum[MtrxWitt])-> MtrxWitt
{returns the sum of the matrices}
require forall{A : A in mat | (A`m eq mat[1]`m) and (A`n eq mat[1]`n)}: "Dimensions do not match";
m:=mat[1]`m;
n:=mat[1]`n;
return Matrix([[ &+[A`entries[i][j]: A in mat]: j in [1..n]]: i in [1..m]] );
end intrinsic;

intrinsic Transpose(A::MtrxWitt)-> MtrxWitt
{returns the transpose matrix}
m:=A`m;
n:=A`n;
return Matrix([[A`entries[i][j] : i in [1..m]]: j in [1..n]] );
end intrinsic;

intrinsic Product(mat::SeqEnum[MtrxWitt])-> MtrxWitt
{returns the product of the matrices}
len:=#mat;
if len eq 1 then
     return mat[1];
else
  return Product(Flat([[Mult(mat[1],mat[2])], [mat[i]: i in [3..len]]]));
end if; 

end intrinsic;

intrinsic Mult(A::MtrxWitt, B::MtrxWitt) -> MtrxWitt
{Multiply two matrices}
require A`n eq B`m: "Dimensions do not match";
m:=A`m;
n:=B`n;
return Matrix([[ &+[A`entries[i][j]*B`entries[j][k] : j in [1..A`n]]: k in [1..n]]: i in [1..m]] );
end intrinsic;


intrinsic VerticalJoin(mat::SeqEnum[MtrxWitt])-> MtrxWitt
{The vertical join of a sequence of matrices}
return Matrix(&cat [A`entries: A in mat]);
end intrinsic;

intrinsic BlockMatrix(m::RngIntElt, n::RngIntElt, blocks::SeqEnum[MtrxWitt])-> MtrxWitt
{The vertical join of a sequence of matrices}
return VerticalJoin([Transpose(VerticalJoin([Transpose(blocks[j]): j in [1+i*m..(i+1)*m]])): i in [0..n-1]]);
end intrinsic;

intrinsic ZeroMatrix(W::RngWitt, m::RngIntElt, n::RngIntElt) -> MtrxWitt
{Zero matrix with m rows and n columns}
return Matrix([[W!0: i in [1..n]]: j in [1..m]]);
end intrinsic;
