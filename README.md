# SuperTheta
Magma Code for computing algebraic theta nullvalues of supersingular Abelian varieties.

The spec file needs to be loaded by typing
```
AttachSpec("spec");
```

The file ssEllCurvEndStr.m defines the class `ssEllipticCurveEndStr` of supersingular elliptic curves together with four Z-linearly independent endomorphisms.

An object in this class is constructed via `ssEllipticCurveEndStr(E, ECMlift, B, indep, indepB, CMframe)`

#### Input:

- `E` a supersingular elliptic curve over a field containing F_{p^2}. `E` must be defined over F_p.
- `ECMlift` is a CM lift of E. Currently ECMlift must be defined over Q.
- `B` a quaternion algebra (needs to be isomorphic to End^0(E))
- `indep` is a four element tuple of endomorphisms of `E` (the rational functions describing these endomorphisms must be defined at the origin).
- `indepB` a four element tuple of elements of `B`
- CMframe is a tuple with two entries `[FB, aB]` in `B`. The first entry `FB` is the Frobenius endomorphsim. The second entry `aB` generates the quadratic subfield of `B` obtained from the CM lift.

#### Output:
Creates an object with class `ssEllipticCurveEndStr`. The elliptic curve `E` has an endomorphism structure B-> End^0(E) given by mapping `indepB[i]` to `indep[i]`. `FB` has to map to the geometric Frobenius.

The file ThetaNull.m needs to be attached manually via
```
Attach("ThetaNull.m");
```
In that file we implemented the main algorithm of the paper. It starts with a supersingular elliptic curve E and a positive integer g. Suppose we give a polarization eta on E^g such that there exists a spanning tuple for (E^g, eta) (see Definition 4.1 in the paper). Then the algorithm calculates the algebraic theta nullvalues of the quotient E^g/H for any maximally isotropic subgroup scheme H.

This is contained in the intrinsic `ThetaNull(Str, fij,param,N, g)`.

#### Input:
- `Str` an object of ssEllipticCurveEndStr giving the supersingular elliptic curve E together with an endomorphism structure.
-  `fij` is a gxr array of gxg Matrices with entries in B describing the spanning tuple of completely decomposed Theta_eta divisors.
- `param` is a vector giving the Dieudonne module of H. Caution: the algorithm does not check whether H is maximally isotropic!
- `N` is the level of the theta nullvalues
- `g` is the dimension of the desired abelian variety.

#### Output:
The theta nullvalues of level N of the quotient E^g/H


## Example:
The following example computes the generic fiber of a 1-dimensional family of supersingular plane quartics

```
AttachSpec("spec");
Attach("ThetaNull.m");
p:=3;
g:=3;
E:= EllipticCurve([GF(p^4)| -1,0]);
ECMlift:=EllipticCurve([-1,0]);
B<iB,FB, iFB>:=QuaternionAlgebra<RationalField()| -1,-p>;

i:= map<E-> E | [-E.1, GF(p^2).1^(Integers()!((p^2-1)/4))*E.2,E.3]>;
F:= map<E->E | [E.1^p,E.2^p,E.3^p]>;
//Notice that Magma composes maps from left to right.
iF:=F*i;
Str:=ssEllipticCurveEndStr(E,ECMlift,B,[IdentityMap(E), i, F, iF],[B| 1, iB, FB,iFB],[FB, iB]);
T:=Time();
k<beta>:=GF(p^12);


K<t>:=RationalFunctionField(k);
x:=[ k.1^520, k.1, 1 ];

fij:=[
    [
     Matrix(B,   [[1, -1/2 - 1/2*FB, 1/2 - 1/2*FB],
        [-1/2 + 1/2*FB, 1, 1/2 + 1/2*FB],
        [1/2 + 1/2*FB, 1/2 - 1/2*FB, 1]]),

     Matrix(B, [[1, 1, -1],
        [1, 1, -1],
        [-1, -1, 1]]),

        Matrix(B, [[1, -1/2 + 1/2*FB, 1/2 + 1/2*FB],
        [-1/2 - 1/2*FB, 1, 1/2 - 1/2*FB],
        [1/2 - 1/2*FB, 1/2 + 1/2*FB, 1]])
    ],
    [
        Matrix(B, [[1, -1/2 - 1/2*FB, -1/2 + 1/2*FB],
        [-1/2 + 1/2*FB, 1, -1/2 - 1/2*FB],
        [-1/2 - 1/2*FB, -1/2 + 1/2*FB, 1]]),

        Matrix(B, [[1, 1, 1],
        [1, 1, 1],
        [1, 1, 1]]),

        Matrix(B, [[1, -1/2 + 1/2*FB, -1/2 - 1/2*FB],
        [-1/2 - 1/2*FB, 1, -1/2 + 1/2*FB],
        [-1/2 + 1/2*FB, -1/2 - 1/2*FB, 1]])
    ],
    [
        Matrix(B, [[1, -1, -1],
        [-1, 1, 1],
        [-1, 1, 1]]),

        Matrix(B, [[1, 1/2 - 1/2*FB, 1/2 + 1/2*FB],
        [1/2 + 1/2*FB, 1, -1/2 + 1/2*FB],
        [1/2 - 1/2*FB, -1/2 - 1/2*FB, 1]]),

        Matrix(B, [[1, 1/2 + 1/2*FB, 1/2 - 1/2*FB],
        [1/2 - 1/2*FB, 1, -1/2 - 1/2*FB],
        [1/2 + 1/2*FB, -1/2 + 1/2*FB, 1]])
    ], 
    [DiagonalMatrix([B|p,0,0]),
    DiagonalMatrix([B|0,p,0]),
    DiagonalMatrix([B|0,0,p])]
];


q:=ThetaNull(Str, fij, [K|x[1],t,x[2],0, x[3],0],4,3);
print q;
C:=CurveFromThetaNull(q,3);
print C;
Time(T);
```


The intrinsic `CurveFromThetaNull(q,g)` computes a curve C such that A=Jac(C) (if exists). So far only only g=2,3 posssible.

#### Input:
- `q` the algebraic theta nullvalues of A. The level should be N=2 if g=2 and N=4 if g=3.
- `g` the dimension of A
#### Output:
A curve `C` of genus `g` such that A=Jac(C) or an error if such a curve does not exist.

Notice that, by Torelli's theorem, `C` is uniquely determined from A.


