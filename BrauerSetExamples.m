/************************************************************
*************************************************************
*************************************************************
This file contains magma code (Compatible with magma V2.25-6) pertaining to the paper
[CS22] 'Explicit Brauer-Manin obstructions on hyperelliptic curves,' by Creutz and Srivastava

This requires the following intrinsic found in the companion file BrauerSet.m

BrauerSet(f :: RngUPolElt, S := {}, B := 1, Approach := "")

This computes a Brauer-Manin obstruction on the hyperelliptic curve C : y^2 = f(x);
The return value is either {} or {1}, being empty if and only if there is an obstruction computed.
The obstruction is given by a subgroup denoted by Br_{\Upsilon,T}(C) in [CS22].
Here T is a set of primes which can be controlled by the optional parameters S and B as follows:

The optional parameter S is a set of prime integers.
The optional parameter B is an integer.

If no optional parameters are set then T = S_min is the minimal set of primes as defined in [CS22].
If B := n is a postive integer, then T is the union of S_min, S and the set of primes of bad reduction up less or equal to n.
If B := 0, then T is the union of S_min, S and the set of primes of bad reduction up less or equal to the bound in [CS22, Theorem 4.4]

The optional parameter Approach is a string equal to 
"" (default) or to "UseFactorBase" (usually better when the genus is larger than 2 or 3).
This determines how the elements in (L^x/k^xL^x2) are represented.

*************************************************************
*************************************************************
*************************************************************/

Attach("BrauerSet.m");
SetVerbose("BrSet",1); // set to 2 or 0 for more or less detail
SetClassGroupBounds("GRH"); // Note that the output will be unconditional even though it is used in the class group computation.

/************************************************************
*************************************************************
*************************************************************
	Example 6.1 in [CS22]
*************************************************************
*************************************************************
*************************************************************/

f := -17*x^12-13*x^11-15*x^10+6*x^9-19*x^8+5*x^7-19*x^6+4*x^5-2*x^4+19*x^3+12*x^2+13*x-6;
BrauerSet(f : Approach := "UseFactorBase");
// The output is nonempty indicating there is no obstruction when T = S_{min} = {2,5,17}.

BrauerSet(f : S := {2,5,17,239}, B := 0, Approach := "UseFactorBase");
// The output is now empty indicating there is an obstruction when T = {2,5,17,239}.

// One can compare with the 2-cover descent algorithm of Bruin-Stoll:
SetVerbose("Selmer",2);
TwoCoverDescent(HyperellipticCurve(f));


/************************************************************
*************************************************************
*************************************************************
	The genus 50 example in Proposition 6.2 of [CS22]
*************************************************************
*************************************************************
*************************************************************/
_<x> := PolynomialRing(Rationals());
g := x^102 + x^101 + x^97 + x^95 + x^93 + x^90 + x^86 + x^80 + x^77 + x^75 + x^71 + 
    x^70 + x^68 + x^65 + x^64 + x^63 + x^62 + x^59 + x^58 + x^53 + x^50 + x^49 +
    x^48 + x^46 + x^45 + x^44 + x^38 + x^37 + x^36 + x^35 + x^32 + x^31 + x^26 +
    x^25 + x^22 + x^16 + x^11 + x^8 + x^7 + x + 1;//GRHBound 130508
f := 5*g;

// The code below checks that there is a Brauer-Manin obstruction
// to the existence of rational points on the hyperelliptic curve
// C : y^2 = f(x);
C := HyperellipticCurve(f);

fdisc := Factorization(Integers()!Discriminant(g));
badbadprimes := [ p[1] : p in fdisc | p[2] gt 1 ];
assert badbadprimes eq [2];

//Check local solubility of C
for pp in fdisc do
	assert IsLocallySoluble(C,pp[1]);
end for;
p := 2;
B := NextPrime(100^2);
assert B+1 ge 100*Sqrt(B);
// From the Weil Bound a smooth genus 50 curve over F_q has points for all q ge B 
while p le 10007 do
	assert IsLocallySoluble(C,p);
	p := NextPrime(p);
	//printf " p = %o\n", p;
end while;

L := NumberField(f);
ell := L.1;
assert Norm(ell) eq 1;
// This element of norm one gives a 2-torsion Brauer class A_ell on C.
// We check that it gives an obstruction to the existence of points.

//***********************
//Local Image at infinity
//***********************
rts := Roots(f,RealField());
assert #rts eq 2;
assert &and[ r[1] lt 0 : r in rts];
// from this we conclude that evaluation map on C(R) is trivial (see the paper)

//***********************
//Local image at 2:
//***********************
// details on computing local image
D2 := Decomposition(L,2);
g := PolynomialRing(Integers())!f;
gg := Reverse(g);
xsz1 := [ Integers()!i : i in Integers(8) | IsSquare(Evaluate(g,i)) ];
// If P = (x:y:1) is a point with x a 2-adic integer, then x = 4 mod 8;
assert xsz1 eq [4];
// Use Bruin-Stoll Lemma 4.4 to check that mu_2 is constant on this neighbourhood.
ff2 := Factorization(f,pAdicField(2));
x0 := xsz1[1];
for hh in ff2 do
	h := Polynomial([Rationals()! a : a in Coefficients(hh[1])]);
	hx := Evaluate(h,x0 + 2*x)- Evaluate(h,x0);
	assert Min([ Valuation(c,2) : c in Coefficients(hx)]) gt Valuation(Evaluate(h,x0),2);
end for;
// Now look at points of the form (1:y:z) with z a 2-adic integer.
zsx1 := [ Integers()!i : i in Integers(32) | IsSquare(Evaluate(gg,i)) ];
// We check that any z for which f(1,z) is a square, will have z*z0 a square for some z0 in zsx1. 
// In other words we have found square classes in Z_2 representing the z-coords of all points.
for z0 in zsx1 do
	assert Valuation(32,2) - Valuation(z0,2) ge 3;
end for;
// Next loop uses Bruin-Stoll Lemma 4.4 as above to ensure mu map is constant for z' = z0 mod 32
for z0 in zsx1 do
	//printf "\n z0 = %o.\n", z0;
	for hh in ff2 do
		h := Reverse(Polynomial([Rationals()! a : a in Coefficients(hh[1])]));
		//printf "   ord(h(z0)) = %o\n", Valuation(Evaluate(h,z0),2);
		hz0 := Evaluate(h,z0+2*x) - Evaluate(h,z0);
		//printf "   ord(h(z0+pi^ex)) = %o\n", Min([ Valuation(c,2) : c in Coefficients(hz0)]);
		assert Min([ Valuation(c,2) : c in Coefficients(hz0)]) gt Valuation(Evaluate(h,z0),2);
	end for;
end for;
// Now any z' = z0 mod 32 will have
// 1) z'*z0 a square
// 2) (z' - theta)*(z0 - theta) is square
// Together these imply that (1-z'*theta)*(1-z0*theta) is a square, so z' and z0 have same image under mu map.
muC2 := [(L!a) - L.1 : a in xsz1 ];
muC2 cat:= [ (a-a^2*L.1) : a in zsx1 ];
/*
muC2 := [
4-L.1,
4-16*L.1,
20-400*L.1,
12-144*L.1,
28-784*L.1,
];
*/
// We evaluate the the algebra at these points
for mP in muC2 do
	invAP := 1;
	invs := [];
	for P2 in D2 do
		HS := HilbertSymbol(L.1,mP,Ideal(P2[1]));
		//printf "  HS = %o\n", HS;
		invs cat:= [HS];
		invAP *:= HS;
	end for;
	//printf "inv_2 of A(P) = %o\n", invAP;
	//printf "invs = %o\n\n", invs;
	assert invAP eq 1;
end for;
// The assertions in the loop show that A_ell is the 0 map on C(Q_2).

//***********************
//Local image at 5:
//***********************
// all Q_5-points lie in a neighbourhood of the Q_5-root of f(x);
xsz1 := [ Integers()!i : i in [0..4] | Valuation(Evaluate(f,i),5) mod 2 eq 0  ];
zsx1 := [ Integers()!i : i in [0..4] | Valuation(Evaluate(Reverse(f),i),5) mod 2 eq 0  ];
assert #xsz1 eq 1 and #zsx1 eq 1;
x0 := xsz1[1];
z0 := zsx1[1];
assert x0*z0 mod 5 eq 1;
// We conclude that x in Q_p and f(x) has even valuation then x = 3 mod 5.
rts5 := Roots(f,pAdicField(5));
r5 := rts5[1][1];
assert #rts5 eq 1;
assert Integers()!r5 mod 5 eq 3;
// f(x) has a 5-adic root with x = 3 mod 5.
// All 5-adic points on C have x coordinate in this neighbourhood.
// We now use Bruin-Stoll Lemma 4.4 to check that the mu map is constant on this neighbourhood
ff5 := [g[1] : g in Factorization(f,pAdicField(5))];
ff5d := [ Polynomial([Rationals()| c : c in Coefficients(g) ]) : g in ff5 | Degree(g) gt 1 ];
for h in ff5d do
	hx := Evaluate(h,x0 + 5*x)- Evaluate(h,x0);
	assert Min([ Valuation(c,5) : c in Coefficients(hx)]) gt Valuation(Evaluate(h,x0),5);
end for;
// It remains to evaluate A_ell at the 5-adic Weierstrass point.
// The paper gives an argument for why it must be nontrivial. The calculation below does this as well.
cofactor := &*[ g : g in ff5 | Degree(g) gt 1 ];
d1factor := [ g : g in ff5 | Degree(g) eq 1 ][1];
d1facQ := Polynomial([Rationals()!a : a in Coefficients(d1factor)]);
cofacQ := 5*Polynomial([Rationals()!a : a in Coefficients(cofactor)]);
im := -Evaluate(d1facQ,L.1)+Evaluate(cofacQ,L.1);	
D5 := Decomposition(L,5);
invAP := 1;
for P5 in D5 do
	HS := HilbertSymbol(L.1,im,Ideal(P5[1]));
	printf "  HS = %o\n", HS;
	invAP *:= HS;
end for;
printf "inv_5 of A(P) = %o\n", invAP;
assert invAP ne 1;
//The evaluation maps at all other primes are trivial because ell is unramified there.
//So the evaluation maps are all constant for all primes and nontrivial at exactly p = 5.
//Thus there is a Brauer-Manin obstruction to the Hasse principle delivered by the algebra A_ell.

/************************************************************
*************************************************************
*************************************************************
	Code for testing random curves and comparing with descent info (primarily for testing correctness of the implementation)
*************************************************************
*************************************************************
*************************************************************/
SetVerbose("BrSet",1);


Q<x> := PolynomialRing(Rationals());

CompareWithDescentInfob := function(g,S,B);
	time BS := BrauerSet(g : S := S , B := B);
	try
		Sel2C :=TwoCoverDescent(HyperellipticCurve(g));
	catch e
		print "TwoCovDescError!!!";
		Sel2C := {};
	end try;
	if #BS eq 0 then
		assert #Sel2C eq 0;
	end if;
	aa,bb,cc:=PicnDescent(g,2);
	if Type(cc[2]) eq SetEnum then
		assert #BS eq 0;
		cc := 0;
	else
		cc := 1;
	end if;
	return #Sel2C, cc, #BS;
end function;

CompareWithDescentInfo := function(g)
	return CompareWithDescentInfob(g,{},1000);
end function;

RatP := [];
NotLS := [];
SelPic1Empty := []; // but no local obstruction
BMobsEmpty := []; // but SelPic nonempty
SelCEmpty := []; // but BMOBS nonempty
Other := [];

TestIntervalRandomly := procedure(N,gns,~RatP,~NotLS,~SelPic1Empty,~BMobsEmpty,~SelCEmpty,~Other);

counter := 0;
cs := { SquareFree(i) : i in [-N..N] | i ne 0 };

while true do
	coeffs := [ Random([-N..N]) : i in [0..(2*gns+1)]];
	f := Parent(x) ! Polynomial(coeffs cat [1]);
	if IsIrreducible(f) then
		c := Random(cs);
		counter +:= 1;
		if counter gt 10 then
				nums := [ #RatP,#NotLS,#SelPic1Empty,#BMobsEmpty,#SelCEmpty,#Other];
				Tot := &+nums;
				printf "\nTotal = %o.\n", Tot;
				printf "Proportions = %o\n\n", [ RealField(2)!nums[i]/Tot : i in [1..#nums]];
			counter := 0;
		end if;
		f *:= c;
		RP := RationalPoints(HyperellipticCurve(f) : Bound := 1000);
		if #RP gt 0 then
			RatP cat:= [f];
			ELS := true;
			time _ := CompareWithDescentInfo(f); // just to check
		else
			rts := Roots(f,RealField());
			if #rts eq 0 and Evaluate(f,0) lt 0 then
				ELS := false;
			else
				ELS := HasPointsEverywhereLocally(f,2);
			end if;

			if ELS then
				A,B,C := CompareWithDescentInfo(f);
				// A = #Sel2C;
				// B = 0,1 determines if SelPic empty
				// C = #BMOBS set
				if B eq 0 then
					SelPic1Empty cat:= [f];
				else
					if C eq 0 then
						BMobsEmpty cat:= [f];
					else
						if A eq 0 then
							SelCEmpty cat:= [f];
						else
							Other cat:= [f];
						end if;
					end if;
				end if;
			else
				NotLS cat:= [f];
			end if;
		end if;//counter gt 10
	end if;//IsIrreducible(f)
end while;
end procedure;

gns:= 3;
TestIntervalRandomly(10,gns,~RatP,~NotLS,~SelPic1Empty,~BMobsEmpty,~SelCEmpty,~Other);
// An assertion will fail if the outputs from TwoCoverDescent, PicnDescent, and BrauerSet are not consistent for a given curve.
/************************************************************
*************************************************************
*************************************************************
	Code for computing BM obstructions on random samples
	(as in Section 6.3 or [CS22])
*************************************************************
*************************************************************
*************************************************************/


SetClassGroupBounds("GRH");
Q<x> := PolynomialRing(Rationals());

RP := [];
NLS := [];
BrEmpty := [];
BrUndecided := [];


TestRandomCurves := procedure(g,N,number,~RP,~NLS,~BrEmpty,~BrUndecided);
ct := 0;
while ct lt number do
	
	f := x^2;
	while Degree(f) lt 2*g+2 or not IsIrreducible(f) do
		f := Parent(x) ! Polynomial([Random([-N..N]) : i in [1..2*g+3]]);
	end while;
	if not HasPointsEverywhereLocally(f,2) 
		then NLS cat:= [f];
	else
		if #RationalPoints(HyperellipticCurve(f):Bound := 1000) gt 0 then
			RP cat:= [f];
		else
			BrS := BrauerSet(f : B := 1, Approach := "UseFactorBase");
			if #BrS eq 0 then
				BrEmpty cat:= [f];
			else
				BrUndecided cat:= [f];
			end if;
		end if;
	end if;
	ct +:= 1;
end while;
end procedure;

//For example:
TestRandomCurves(4,20,10,~RP,~NLS,~BrEmpty,~BrUndecided); printf "RP,NLS,BrEmpty,Undecided = %o,%o,%o,%o\n", #RP,#NLS,#BrEmpty,#BrUndecided;


// The curves in BrUndecided may have obstructions if the size of S is increased, or they may have points of large height.

for f in BrUndecided do
	i := Index(BrUndecided,f);
	if #RationalPoints(HyperellipticCurve(f) : Bound := 10^5) gt 0 then
	// One can also take larger height bound
		RP cat:= [f];
		Remove(~BrUndecided,i);
		print " Found a Rational Point!\n";
	end if;
	if #BrauerSet(f : S := {p : p in PrimesUpTo(100)}, B := 1000) eq 0 then
	// One can consider including even more primes.
		BrEmpty := [];
		Remove(~BrUndecided,i);
		" Found an obstruction!\n";
	end if;
end for;

printf "After further testing:\n RP,NLS,BrEmpty,Undecided = %o,%o,%o,%o\n", #RP,#NLS,#BrEmpty,#BrUndecided;
	

