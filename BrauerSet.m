/*
BrauerSet.m
Authors: Brendan Creutz & Duttatrey Srivastava 2022
Summary: This is magma code for computing the obstruction to rational points on a hyperelliptic curve over Q coming from 2-torsion in the Brauer group.
Details of the algorithm are in the paper 'Explicit Brauer-Manin obstructions on hyperelliptic curves'

Code was developed for magma V2.25-6
*/

freeze;

declare verbose BrSet, 2;


//Useful functions independent of L;
QpPolynomial:=function(f,p,prec);
		Qp:=pAdicField(p,prec);
		Q<x>:=PolynomialRing(Qp,prec);
		fp:=Qp!f;
		return fp;
	end function;
Bad_Primes:=function(c,f);
	S:={2};
	S join:={p[1]: p in Factorization(Numerator(Rationals()!(4*(Discriminant(f))) ))};
	S join:= {p[1]: p in Factorization(Integers()!c)};
	//S join:= {3,5,7,11,13};
	return S;
	//return S;
end function;

TwoSelmerGroupLargeP := function(L,P,LP,toLP);
// KP a p-adic field with large residue field of odd cardinality.
// This function is the same as pSelmerGroup(2,KP), but seems to be much faster for large residue field
	G := AbelianGroup([2,2]);
	pi := UniformizingElement(LP);
	k,rk := ResidueClassField(P);
	a := k!0;
	while IsSquare(a) do
		a := Random(k);
	end while;
	checkres := function(x);
		n := Valuation(x);
		xt := x*pi^(-n);
		if IsSquare(rk(xt @@ toLP)) then
			return 0;
		else
			return 1;
		end if;
	end function;
	preim := function(g);
		gg := Eltseq(g);
		return pi^gg[1]*toLP((a^gg[2]) @@ rk);
	end function;
	return G, map< LP -> G | x :-> Valuation(x)*G.1 + checkres(x)*G.2, y :-> preim(y) >;
end function;


/***********************************************************************************
Processing precision errors from p-adic Roots and Factorization
***********************************************************************************/
//Since the returned string has unpredictable linebreaks in it,
//remove all non-alphabetic characters from either string and compare those.
//SetClassGroupBounds("GRH");

alphabetic_characters:={CodeToString(c): c in {StringToCode("A")..StringToCode("Z")} join {StringToCode("a")..StringToCode("z")}};
FactorizationErrorMessage:=&cat[a : a in Eltseq("Runtime error in'LocalFactorization': Factorization: Insufficient precision in factorization of a non-squarefree polynomial.") | a in alphabetic_characters];
RootFindingErrorMessage:=&cat[a : a in Eltseq("Runtime error in 'Roots': Insufficient precision to find roots")| a in alphabetic_characters];

function IsFactorizationPrecisionError(ERR)
 return FactorizationErrorMessage eq  &cat[a: a in Eltseq(ERR`Object) | a in alphabetic_characters];
end function;

function IsRootFindingPrecisionError(ERR)
 return RootFindingErrorMessage eq
				&cat[a: a in Eltseq(ERR`Object) | a in alphabetic_characters];
end function;

//Polynomial Data
QQ:= Rationals();
Qx<x>:= PolynomialRing(Rationals());

//B-M Obstruction
BrauerSetb :=function(g,S,B,Approach);
	// g = g(x) polynomial defining hyperelliptic curve C : y^2 = g(x)
	// S a sequence of primes for which local information will be taken into account (small primes of bad reduction will always be included)
	// B an integer, ignore primes of bad reduction larger than B if they divide discriminant of g(x) exactly. Set to 0 if no bound is required.
	g1:= Qx ! MonicModel(g,2);
	//g1 := g;
	c:=LeadingCoefficient(g1);
	f:=Rationals()!(1/c)*g1;
	if not HasPointsEverywhereLocally(c*f,2) then
		vprintf BrSet, 1 : "Not locally soluble.\n";
		return {};
	end if;
	assert IsIrreducible(c*f);
	vprintf BrSet, 1 : "\n/*--------------------------------------------------*/\n";
	vprintf BrSet, 1 : "y^2= %o Has Monic Model \n", g;
	vprintf BrSet, 1 : "y^2=%o \n", c*f;
	vprintf BrSet, 1 : "/*--------------------------------------------------*/\n";
	//-----------------------------------------------------------------------------------------
	//Bad Primes(see paper for details) AND BRUIN-STOLL bound
	//-----------------------------------------------------------------------------------------
	Sgiven := Setseq(S);
	S:=Sort( Setseq(Bad_Primes(c,f) join S ));
	if B gt 0 then
		S:=[ p : p in S | p le B or Valuation(Discriminant(g),p) ge 2 or Valuation(c,p) gt 0 or p in Sgiven or p eq 2];
	end if;
	prime_bound:=function(f);
		dg:=Degree(f);
		if dg mod 2 eq 0 then
			gns:= Integers()!(dg-2)/2;
		else
			gns:= Integers()!(dg-1)/2;
		end if;
		BSbd:=Integers()!(2*(1+(gns-1)*2^(2*gns)));
		return NextPrime(Integers()!(BSbd^2+2)), BSbd;
	end function;
	bd,_:=prime_bound(g1);
	S_small:= [p: p in S | p le bd or Valuation(Discriminant(f),p) gt 1];
	S_large:= [p: p in S | p gt bd and Valuation(Discriminant(f),p) le 1];

	vprintf BrSet, 1 : "S:=%o with %o small primes and %o large primes\n", S,#S_small,#S_large;
	//-----------------------------------------------------------------------------------------
	//L as NumberField
	//-----------------------------------------------------------------------------------------
	q:=2;
	L:=NumberField(c*f);
	//-----------------------------------------------------------------------------------------
	//L1 is L as Polynomial Ring quotient
	//-----------------------------------------------------------------------------------------
	I:= ideal<Qx|c*f>;//g1=c*f
	L1,m:=quo<Qx|I>;
	FF := < gg[1] : gg in Factorization(c*f) >;
	L1_alg, toL1:=AbsoluteAlgebra(L1);
	BacktoL:=Inverse(toL1);
	LNum:=NumberOfComponents(L1_alg);
	//-----------------------------------------------------------------------------------------
	//LtoL1 connects L to L1 (as structures on the same underlying object)
	//-----------------------------------------------------------------------------------------
	LtoL1:=hom<L->L1| m(Qx!x)>;
	L1toL:=hom<L1->L|[L.1] >;
	//Part 1: Construct (L*/Squares ONLY), and then finding elements of square norm or c times square norm
	Qnf:= NumberField(x-1 : DoLinearExtension);
	O:= MaximalOrder(L);
	O := LLL(O);
	Z:= MaximalOrder(Qnf);
	S_Z:= {ideal<Z|p> : p in S};
	S_O:= {fid[1]: fid in Factorization(ideal<O|p>), p in S};
	// L mod Squares: LSq
	vprintf BrSet, 1 : "Computing p-Selmer group of L ";
	vprintf BrSet, 1 : "Log(Disc(L)) = %o, Minkowski Bound = %o, GRH Bound = %o\n", Log(AbsoluteValue(Discriminant(L))),MinkowskiBound(L),GRHBound(L);
	t0 := Cputime();
	LSq, LtoLSq, mB, B:= pSelmerGroup(q, S_O:Raw);
	vprintf BrSet, 1 : ": %o seconds.\n", Cputime() - t0;
	LSqtoL:=Inverse(LtoLSq);
	QSq, QtoQSq := pSelmerGroup(q,S_Z);
	//Define norms
	B:=Eltseq(B);
	// B is the Factorbase.
	
	SOs := [ P : P in S_O];
	VS_0 := VectorSpace(GF(2),#SOs);
	primebelow := function(P);
		for p in S do
			if Valuation(O!p,P) gt 0 then return p; end if;
		end for;
	end function;
	Bps := [* VS_0 ! [ Valuation(b,p) : p in SOs ]  : b in B *];
	// Used to determine where b in B is ramified, and also for products of such b's.
	NB:= [Norm(b): b in B];
	//time NBps := [ {p : p in S | Valuation(NB[m],p) ne 0 } : m in [1..#B]];
	//Defining Norms
	LSqNorm:= hom<LSq-> QSq | [QtoQSq(PowerProduct(NB, [c mod q: c in Eltseq(mB(g))])) : g in OrderedGenerators(LSq) ]>;
	//Step 1: Elements of square norm:
	//We compute the basis for kernel of Norm map as a subgroup of LSq, and takes representatives of the basis elements of this subgroup in L
	N1_elts_LSq:= Kernel(LSqNorm);
	// An inclusion map for the kernel as a subgroup
	Norm1toLSq:= hom<N1_elts_LSq->LSq | [LSq!i: i in OrderedGenerators(N1_elts_LSq)] >;

	t1 := Cputime(); t:= t1-t0;
	vprintf BrSet, 1 : "Unramified outside S elements of square norm computed; Dimension = %o, took %o seconds.\n", Ngens(N1_elts_LSq),t;

	// Part Two: Image of mu_p maps
	//---------------------------------------
	//L_p*/Squares
	//---------------------------------------
	LpMods:= function(L,p);
		//O := MaximalOrder(L);
		vprintf BrSet, 2 : "Computing LpMods for p = %o\n", p;
		pids:=[pid[1]: pid in Factorization(p*O)];
		L_p:=<>;
		LtoL_p:=<>;
		L_pModSq:=<>;
		L_ptoL_pModSq:=<>;
		dim := 0;
		dim_p:=<>;
		pri:=<>;
		HSmats:=<>;
		for p_i in pids do
			vprintf BrSet, 2 : "Computing at pp = %o\n", p_i;
			L_pi,LtoL_pi:= Completion(L,p_i);
			L_pi`DefaultPrecision:=100;
			//Added to deal with Large primes more efficiently(BC)
			if Norm(p_i) lt 1000 or p eq 2 then
				L_piModSq,L_pitoL_piModSq:=pSelmerGroup(2,L_pi);
			else
				vprintf BrSet, 2 : "Using TwoSelmerGroupLarge...\n";
				L_piModSq,L_pitoL_piModSq:=TwoSelmerGroupLargeP(L,p_i,L_pi,LtoL_pi);
			end if;
			Append(~dim_p,#Generators(L_piModSq));
			Append(~L_p,L_pi);
			Append(~LtoL_p, LtoL_pi);
			Append(~L_pModSq,L_piModSq);
			Append(~L_ptoL_pModSq,L_pitoL_piModSq);

			//HilbertSymbol
			reps := [ (L_piModSq.i @@ L_pitoL_piModSq) @@ LtoL_pi : i in [1..#OrderedGenerators(L_piModSq)]];

			vprintf BrSet, 2 : "Computing HS matrix at prime of dimension %o\n",#reps;
			HSmat := []; // matrix of the bilinear pairing on L_pi x L_pi given by Hilbert Symbol.
			for i in [1..#reps] do
				for j in [1..#reps] do
					m := HilbertSymbol(reps[i],reps[j],p_i);
					if m eq 1 then
						HSmat cat:= [0];
					else
						HSmat cat:= [1];
					end if;
				end for;
			end for;
			HSmat := Matrix(GF(2),#reps,#reps,HSmat);
			Append(~HSmats,HSmat);
		end for;
		dim:=&+[ dim_p[i]: i in [1..#dim_p] ];
		//Here: Building L_p/L_p^2 as a quotient of abelian groups: Easier calculation via ModqthPowers and Inj, but this loses connection to actual L computations.
		//Using this part sparingly.
		A := FreeAbelianGroup(dim);
		G := quo<A | [ q*A.i : i in [1..dim]]>;
		dima := 0;
		lis := [];
		for i in [1..#LtoL_p] do
			G_i := Codomain(L_ptoL_pModSq[i]);
			lis cat:= [hom< G_i -> G | [G.(j+dima) : j in [1..#Generators(G_i)]] >];
			dima +:= #Generators(G_i);
		end for;
		ModqthPowers := map< CartesianProduct([L_p : L_p in [ Domain(m) : m in L_ptoL_pModSq]]) -> G | x :-> &+[ lis[i](L_ptoL_pModSq[i](x[i])) : i in [1..#L_ptoL_pModSq] ]>;
		Inj := map< L -> Domain(ModqthPowers) | x :-> < LtoL_p[i](x) : i in [1..#LtoL_p] > >;
		return <p,pids,dim_p,dim,LtoL_p,L_ptoL_pModSq,pri, ModqthPowers, Inj, HSmats>;
	end function;

	t0 := Cputime();
	//Computing and storing this data for all p in S: This is to avoid issues coming from change in representatives when the function is called in different instances!
	L_pModsList:=[* LpMods(L,S[i]): i in [1..#S] *];
	//Set up data at the infinite place: refer to Bruin-Stoll 2009 for details
	L1:= Domain(toL1);
	pl := InfinitePlaces(Rationals())[1];
	embs := RealExtensions(L1,pl);
	if #embs ne 0 then
		rts := [ e(L1.1) : e in embs ];
		Sort(~rts);
	else
		rts:=[1];
		//vprintf BrSet, 1 : "No real roots of c*f!!";
	end if;
	//m:=#rts;
	//adding images on basis elements of L_p Mod Sq at p=infty
	VSp_rts:=VectorSpace(GF(2),#rts);
	ARstar := Hom(VSp_rts,VectorSpace(GF(2),1));
	basis_list:=[Eltseq(i): i in Basis(VSp_rts)];
	t1 := Cputime();
	vprintf BrSet, 1 : "Setting up local data took %o seconds.\n", t1 - t0;

	//This function combines all uses of LpMods: It accesses L_pModsList and provides the required information
	L_pMods:= function(L,p,S, L_pModsList, flg);
		//L_pModsList;
		ii:=Index(S,p);
		if ii eq 0 then
			vprintf BrSet, 1 : "Given prime is not in S: Use LpMods(L,p) instead to find explicit object.\n";
		else
			LpMod_at_p:=L_pModsList[ii];
			//Now LpMod looks like this <S[ii],pids,dim_p,dim,LtoL_p,L_ptoL_pModSq,pri, ModqthPowers, Inj,HSmats>
		if flg eq 1 then
			pids:=LpMod_at_p[2];
			LtoL_p:=LpMod_at_p[5];
			L_ptoL_pModSq:=LpMod_at_p[6];
			ModqthPowers:= LpMod_at_p[8];
			HSmats := LpMod_at_p[#LpMod_at_p];
			return pids, LtoL_p, L_ptoL_pModSq, ModqthPowers, HSmats;
		elif flg eq 2 then //LocalSelmerGroup_1
			ModqthPowers:= LpMod_at_p[8];
			Inj:= LpMod_at_p[9];
			dim_p:= LpMod_at_p[3];
			return  ModqthPowers, Inj, dim_p;
		elif flg eq 3 then
			pri:=LpMod_at_p[7];
			pids:=LpMod_at_p[2];
			dim_p:= LpMod_at_p[3];
			dim:= LpMod_at_p[4];
			return pri, dim_p,dim,pids; //used in finding inverses in inv_p;
		else
			vprintf BrSet, 1 : "flg can take values 1,2 or 3. You entered %o\n", flg;
			return [];
		end if;
		end if;//ii eq 0
	end function;
	//---------------------------------------
	//Local Image for p large: p> PrimeBound(f)
	//---------------------------------------
	unr_elts_at_p:= function(L,p,c,S,L_pModsList);
		pids, LtoL_p, L_ptoL_pModSq, ModqthPowers:=L_pMods(L,p,S,L_pModsList, 1);
		L_p:=<Codomain(LtoL_p[i]): i in [1..#LtoL_p]>;
		L_pModSq:=<Codomain(L_ptoL_pModSq[i]): i in [1..#L_ptoL_pModSq]>;
//Qp mod Squares in Lp mod Squares: as diagonal image.
		O:= MaximalOrder(L);
		Z:= MaximalOrder(Qnf);
		QpSq, QptoQpSq := pSelmerGroup(2,pAdicField(p,30));
		QpSqElts:={i@@QptoQpSq: i in QpSq};
		QpSqEltsinLp:=[];
		QpSqEltsinLpSq:=[];
		for QpElt in QpSqElts do
			QpSqEltsinLp cat:=[<L_p[i]!QpElt: i in [1..#L_p]>];//Diagonal Image
			QpSqEltsinLpSq cat:=[[w: w in Flat(<Eltseq(L_ptoL_pModSq[i](L_p[i]!QpElt)): i in [1..#L_p]>)]];
		end for;
//even valuation elements
		cr:=<>;
		cr1:=<>;
		for i in [1.. #L_pModSq] do
			L_pMS_i:=L_pModSq[i];
			val0:=[];
			valS:=[];
			for elt in L_pMS_i do
				eltinLp_i:=elt@@L_ptoL_pModSq[i];
				eltinL_i:=eltinLp_i@@LtoL_p[i];
				val_o_elt:=Valuation(eltinL_i, pids[i]);
				if  val_o_elt mod 2 eq 0 then
					Append(~val0,eltinL_i);
					Append(~valS,(eltinLp_i));
				end if;
			end for;//Inverse(LtoL_p[i])(Inverse(L_ptoL_pModSq[i])(elt)
			Append(~cr, val0);
			Append(~cr1, valS);
		end for;
		//cr1;
		ccr:=CartesianProduct([i: i in cr]);
		ccr1:=CartesianProduct(<i: i in cr1>);
		fin:=[];
		fin_in_LpSq:=[];
		for elt in ccr1 do
			eltNorm:= &*[Norm(L_p[i]!elt[i],pAdicField(p,30)): i in [1..#elt]];
	//		vprintf BrSet, 1 : "FOUND!", IsSquare(c*eltNorm);
			if IsSquare(pAdicField(p,30)!(c*eltNorm)) then//Norm condition ensures we are still in H_k
				fin cat:=[elt];
				elt_in_LpSq:=[w: w in Flat(<Eltseq(L_ptoL_pModSq[i](elt[i])): i in [1..#elt]>)];
				Include(~fin_in_LpSq, elt_in_LpSq);
			end if;
		end for;
		fin:=fin cat QpSqEltsinLp; //this is still only unramified elements of even valuation and elts of QpSq in LpSq
		fin_in_LpSq:= fin_in_LpSq cat QpSqEltsinLpSq; // include relevant elements of Q_p* mod squares
		dm:=#fin_in_LpSq[1];
		finSp:= VectorSpace(GF(2), dm);
		finSpSq:={finSp!i: i in fin_in_LpSq};
		finSpElt:={Eltseq(i): i in sub<finSp|finSpSq>};
		fin_in_LpSq:=finSpElt;
		return fin, fin_in_LpSq, L_ptoL_pModSq, LtoL_p;//fin is a list of all tuples that are of norm c mod squares.
	end function;
	//----------------------------------------------------------------------------
	mu_p_large:=function(c,f,p,L,L_pModsList);
				if p ge prime_bound(f) then
					//vprintf BrSet, 1 : "Computing at large prime: %o \n", p;
					imag, imag_mod_sq,L_ptoL_pModSq, LtoL_p:= unr_elts_at_p(L,p,c,S,L_pModsList);
					return imag, imag_mod_sq, L_ptoL_pModSq, LtoL_p;
				else
					return [];
				end if;
	end function;

	//---------------------------------------
	// p at infinity
	//---------------------------------------
	muInf_pts:= function(toL1, c,f);//rts is sorted list of real roots
		L1 := Domain(toL1);
		pl := InfinitePlaces(Rationals())[1];
		embs := RealExtensions(L1,pl);
		rts := [ e(L1.1) : e in embs ];
		if #rts eq 1 then
			eps:=0.01;
			if c gt 0 then
				lst:={rts[1]};
			else
				lst:={rts[1]};
			end if;
			return lst,eps,embs,rts;
		elif #rts gt 1 then
			Sort(~rts);
			eps:=Minimum([Abs(rts[i]-rts[j]): i,j in [1..#rts] | i lt j])/1000;
			nm:=#rts;
			rts:=Sort([i: i in rts]);
			lst:={rts[1]}; 
			for i in [2..#rts] do
				if i mod 2 ne 0 then
					//vprintf BrSet, 1 : "fc";
					Include(~lst,rts[i]);
				end if;
			end for;
			if c gt 0 then
				Include(~lst, rts[#rts]);//largest roots
			end if;
			for i in lst do
				if c lt 0 then
					assert Evaluate(c*f,i+eps) gt 0;
					else
					if i ne rts[#rts] then
							assert Evaluate(c*f,i-eps) gt 0;
						else
							assert Evaluate(c*f,i+eps) gt 0;
						end if;
					end if;
				end for;
				return lst,eps,embs,rts;//lst is the list of one root per component, eps is the epsilon.
		else return [1],0,embs,[1];
		end if;
	end function;

	phi_Z:=function(a);//converts R/R^2 values to Z/2 values
		Z1:=Parent(a);
		assert a in {1,-1};
		if a eq Z1!-1 then
			return 1;
		elif a eq Z1!1 then
			return 0;
		else
			return 3;//nonsense answer
		end if;
	end function;

	muInf:= function(toL1,c,f);
		//muInf for local image at infinity, in Z/2 vector space structure
		assert c ne 0;
		L1 := Domain(toL1);
		pl := InfinitePlaces(Rationals())[1];
		ev_pts_set,eps, embs, rts := muInf_pts(toL1,c,f);
		ev_pts:=[i: i in ev_pts_set];
		Sort(~ev_pts);
		if c gt 0 and #ev_pts gt 1 then
			pts:=[ev_pts[i]-eps: i in [1..#ev_pts-1 ]] cat [ev_pts[#ev_pts]+eps];
		elif c lt 0 then //and #ev_pts gt 1 then
			pts:=[ev_pts[i]+eps: i in [1..#ev_pts]];
		//else
			//pts:=[1]; //BC WHAT IS THIS?!
		end if;
		mu_inf_list:=[];
		if #rts eq 1 then//exceptional case: in case of no roots, only one point comes through muInf_pts: and for use in A_l, this is just 0 going to 0 in Z/2
			return [ [0] ];
		end if;
		for xR in pts do
			mu_inf_list cat:= [[phi_Z(Sign( (xR-e(L1.1) ))): e in embs]];
		end for;
		return  mu_inf_list;
	end function;

	//Below: inv_infinity
	//-------------------------------------------------------------------------
	phi_R:=function(a);//converts Z/2 values to R*/R*2 values
		Z1:=Parent(a);
		assert a in {0,1};
		if a eq Z1!0 then
			return 1;
		elif a eq Z1!1 then
			return -1;
		else
			return 3;//nonsense answer
		end if;
	end function;
	//---------------------------------------
	//Invariant Maps: inv_p and inv_inf
	//---------------------------------------
	inv_at_inf:=function(toL1,c,f,l1,elt); //elt is a tuple in the vec space structure of L_p Mod Sq at p=infty, MUST have only 0 or 1 as entries.
		L1 := Domain(toL1);
		pl := InfinitePlaces(Rationals())[1];
		embs := RealExtensions(L1,pl);
		rts := [ e(L1.1) : e in embs ];
			Sort(~rts);
		assert #embs gt 0;
		inv_inf:=1;
		if #embs gt 0 then
			l1_at_roots:=[ e(l1) : e in embs ];
			assert #l1_at_roots eq #Eltseq(elt);
			for i in [1..#l1_at_roots] do
				inv_inf *:= (l1_at_roots[i] lt 0) and phi_R(elt[i]) lt 0 select -1 else 1;
			end for;
		end if;
		return phi_Z(inv_inf);
	//phi_Z ensures that the output is a value in Z/2 ={0,1} and not {1,-1}
	end function;
	//Inv_infinity would be used for bigger A_l map
	inv_p:= function(p,l,w,i); //l in possibL i.e. L, w in W=Image(mu_P) preimages in L
		pids:=[pid[1]: pid in Factorization(p*O)];
		A := HilbertSymbol(l,w,pids[i]);
		return phi_Z(A);
	end function;

	inv_pp:= function(l,w,pid); //l in L, w in W=Image(mu_P) preimages in L
		A := HilbertSymbol(l,w,pid);
		return phi_Z(A);
	end function;

//for l in possibL do
//	l;GF(2)!(&+[inv_p(c,f,p,S,L,L_pModsList,l,-L.1): p in S]);
//	end for; //this sum should be 0 for any curve with rational points
	//---------------------------------------
	//Local Image for p small: p leq PrimeBound(f)
	//---------------------------------------
	ImageOfCQp:= function(c,f,p,L);
		image:=[];
		//Step 0: See if c is a square in Q_p;
		Qp:=pAdicField(p);
		if p eq 2 then
			Qp`DefaultPrecision *:=30;
		end if;
		if Valuation(c,p) gt 0 then
			Qp`DefaultPrecision *:=30;
		end if;
		if IsPower(Qp!c,2) then
			//point above infinity: if c is a square, its sqrt(c)
			im:=L!1;
			image cat:=[im];
		end if;
		//Step 1: Look for Weierstrass point
		cf:=c*f;
		while true do
			try
				ff:={gg[1]: gg in Factorization(cf,Qp)};
				no_error:= true;
			catch ERR
				if IsFactorizationPrecisionError(ERR) then
					no_error:= false;
				else
					error ERR;
				end if;
			end try;
			if no_error then
				break;
			end if;
			Qp`DefaultPrecision+:=10;
			vprintf BrSet, 1 : " Factorization over Q_%o requires increasing precision to %o", p, Qp`DefaultPrecision;
			error if Qp`DefaultPrecision gt 200, "Precision problems while factoring.\n";
		end while;
		ff := { Polynomial([ Rationals() ! a : a in Coefficients(gg)]) : gg in ff};
		// May encounter precision issues because of this!
		for gg in { gg : gg in ff | Degree(gg) eq 1 } do
			//This means there is a Qp-rational Weierstrass point.
			cofactor := c*&*{ h : h in ff | h ne gg};
			ggQ := Polynomial([Rationals()!a : a in Coefficients(gg)]);
			cofacQ := Polynomial([Rationals()!a : a in Coefficients(cofactor)]);
			im := -Evaluate(ggQ,L.1)+Evaluate(cofacQ,L.1);
			image cat:= [im];
			// (rootg - theta) + cofactor(theta)
		end for;
		//Step 2: Looking for points with z=1
		ord:= func< g | g eq 0 select Infinity() else Min([Valuation(c,p) : c in Coefficients(g)])>;
		_<x> := Parent(cf);

		IsSquareAtLevel := function(e);
		//returns a function which, given integer A, checks if it is a square till preicison e
			if p eq 2 then
				IsSquare := function(A);
					v := Valuation(A,p);
					if v mod 2 eq 1 then
						return false;
					end if;
					return (Integers()!(A/p^v)) mod 2^Min(3,e) eq 1;
				end function;
			else
				IsSquare := function(A);
					v := Valuation(A,p);
					if v mod 2 eq 1 then
						return false;
					end if;
					return IsPower(GF(p)!Integers()!(A/p^v),2);
				end function;
			end if;
			return IsSquare;
		end function;

		IsSquareAtLevels := [ IsSquareAtLevel(e) : e in [1..p eq 2 select 3 else 3]];
		ConditionToGoDeeper := function(fx1,v1,E1);
		// v1 = ord(fx1)
			if E1 le v1 then
				return true;
			end if;
			if v1 mod 2 ne 0 then
				return false;
			end if;
			s := Min({E1 - v1,p eq 2 select 3 else 1});
			issqr := IsSquareAtLevel(s)((fx1*p^(-v1)));
			return issqr;
		end function;

	procedure SquareClasses(x0,e,G0,~found,~image, c0,inf,cf);
		for r in [0..p-1] do
			c1:= c0;
			x1:= x0 + (p^e)*r;
			//vprintf BrSet, 1 : "considering x1 = %o, mod p^(%o)\n", x1, e+1;
			fx1:= Evaluate(cf,x1);
			v1:= Valuation(fx1,p);
			E1:= ord( Evaluate(cf, x1+x*(p^(e+1)))-fx1 );
			if ConditionToGoDeeper(fx1,v1,E1) then
				//vprintf BrSet, 1 : "Going Deeper...\n";
				G1:= {gg: gg in G0 | ord( Evaluate(gg, x1+x*( p^(e+1) ))-Evaluate(gg,x1)) le Valuation(Evaluate(gg,x1),p)};
				if #G1 eq 0 or (#G1 eq 1 and  #{gg : gg in G1 | Degree(gg) eq 1 } eq 1) then
					//vprintf BrSet, 1 : "G1 condition met.\n";
					if G1 ne G0 then
						//vprintf BrSet, 1 : "selecting 2.\n";
						c1:= p eq 2 select 2 else 0;
					else
						//vprintf BrSet, 1 : "decreasing c1 from %o...\n",c1;
						c1:=c0-1;
					end if;
					//vprintf BrSet, 1 : "ere",p,x1,c1;
					if c1 eq 0  then
						if #G1 eq 0 then
							if not inf then
							//	vprintf BrSet, 1 : "  grabbing image x = %o\n", x1;
								im:= L!(x1-L.1);
								image cat:=[im];
							else
								try
									im:= L!(x1*(1-x1*L.1));
									image cat:=[im];
								catch e
									vprintf BrSet, 1 : "error in Local Image";
								end try;
							end if;
							found:= true;
							//break;
						end if;//if #G1 eq 0 then
					else
						SquareClasses(x1,e+1,G1,~found,~image, c1,inf,cf);
					end if;//if c1 eq 0  then
				else
				//	vprintf BrSet, 1 : "recursing, G1 condition not met.\n";
					SquareClasses(x1,e+1,G1,~found,~image, c1,inf,cf);
				end if;//if #G1 eq 0 or (#G1 eq 1 and  #{gg : gg in G1 | Degree(g) eq 1 } eq 1) then
			end if;//if ConditionToGoDeeper(fx1,v1,E1) then
		end for;
	end procedure;
		//Use the procedure to find a point with z=1.
		found := false;
		inf:= false;
		imagex := [];
		imagez:=[];
		SquareClasses(0,0,ff,~found,~imagex, -1,inf,cf);
		//if found then return image; end if;
		/*Still need to look for points with z in pZ and x = 1
		change of vars: z = 1/x, w = y/x^m
		y^2 = c*f(x)  <===> w^2 = z^s*SwapVar(f)(z)---------*/
		SwapVar := func< a | a ne 0 select &+[ Coefficient(a,i)*Parent(a).1^(Degree(a)-i) : i in [0..Degree(a)]] else 0 >;
		cftilde := SwapVar(c*f);
		//ftilde := Polynomial([ Qp ! c : c in Coefficients(ftilde)]);
		fftilde := { SwapVar(gg) : gg in ff };
		Include(~fftilde, Parent(cf).1);
		 // Line 11 in LocalImage in Bruin Stoll paper suggests putting "x" one more element in fftilde if f has even degree AND c is a square
		// fftilde := fftilde join { Universe(fftilde).1 };
		 // we also include z even if s = 0 for two reasons:
		 // 1) so the points with z = 0 are ignored by the procedure SquareClasses
		 //	  (since we can just compute these directly).
		 // 2) we use (x - T) = (1/z - T) = z(1-zT), and the other polys in fftilde may only ensure (1-zT)
		 //	 has constant q-th power class on the neighborhoods computed.
		SquareClasses(0,1,fftilde,~found,~imagez,-1,true,cftilde);
		return imagez cat imagex cat image;
	end function;
	/*-----------------------------------------------------------------------------------------
	/ Building mu_S(C)
	/-----------------------------------------------------------------------------------------*/
	mu_S_small:=[**];
	mu_S_small_mods:=[**];
	t0 := Cputime();
	for p in S_small do
		imag := ImageOfCQp(c,f,p,L);
		ModqthPowers,Inj,dim_p:=L_pMods(L,p,S,L_pModsList,2);
		nm:= NumberOfComponents(Codomain(Inj));
		imag_mod_Lp:={};
		for el in imag do
			if ModqthPowers(Inj(L!el)) in imag_mod_Lp then
				Exclude(~imag,el);
			else
				Include(~imag_mod_Lp, ModqthPowers(Inj(L!el)));
			end if;
		end for;
		// at the end of this, imag is in L* and imag_mod_Lp is the classes.
		if #imag eq 0 then
			vprintf BrSet, 1 : "Locally not solvable at %o: No rational point exists\n", p;
			//quit;
		end if;
		mu_S_small cat:=[*[*p,imag*]*];
		mu_S_small_mods cat:=[*[*p,[Eltseq(i): i in imag_mod_Lp]*]*];
	end for;
	t1 := Cputime();
	vprintf BrSet, 1 : "Computing Local Image at Small Primes took %o seconds.\n", t1-t0;
	//Useful in A_l
	//mu_S_small_in_LpModSq:= CartesianProduct([[i[2]]: i in mu_S_small_mods]);
	mu_S:= mu_S_small;
	mu_S_mods:=mu_S_small_mods;
	mu_S_large:=[**];
	mu_S_large_mods:=[**];
	if #S_large ne 0 then
		for p in S_large do
				t0 := Cputime();
				im,im_mod_sq_large,L_ptoL_pModSq, LtoL_p:= mu_p_large(c,f,p,L,L_pModsList);
				t1 := Cputime();
				vprintf BrSet, 1 : "Time to compute image at p = %o was %o seconds.\n",p,t1-t0;
				im_mod_sq_large := Setseq(im_mod_sq_large);
				mu_S_large cat:=[*[*p, im*]*];//this is still only unramified elements of even valuation
				mu_S_large_mods cat:=[* [*p,im_mod_sq_large*]*];
		end for;
	mu_S cat:= mu_S_large;
	mu_S_mods cat:= mu_S_large_mods;// [*[*prime, local image at prime*]*]_{p in S}
	end if;
	mu_Inf_mods:= [*[*-1,muInf(toL1,c,f)*]*];
	mu_S:=mu_S cat mu_Inf_mods;
	mu_S_mods cat:= mu_Inf_mods;
	//mu_S_mods is the total
/*for i in [1..#S] do
	if S[i] ne -1 then
		if #mu_S_mods[i][2] eq 2^(L_pModsList[i][4]) then
			Exclude(~mu_S_mods, mu_S_mods[i]);
		end if;
end for;*/
	mu_S_in_LSq:= CartesianProduct(<i[2]: i in mu_S_mods>);
	assert #mu_S_in_LSq ne 0;
//	vprintf BrSet, 1 : "Computed Local Images at %o small primes, %o large primes, and at infinity \n", #S_small, #S_large;
	//Finished building mu_S(C): This one checks if #S_large is empty
	//By design, S_small is assumed to be non empty: and local image at infinity is included always: Even in the case of zero Real roots: in which case the image is just trivial.
	//-----------------------------------------------------------------------------------------
	// Building A_l as a homomorphism(linear map)
	//-----------------------------------------------------------------------------------------


	NotSoBadPrimes := [ p : p in S | Valuation(Discriminant(g1),p) le 1 and p gt 2 and Valuation(c,p) eq 0 ];
	vprintf BrSet, 2 : " The not-so-bad primes in S are %o\n", NotSoBadPrimes;
	BadBadPrimes := [ p : p in S | not p in NotSoBadPrimes ];


	if Approach eq "UseFactorBase" then


	t0 := Cputime();
	vprintf BrSet, 1 : "Computing A_b maps on factor base : #B = %o ", #B;
	ct := 0;
	Bmaps := [* *];
	for b in B do
		vprintf BrSet, 2 : "Considering b = %o\n", b;
		Bmap := [* *];
		t11 := 0;
		t00 := Cputime();
		for p in S do
			pids, LtoL_p, L_ptoL_pModSq,_,HSmats:=L_pMods(L,p,S,L_pModsList,1);
			_,dim_p,dim,pids:=L_pMods(L,p,S,L_pModsList,3);
			L_p:=<Codomain(LtoL_p[i]): i in [1..#LtoL_p]>;
			L_pModSq:=<Codomain(L_ptoL_pModSq[i]): i in [1..#LtoL_p]>;
			img_mat := [];
			for i in [1..#pids] do
				Vp := VectorSpace(GF(2),dim_p[i]);
				a1 := Eltseq( (Vp! (Eltseq(LtoL_p[i](L!b) @ L_ptoL_pModSq[i]))) * HSmats[i] );
				//time a2 := [inv_pp(b,(((L_pModSq[i].j)@@L_ptoL_pModSq[i])@@LtoL_p[i]),pids[i]): j in [1..#OrderedGenerators(L_pModSq[i])] ];
				//assert a1 eq a2;
				img_mat cat:= a1;
			end for;
			Bmap cat:= [* [* p, img_mat *] *];
			//if not IsOdd(p) then
			//	t11 := Cputime();
			//end if;
		end for;
		//printf "time for all p's %o, time for p = 2 : %o\n", Cputime()- t00, t11 - t00;
		//Now add the map at infinite place:
		img_mat := [];
		if #rts eq 1 then
			img_mat cat:=[0];
		else
			for elt in basis_list do
				img_mat cat:=[inv_at_inf(toL1,c,f,LtoL1(b),elt)];
			end for;
		end if;
		Bmap cat:= [* [*-1,img_mat*] *];
		Bmaps cat:= [* Bmap *];
		ct +:= 1;
		if ct eq 10 then
			vprintf BrSet, 1 : " : Estimate %o secs", (Cputime()-t0)*#B/10;
		end if;
		if ct eq 100 then
			vprintf BrSet, 1 : " : updated %o secs", (Cputime()-t0)*#B/100;
		end if;
	end for;
	vprintf BrSet, 1 : " : Actual %o secs.\n", Cputime()-t0;

//      N1eltsB := [ Eltseq(mB(a)) : a in OrderedGenerators(N1_elts_LSq) ];
        //each mB(a) is a list of exponents. The corresponding element ell in L* is
        // ell = PowerProduct(B,Eltseq(mB(a)))
        // We want to avoid actually multiplying this out.
//      NormsB := [ Norm(b) : b in B ];
//      N1eltsNorms := [ PowerProduct(NormsB,ell) : ell in N1eltsB ];
		//These are the norms (in k) of the elements in N1eltsB.
	// We should avoid writing these down as they are huge!
	// Instead determine where ell is ramified as follows:
	Ram_ells := function(mBell);
		ellS_0 := &+[ mBell[m]*Bps[m] : m in [1..#B]];
		ps := {};
		for i in [1..#SOs] do
			if ellS_0[i] ne 0 then
				ps join:= {primebelow(SOs[i])};
			end if;
		end for;
		return [p : p in ps];
	end function;

	evmaps_ells := [* *];
  vprintf BrSet, 1 : "Now computing corresponding A_ell maps : ";

        t0 := Cputime();

        //for m in [1..#N1eltsB] do
        for ell in OrderedGenerators(N1_elts_LSq) do
                //Working with ell in L* the element corresponding to PowerProduct(N1eltsB[m],B).
                // Want to get BadPrimes(ell) and the kernels of evaluation on mu_p(C) for such primes.
                //Ram_ell := [ p[1] : p in Factorization(Numerator(N1eltsNorms[m])*Denominator(N1eltsNorms[m])) | p[1] in S ];
                // includes all primes where ell is ramified (but could contain some primes where it is not...)
                N1eltB :=  Eltseq(mB(ell));
                Ram_ell := Ram_ells(N1eltB);
                // We use that A_ell evaluations to 0 at NotSoBadPrimes outside Ram_ell (because ell and local image are unramified)
				// printf " S = %o", S;
                BadPrimes_ell := Sort([p : p in Set(Ram_ell cat BadBadPrimes)]);
                vprintf BrSet, 2 : "Bad primes for ell_%o include : %o\n", m, Ram_ell;
                evmap_ell := [* *];

                for p in BadPrimes_ell do
                        //Build the map A_ell,p from the A_b,p as b ranges over the factor base.
                        jj := Index(S, p);
                        assert p eq Bmaps[1][jj][1];
                        pids, LtoL_p, L_ptoL_pModSq:=L_pMods(L,p,S,L_pModsList,1);
                        _,dim_p,dim,pids:=L_pMods(L,p,S,L_pModsList,3);
                        L_p:=<Codomain(LtoL_p[i]): i in [1..#LtoL_p]>;
                        L_pModSq:=<Codomain(L_ptoL_pModSq[i]): i in [1..#LtoL_p]>;
                        A := VectorSpace(GF(2),dim);
                        A1 := VectorSpace(GF(2),1);
                        Astar:=Hom(A,A1);
                        eval_ellp := Astar ! 0;
                        for i in [1..#B] do
                                if N1eltB[i] mod 2 ne 0 then
                                        eval_ellp +:= Astar ! Bmaps[i][jj][2];
                                end if;
                        end for;
                        evmap_ell cat:= [* [* p, Kernel(eval_ellp) *] *];
                end for;
                // add map at p = infty...
                evmap_ellR := ARstar ! 0;
                for i in [1..#B] do
                        if N1eltB[i] mod 2 ne 0 then
                                evmap_ellR +:= ARstar ! Bmaps[i][#S+1][2];
                        end if;
                end for;
                evmap_ell cat:= [* [* -1, Kernel(evmap_ellR) *] *];
                evmaps_ells cat:= [* [*m, evmap_ell*] *];
        end for;
        vprintf BrSet, 1 : " %o secs.\n", Cputime()-t0;

	else //Don't use Factor Base....

	vprintf BrSet, 1 : "Computing A_ell maps : \n";
	requiredL := {};
	vprintf BrSet, 1 : "	Step 1 write down ell's : ";

	// Or here we can take a random subset!

	Randomized := false;
	NumberRandoms := 5; //How many random elements will we take?
	if not Randomized then
		t0 := Cputime();
		ct := 0;
		for a in OrderedGenerators(N1_elts_LSq) do
			ct +:= 1;
			requiredL join:= {L!((Norm1toLSq(a))@@LtoLSq)};
			if ct eq 2 then
				vprintf BrSet, 1 : " Estimate: %o secs. ", (Cputime()-t0)*#OrderedGenerators(N1_elts_LSq)/2;
			end if;
		end for;
		vprintf BrSet, 1 : " : Actual : %o secs.\n",Cputime()-t0;
	else
		//t0 := Cputime();
		ellsLSq := { Random(N1_elts_LSq) : i in [1..NumberRandoms]};
		for a in ellsLSq do
			requiredL join:= {L!((Norm1toLSq(a))@@LtoLSq)};
		end for;
		vprintf BrSet, 1 : "	total time : %o secs.\n",Cputime()-t0;
	end if;

	evmaps_ells := [* *];
	t1 := Cputime();
	vprintf BrSet,1 : "	Step 2 compute corresponding maps : ";
	for ell in requiredL do
		// Want to get BadPrimes(ell) and the kernel of evaluation on mu_p(C) for such primes.
		Ram_ell := [ p[1] : p in Factorization(Numerator(Norm(ell))*Denominator(Norm(ell))) | p[1] in S ];
		// includes all primes where ell is ramified (but could contain some primes where it is not...)
		// We use that A_ell evaluations to 0 at NotSoBadPrimes outside Ram_ell (because ell and local image are unramified)
		BadPrimes_ell := Sort([p : p in Set(Ram_ell cat BadBadPrimes)]);
		vprintf BrSet, 2 : "Bad primes for ell = %o include : %o\n\n", ell, [ p[1] : p in Factorization(Numerator(Norm(ell))*Denominator(Norm(ell))) ];
		evmap_ell := [* *];
		for p in BadPrimes_ell do
			pids, LtoL_p, L_ptoL_pModSq:=L_pMods(L,p,S,L_pModsList,1);
			_,dim_p,dim,pids:=L_pMods(L,p,S,L_pModsList,3);
			L_p:=<Codomain(LtoL_p[i]): i in [1..#LtoL_p]>;
			L_pModSq:=<Codomain(L_ptoL_pModSq[i]): i in [1..#LtoL_p]>;
			img_mat := [];
			for i in [1..#pids] do
				img_mat cat:= [inv_pp(ell,(((L_pModSq[i].j)@@L_ptoL_pModSq[i])@@LtoL_p[i]), pids[i]): j in [1..#Generators(L_pModSq[i])] ];
			end for;
			A := VectorSpace(GF(2),dim);
			A1 := VectorSpace(GF(2),1);
			Astar:=Hom(A,A1);
			ev_map:=Astar!img_mat;
			if Dimension(Kernel(ev_map)) lt dim then
				evmap_ell cat:= [* [* p, Kernel(ev_map) *] *];
			// else evaluation of A_ell at this prime is 0.
			end if;
		end for;
		L1:= Domain(toL1);
		pl := InfinitePlaces(Rationals())[1];
		embs := RealExtensions(L1,pl);
		//vprintf BrSet, 1 : "gf:=",  #embs;
		if #embs ne 0 then
			rts := [ e(L1.1) : e in embs ];
			Sort(~rts);
		else
			rts:=[1];
			//vprintf BrSet, 1 : "No real roots of c*f!!";
		end if;
		m:=#rts;
		//adding images on basis elements of L_p Mod Sq at p=infty
		VSp_rts:=VectorSpace(GF(2),#rts);
		basis_list:=[Eltseq(i): i in Basis(VSp_rts)];
		img_mat := [];
		if #rts eq 1 then
			img_mat cat:=[0];
		else
			for elt in basis_list do
				img_mat cat:=[inv_at_inf(toL1,c,f,LtoL1(ell),elt)];
			end for;
		end if;
		A := VectorSpace(GF(2),#img_mat);
		A1 := VectorSpace(GF(2),1);
		Astar:=Hom(A,A1);
		ev_map:=Astar!img_mat;
		if Dimension(Kernel(ev_map)) lt #img_mat then
			evmap_ell cat:= [* [* -1, Kernel(ev_map)*] *];
		end if;
		if #evmap_ell gt 0 then
			evmaps_ells cat:= [* [* ell, evmap_ell *] *];
		//else Evaluation of A_ell is 0 everywhere!
		end if;
	end for;

	vprintf BrSet, 1 : " %o secs\n", Cputime()-t1;

	end if;



	AdelicProds := mu_S_mods;
	TotalLevels := #evmaps_ells; // le Dimension(N1elts)
	pind := function(AdelicProd,p);
		//printf "Adelic Prod = %o\n", AdelicProd;
		for i in [1..#AdelicProd] do
			if AdelicProd[i][1] eq p then
				return i;
			end if;
		end for;
	end function;

	FoundPoint := false;

	procedure UseA_ellInfo(AdelicProd,level,~FoundPoint);
		if level gt TotalLevels then
			vprintf BrSet, 1 : "Found a point that survived.\n";
			FoundPoint := true;
		else

			ell := evmaps_ells[level][1];
			evmaps_ell := evmaps_ells[level][2];
			S_ell := [ e[1] : e in evmaps_ell ];
			M := Hom(VectorSpace(GF(2),#evmaps_ell),VectorSpace(GF(2),1)) ! [1 : i in [1..#evmaps_ell]];
			for m in Kernel(M) do
				AP := AdelicProd;
				mm := Eltseq(m);
				//printf "Looking at mm = %o\n", mm;
				//printf "AdelicProd coming in: %o\n care about S = %o\n\n ", AP, S_ell;

				for i in [1..#mm] do
					ind := pind(AP,S_ell[i]);
					//printf "evmaps_ell[ind][2] = %o", evmaps_ell[i][2];
					if mm[i] eq 0 then
						//printf "AP[ind][2] = %o", AP[ind][2] ;
						AP[ind] := [* S_ell[i], [* xp : xp in AP[ind][2]  | (Generic(evmaps_ell[i][2]) ! xp) in evmaps_ell[i][2] *] *];
					else
						AP[ind] := [* S_ell[i], [* xp : xp in AP[ind][2]  | not (Generic(evmaps_ell[i][2]) ! xp) in evmaps_ell[i][2] *] *];
					end if;
				end for;

			//	printf "AdelicProd coming out: %o\n", AP;

				if &*[ #A[2] : A in AP ] gt 0 then
					vprintf BrSet, 2 : "Branch survived, size now %o, going to level %o.\n", &*[ #A[2] : A in AP ], level + 1;
					UseA_ellInfo(AP,level +1,~FoundPoint);
				else
					vprintf BrSet, 2 : "Branch died at level %o\n", level;
				end if;

			end for;
		end if;

	end procedure;

	t0 := Cputime();
	UseA_ellInfo(AdelicProds,1,~FoundPoint);
	t1 := Cputime();
	vprintf BrSet, 1 : "Computation of intersection recursively took %o seconds.\n", t1 -t0;

	if FoundPoint then
		return {1};
	else
		return {};
	end if;


end function; //BrauerSetb

intrinsic BrauerSet(g :: RngUPolElt : S := {}, B := 1, Approach := "" ) -> Set
{Computes a set containing the image of the Brauer-Manin Set of the hyperelliptic curve y^2 = g(x)}
	return BrauerSetb(g,S,B,Approach);
end intrinsic;
