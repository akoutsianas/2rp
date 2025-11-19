// We apply the elinimation step for the equation -5x^2 + y^5 = z^{2n} when 10|x.



Q<z> := PolynomialRing(Rationals());
K<u> := NumberField(z^2 - z - 1);
RK<x> := PolynomialRing(K);
OK := RingOfIntegers(K);
q2 := Factorization(2*OK)[1,1];
q5 := Factorization(5*OK)[1,1];



// Returns the list of possible traces of Frobenius on a GL_2 block over K.
function get_traceFrob(a,b,q,twist)

	Cab := QuadraticTwist(HyperellipticCurve(x^5 - 25*b*x^3 + 125*b^2*x - 250*a),twist);
	Q := Factorization(q*OK)[1,1];

	Lf := EulerFactor(Cab,Q);
	Lf := Reverse(Lf);
	Lfactor := Factorization(RK!Lf);
	traceFrob := [-Coefficient(f[1],1) : f in Lfactor];

	return traceFrob;
end function;



function elimination_step_J(decomp, primes, twist)
/*
	INPUT:
		- decomp : a list of newforms 
		- primes : a set of prime
		- twist : a list of numbers that we use for twisting

	OUTPUT:
		The function returns `true` if the elimination works together with a set of small primes which do not succeed.
		If forms := [] then we deal with all newforms otherwise only with the ones in forms.
*/


if #decomp eq 0 then
	printf "Empty space of newforms!\n";
	return true;
end if;

RQ<z> := PolynomialRing(Rationals());
K := BaseField(decomp[1]);
RK<x> := PolynomialRing(K);
OK := RingOfIntegers(K);

el := true;


// we apply the elimination step
for i:=1 to #decomp do

	decompf := decomp[i];
	newf := Eigenform(decompf);
	small_primes_newf := [];
	L := HeckeEigenvalueField(decompf);


	// This code will embed K into L so later comparisons do not type casting in Magma. The variable bol is not used.
	if Degree(L) gt 1 then
		bol, KtoL := IsSubfield(K,L);
	else
		L := K;
		bol, KtoL := IsSubfield(K,L);
	end if;
	
		
	for q in primes do
		qK_list := SetToSequence(Support(q*OK));
		aqfnew_list := [HeckeEigenvalue(newf,qK) : qK in qK_list];

		prodq := q;

		for a in [0 .. q-1] do
			for b in [0 .. q-1] do
				c := -5*a^2 + b^5;

				if c mod q ne 0 then
	
					traceFrob := get_traceFrob(a,b,q,twist);

					if #traceFrob eq 1 then
						tr1 := traceFrob[1];
						nextprodq := Gcd([Integers()!Norm(tr1^2 - aqfnew^2) : aqfnew in aqfnew_list]);
					elif #traceFrob eq 1 and #aqfnew_list eq 1 then
						tr1 := traceFrob[1];
						aq1 := aqfnew_list[1];
						nextprodq := Integers()!Norm(tr1^2 - aq1^2);
					elif #traceFrob eq 2 and #aqfnew_list eq 2 then
						// note we do not know which trace corresponds to which prime of K so we consider the two possible permutations
						tr1 := traceFrob[1];
						tr2 := traceFrob[2];
						aq1 := aqfnew_list[1];
						aq2 := aqfnew_list[2];

						// we only know the traces up to an unramified quadratic character
						nextprodq := Gcd([Integers()!Norm(tr1^2 - aq1^2),Integers()!Norm(tr2^2 - aq2^2)])*Gcd([Integers()!Norm(tr1^2 - aq2^2),Integers()!Norm(tr2^2 - aq1^2)]);
					end if;

				else
	
					if LegendreSymbol(5,q) eq 1 then
						nextprodq := Gcd([Integers()!Norm(aqfnew^2 - (q + 1)^2) : aqfnew in aqfnew_list]);
					else			
						aqfnew := aqfnew_list[1];			
						nextprodq := Integers()!Norm(aqfnew^2 - (q^2 + 1)^2);
					end if;
				end if;

				prodq *:= nextprodq;


			end for;
		end for;

		Append(~small_primes_newf,Integers()!prodq);

	end for;

	gcd := GCD(small_primes_newf);

	if gcd ne 0 then
		printf "i = %o of %o, small exponents after elimination = %o\n",i,#decomp,PrimeFactors(gcd);
		el:=true;
				
	else
		printf "i = %o of %o failed using %o\n",i,#decomp,primes;
		el := false;
	end if;
end for;


return el;

end function;



// Compute the required spaces of Hilbert newforms for the Case (II)
N := q2^5 * q5^2;

time decomp := NewformDecomposition(NewSubspace(HilbertCuspForms(K, N)));


// List of required twists to perform the elimination.

TwistList:=[1, -1, 2, -2, 2*u-2, -2*u-2, u-1, -u-1];


// Elimination step for the Case (II)
// For each twist, perform the elimination using that twist.
for d in TwistList do
	print "-> Performing elimination for twist by d = ", d;

  elimination_step_J(decomp, [3, 7, 11, 13, 17, 19, 23, 29], d);
end for;

