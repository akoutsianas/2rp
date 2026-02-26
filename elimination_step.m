/*************************************************
** MODULE NAME: elimination_step.m
**
** Authors: Pedro-Jose Cazorla Garcia
**          Angelos Koutsianas  
**          Lucas Villagra-Torcomian
**
** Affiliations: Universidad Pontificia Comillas, Spain
**               Aristotle University of Thessaloniki, Greece
**               Simon Fraser University, Canada
**
** Description: This module includes the functions to carry out 
**              the elimination step for the equation 
**                 -5x^2 + y^5 = z^{2p},
**              under the assumption that solutions (a,b,c)
**              satisfy either
**                 (*) 2 | c or 
**                 (*) 3 | b and 2 | a (the latter is automatic
**                     if 2 does not divide c).
**
**              Specifically, we aim to find an upper bound for 
**              the exponent p by computing the possible traces 
**              of Frobenius and comparing them to the coefficients
**              of the Hilbert newforms, as per the proof of Theorem
**              7.1 in the article.
**
** Article: Cazorla-Garcia, P.J., Koutsianas, A. and Villagra-Torcomian, L.
**          "The generalized Fermat equation Ax^2+By^r = Cz^p and applications",
**          available online in arxiv.
**
**************************************************/

/*******************************************************
****************** SETUP PARAMETERS ********************
*******************************************************/

/* We define some parameters that will be common for all functions 
   in this module. */
   
/* We define the ring RQ[z] of polynomials over the rationals*/

RQ<z> := PolynomialRing(Rationals());


/* We define the number field K = Q(zeta_5 + zeta_5^-1) and its
   ring of integers OK. Since the two ideals over 2 and over 5
   will be used throughout, we also define them.   */

K<u> := NumberField(z^2 - z - 1);
OK := RingOfIntegers(K);
q2 := Factorization(2*OK)[1,1];
q5 := Factorization(5*OK)[1,1];


/* Finally, we define the ring of polynomials over the number 
   field K. */

RK<x> := PolynomialRing(K);


/*******************************************************
****************** MAIN FUNCTIONS **********************
*******************************************************/

/******************************************************
** Name: get_traceFrob
** Description: Given the coefficients a, b of the curve
**              C(a,b), a rational prime q and a twisting
**              parameter, this function returns the list 
**              of all possible traces of Frobenius of the 
**              Jacobian of the curve C(a,b) twisted by the
**              parameter on a GL_2 block.
**
** Arguments: a,b -> Integer parameters corresponding to the 
**                   parameters of the curve C(a,b).
**            q -> Rational prime over which the trace of 
**                 Frobenius will be computed.
**            twist -> Squarefree integer for which the 
**                     curve will be twisted.
**            
** Output: The list of all possible traces of Frobenius
**         of the Jacobian of the curve over K.
******************************************************/

function get_traceFrob(a,b,q,twist)

	/* We begin by defining the appropiate twist of the curve C(a,b) and finding the 
	   prime ideal of OK lying over q. */
	
	Cab := QuadraticTwist(HyperellipticCurve(x^5 - 25*b*x^3 + 125*b^2*x - 250*a),twist);
	qIdeal := Factorization(q*OK)[1,1];


	/* We proceed to compute the Euler factor Lf of the curve over the prime over q. Then,
	   the possible traces of Frobenius are -(the linear coefficient of the irreducible
	   factors of Lf), and we return these. */
	
	Lf := EulerFactor(Cab,qIdeal);
	Lf := Reverse(Lf);
	Lfactor := Factorization(RK!Lf);
	traceFrob := [-Coefficient(f[1],1) : f in Lfactor];

	return traceFrob;
end function;


/******************************************************
** Name: elimination_step_J
** Description: Given a list of modular forms and a list 
**              of auxiliary primes and a twist, this function
**              performs the elimination step by attempting to 
**              compute a bound for the exponent p. This is 
**              performed by using all primes in the list (even
**              if the same result could be possibly achieved 
**              by using less) and for the given twist. 
**
**              This function also displays all primes which
**              could not be eliminated for each modular form.
**
** Arguments: decomp -> List of modular forms. 
**            primes -> List of auxiliary primes that will be 
**                      used for the elimination step. More primes
**                      give better results but worse performance.
**            twist -> Squarefree integer for which the 
**                     curve will be twisted.
**
** Parameters: bdiv3 -> Boolean parameter indicating whether b is 
**                      assumed to be divisible by 3. By default its 
**                      value is false.
**
** Output: True if the elimination step has been successful for all 
**         modular forms, False if not. In addition, the set of 
**         small primes for each newform for which elimination could 
**         not be proved is displayed on the screen.
******************************************************/

function elimination_step_J(decomp, primes, twist : bdiv3 := false)

	/* We define a boolean variable stating whether the elimination step has been 
   	   carried out successfully. By default, we set it to true.                 */
	
	successful := true;


	/* We apply the elimination step to each of the modular forms given in 
	   the decomp variable. */
	
	for i:=1 to #decomp do

		/* We consider each newform separately and define L to be its 
		   field of coefficients. */
		
		decompf := decomp[i];
		newf := Eigenform(decompf);
		L := HeckeEigenvalueField(decompf);
	
		/* We define M to be the compositum field of K and L, and consider
		   the two embeddings K -> M and L -> M. */

		M := CompositeFields(K,L);
		bol1, KtoM := IsSubfield(K,M[1]);
		bol2, LtoM := IsSubfield(L,M[1]);
		
		/* We initialise a list where we will keep the possible values of Bq
           	   (see proof of Theorem 7.1).	*/
		
		list_Bq_newf := [];
			
		/*
		** Main loop: for each prime q in our list of primes,
		**            we proceed to compute the possible traces
		**            of Frobenius and compare them to the eigen-
		**            values of the newform.                    */
		
		for q in primes do
		
			/* We need to consider all prime ideals dividing q*OK,
			   and so we compute all the Hecke eigenvalues for the 
			   newform under consideration. */
			
			qK_list := SetToSequence(Support(q*OK));
			aqfnew_list := [HeckeEigenvalue(newf,qK) : qK in qK_list];

			/* We initialize the product with the prime under consideration.
			   This corresponds to the quantity Bq in the proof of Theorem 7.1*/
			
			prodq := q;

			/* CASE 1: If q is 3 and 3 | b, we know that b = 0 (mod 3) and we 
			           may use this additional information. */
			
			if q eq 3 and bdiv3 eq true then
				
				b := 0;
				/* We need to consider the case where b = 0 (mod 3). By coprimality,
				   then a = 1,2 (mod 3). */
				
				for a in [1, 2] do
					traceFrob := get_traceFrob(a,b,q,twist);
					
					/* First case: only one trace of Frobenius. We compute the norm of tr(Frob)-aq, which 
                       			   will be added to the product. */
					
					if #traceFrob eq 1 then
						tr1 := KtoM(K!traceFrob[1]);
						nextprodq := Gcd([Integers()!Norm(tr1^2 - LtoM(aqfnew^2)) : aqfnew in aqfnew_list]);
					
					/* Second case: there are two traces of Frobenius. Since we do not know which trace 
					 corresponds to which prime of K so we consider the two possible permutations. The 
					 computed product will be added to the possible list of primes. */

					elif #traceFrob eq 2 and #aqfnew_list eq 2 then
						tr1 := KtoM(K!traceFrob[1]);
						tr2 := KtoM(K!traceFrob[2]);
						aq1 := LtoM(aqfnew_list[1]);
						aq2 := LtoM(aqfnew_list[2]);

						nextprodq1 := Gcd([Integers()!Norm(tr1^2 - aq1^2),Integers()!Norm(tr2^2 - aq2^2)]);
						nextprodq2 := Gcd([Integers()!Norm(tr1^2 - aq2^2),Integers()!Norm(tr2^2 - aq1^2)]);
						nextprodq := nextprodq1 * nextprodq2;
					end if;

					prodq *:= nextprodq;
				end for;

			else
				/* CASE 2: If q is not 3. */

				/* We consider all possible values of a and b modulo q. Note that, by 
				   coprimality, it cannot happen that a, b and c are simultaneously 
				   divisible by q. */
				
				for a in [0 .. q-1] do
					for b in [0 .. q-1] do
						if a ne 0 or b ne 0 then
							cp := -5*a^2 + b^5;

							/* First case: c is not divisible by q and so it is a prime of good 
							   reduction for C(a,b). In this case, the factor is the 
							   norm of the trace of Frobenius minus the eigenvalue. */
							
							if cp mod q ne 0 then
			
								/* We proceed to compute all possible traces of Frobenius for all 
								possible twists. */
								
								traceFrob := get_traceFrob(a,b,q,twist);
																
								if #traceFrob eq 1 then
									/* First subcase: only one trace of Frobenius. We compute 
									   the norm of tr(Frob)-aq, which will be added to the product. */

									tr1 := KtoM(K!traceFrob[1]);
									nextprodq := Gcd([Integers()!Norm(tr1^2 - LtoM(aqfnew^2)) : aqfnew in aqfnew_list]);
								elif #traceFrob eq 2 and #aqfnew_list eq 2 then

									/* Second subcase: there are two traces of Frobenius. Since we do not know which
									   trace corresponds to which prime of K so we consider the two possible
									   permutations. The computed product will be added to the possible 
									   list of primes. */

									tr1 := KtoM(K!traceFrob[1]);
									tr2 := KtoM(K!traceFrob[2]);
									aq1 := LtoM(aqfnew_list[1]);
									aq2 := LtoM(aqfnew_list[2]);

									nextprodq1 := Gcd([Integers()!Norm(tr1^2 - aq1^2),Integers()!Norm(tr2^2 - aq2^2)]);
									nextprodq2 := Gcd([Integers()!Norm(tr1^2 - aq2^2),Integers()!Norm(tr2^2 - aq1^2)]);
									nextprodq := nextprodq1 * nextprodq2;
								end if;

							else
								/* Second case: c is divisible by q and so it is a prime of bad reduction for C(a,b).
							           In this case, the factor is the eigenvalue - (q+1)^2. */

								if LegendreSymbol(5,q) eq 1 then
									nextprodq := Gcd([Integers()!Norm(aqfnew^2 - (q + 1)^2) : aqfnew in aqfnew_list]);
								else			
									aqfnew := aqfnew_list[1];			
									nextprodq := Integers()!Norm(aqfnew^2 - (q^2 + 1)^2);
								end if;
							end if;

							/* Once again, we update the product with the factors that we have added. */
							
							prodq *:= nextprodq;
						end if;
					end for;
				end for;	
			end if;

			/* We update the list of possible Bq by adding the one we have computed for q. */
			
			Append(~list_Bq_newf,Integers()!prodq);
		end for;

		/* Once we have exhausted all primes, we simply compute the bound as the gcd of all the Bq that we have computed. */
		
		bound := GCD(list_Bq_newf);
		
		if bound ne 0 then
			/* In the case where the bound is non-zero, we have successfully managed to bound the exponent. Since 
		   	   p is prime, we display the possible exponents. */

			printf "i = %o of %o, small exponents after elimination = %o\n",i,#decomp,PrimeFactors(bound);
					
		else
			/* If the bound is zero, the elimination step has been unsuccessful. */

			printf "i = %o of %o failed using %o\n",i,#decomp,primes;
			successful := false;
		end if;
	end for;

	/* We return the boolean value determining whether the elimination step has been successful or not. */
	return successful;

end function;

/******************************************************
******************* MAIN LOOP *************************
******************************************************/

/* We compute the required spaces of Hilbert newforms. For this, we set the conductors. */ 

N52 := q2^5 * q5^2; // Case 2|a and 3|b
N62 := q2^6 * q5^2; // Case 2|c

time decomp52 := NewformDecomposition(NewSubspace(HilbertCuspForms(K, N52)));
time decomp62 := NewformDecomposition(NewSubspace(HilbertCuspForms(K, N62)));


/* In order to successfully carry out the elimination step, we need to consider eight different twists. */

TwistList:=[1, -1, 2, -2, 2*u-2, -2*u-2, u-1, -u-1];


/* For each twist, we perform the elimination using that twist. */

print "The case 2|a and 3|b";
time for d in TwistList do
	print "-> Performing elimination for twist by d = ", d;
  	elimination_step_J(decomp52, [3, 7, 11, 13], d : bdiv3 := true);
end for;

print "************************";

print "The case 2|c";
time for d in TwistList do
  	elimination_step_J(decomp62, [3, 7, 11, 13], d);
end for;
