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
**              satisfy 2 | a and 3 | b.
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

load "/to_your_folder/elimination_step_functions.m";

/******************************************************
******************* MAIN LOOP *************************
******************************************************/

/* We compute the required spaces of Hilbert newforms. For this, we set the conductors. */ 

N52 := q2^5 * q5^2; // Case 2|a and 3|b

time decomp52 := NewformDecomposition(NewSubspace(HilbertCuspForms(K, N52)));


/* We perform the elimination using. */

primes := [3, 7, 11, 13, 17, 19, 23];

/*  The case 2|a and 3|b */

filename := "/to_your_folder/elimination_step_output_level_N52.txt";
PrintFile(filename, "The case 2|a and 3|b": Overwrite:=true);
PrintFile(filename, Sprintf("primes = %o", primes));
time problematic_newforms := elimination_step_J(decomp52, primes, filename);


print "**** Newforms with 'big' small primes ****";

primes := [p : p in PrimesUpTo(100) | p ne 2 and p ne 5];
PrintFile(filename, Sprintf("**** Newforms with 'big' small primes ****"));
PrintFile(filename, Sprintf("primes = %o", primes));
time _ := elimination_step_J(problematic_newforms, primes, filename);
