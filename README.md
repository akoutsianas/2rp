## The Generalized Fermat equation $Ax^2 + By^r=Cz^p$ and applications

This is the repo associate to the paper *'The Generalized Fermat equation $Ax^2 + BY^r=Cz^p$ and applications'*
written by Pedro-Jose Cazorla Garcia, Angelos Koutsianas and Lucas Villagra Torcomian.


### Contents of the repository

- **elimination_step_functions.m**: This file contains the code for the elimination step in the modular method. This 
refers to the computations for the proof of Theorem 7.1. The main function is the *elimination_step_J* 
where the inputs are
  - *decomp*: the output of the *NewformDecomposition* of the New Subspace
  - *primes*: a list of primes that we use in the elimination step
  - *filename*: the location and name of the file where the output of the elimination step will be stored
- **elimination_step.m**: The file where we also describe how to run the computations


### The computations

If you want to do/repeat the computations supporting the paper run the following in Magma.

```commandline
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
```

#### Load code

From the appropriate folder of the repo in your local machine load the file */elimination_step_functions.m*

```commandline
load "/to_your_folder/elimination_step_functions.m";
```

#### Compute space of Newforms

```commandline
N52 := q2^5 * q5^2; // Case 2|a and 3|b
time decomp52 := NewformDecomposition(NewSubspace(HilbertCuspForms(K, N52)));
```

#### Choose the location of elimination_step_output_level_N52.txt

We choose the folder where the file */elimination_step_output_level_N52.txt* is located. The output of all computations
will be saved in this file.

```commandline
filename := "/to_your_folder/elimination_step_output_level_N52.txt";
```

#### First run of the elimination step

We run the elimination step with all primes $\leq 23$.

```commandline
primes := [3, 7, 11, 13, 17, 19, 23];

/*  The case 2|a and 3|b */

PrintFile(filename, "The case 2|a and 3|b": Overwrite:=true);
PrintFile(filename, Sprintf("primes = %o", primes));
time problematic_newforms := elimination_step_J(decomp52, primes, filename);
```

#### Second run of the elimination step to eliminate big primes

We apply the elimination step only for the *problematic_newforms* using all the primes $\leq 100$.

```commandline
print "**** Newforms with 'big' small primes ****";

primes := [p : p in PrimesUpTo(100) | p ne 2 and p ne 5];
PrintFile(filename, Sprintf("**** Newforms with 'big' small primes ****"));
PrintFile(filename, Sprintf("primes = %o", primes));
time _ := elimination_step_J(problematic_newforms, primes, filename);
```