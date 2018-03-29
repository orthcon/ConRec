# Connection-Coefficients
Compute the connection coefficients of orthogonal polynomials

The package APCI is required to support the computations.
More precisely, we need the Ext_Zeil and qExt_Zeil of APCI.

The main file is conrec.mpl and the example file is examples.mw which
includes all the examples in the manuscript.

To use the package, one need the following steps.

1. Download the four files APCI.hdb, apci.help, apci.ind, apci.lib and put them in one directory, say for example, "d:/maplelib/apci".

2. Include the path of APCI in libname. That is, open Maple and type the command 

        libname:=libname,"d:/maplelib/apci";

3. Load the package APCI by the Maple command 

        with(APCI);

4. Download the file ConRec.mple and put it in a certain directory, say for example, "d:/maplepkg/" and load the package by the Maple command

        read "d:/maplepkg/ConRec.mpl";
        
5. Now you can use the commands of the package. For examples, see the file "examples.mw".

===================================================================================

The usage of the Maple commands ConRec and ConRecq of the package.

ConRec(P,Q,n,k,x,t,Ls,shift,Pindex,Qindex)

ConRecq(P,Q,n,k,x,t,Ls,shift,Pindex,Qindex,q)

The meaning of the parameters are listed as follows.

1. P,Q: two orthogonal polynomials, represented as a hypergeometric term P(n,k,t) such that

P_n(x) = \sum_{k} P(n,k,t) with x=x(t)

For example, Wilson polynomials are

W_n(x(t)) = \sum_k poch([a+b, a+c, a+d], n) hyperterm([-n, n+a+b+c+d-1, a+sqrt(-1)*t, a-sqrt(-1)*t], [a+b, a+c, a+d], 1, k)

with x(t)=t^2

Here, we use `poch([a,b],k)` to denote

Pochhammer(a,k)*Pochhammer(b,k) = (a)_k (b)_k

and use `hyperterm([a,b], [c], x, k)` to denote

(a)_k (b)_k x^k / ( (c)_k k! )

2. L: an operator acting on f(x), represented as a function of `f` and `x`. For example,

L := proc (f, x) diff(f, x) end proc

3. shift: indicate the shift variable of the recurrence relation. `ShiftP` means the recurrence relation
is of the form

   * a[n+2,m] + * a[n+1,m] + * a[n,m] + * a[n-1,m] + * a[n-2,m]

where

   P_n(x) = \sum_m a[n,m] Q_m(x).        (*)

`ShiftQ` means the recurrence relation is of the form

    * a[n,m+2] + * a[n,m+1] + * a[n,m] + * a[n,m-1] + * a[n,m-2]

4. Pindex,Qindex: the subindex of P and Q. For example, in (*) we have Pindex=n and Qindex=m 



