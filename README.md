# Connection-Coefficients
Compute the connection coefficients of orthogonal polynomials

The package APCI is required to support the computations.
More precisely, we need the Ext_Zeil and qExt_Zeil of APCI.

The main file is conrec.mpl and the example file is examples.mw which
includes all the examples in the manuscript.

To use the package, one need the following steps.

1. Download the four files APCI.hdb, apci.help, apci.ind, apci.lib and put them in one directory, say for example, "d:/maplelib/apci"

2. Include the path of APCI in libname. That is, open Maple and type the command 
        libname:=libname,"d:/maplelib/apci";

3. Load the package APCI by the Maple command 
        with(APCI);

4. Download the file and put it in a certain directory, say for example, "d:/maplepkg/" and load the package by the Maple command
        read "d:/maplepkg/";
        
5. Now you can use the commands of the package. For examples, see the file.
