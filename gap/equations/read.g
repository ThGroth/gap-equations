#############################################################################
##
#W    read.g                 The Equation package              Thorsten Groth
##

#############################################################################
##
#R  Read the install files.
##
ReadPackage( "equations","lib/freeproducts.gi");
ReadPackage( "equations","lib/equations.gi");
ReadPackage( "equations","lib/normalform.gi");

if LoadPackage("fr") then
	ReadPackage( "equations","lib/decomposable.gi");	
fi;
#E  read.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here