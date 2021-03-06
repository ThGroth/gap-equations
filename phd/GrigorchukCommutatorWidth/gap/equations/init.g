#############################################################################
##
#W    init.g                 The Equation package             Thorsten Groth
##


#############################################################################
##
#R  Read the declaration files.
##
ReadPackage( "equations","lib/freeproducts.gd");
ReadPackage( "equations","lib/equations.gd");
ReadPackage( "equations","lib/normalform.gd");

if LoadPackage("fr") then
	ReadPackage( "equations","lib/decomposable.gd");	
fi;
#E  init.g . . . . . . . . . . . . . . . . . . . . . . . . . . . .  ends here