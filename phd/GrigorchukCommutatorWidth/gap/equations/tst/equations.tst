#############################################################################
##
#A  equations.tst 	           Equations package                Thorsten Groth
##
gap> START_TEST("Equations package: equations.tst");
gap> ReadPackage("equations","tst/declarations.g");
true
gap> EqG := EquationGroup(G,F);
GrigorchukGroup*FX
gap> Eq := Equation(EqG,[Comm(F.1,F.2),(a*b)^2]);
Equation in [ x1, x2 ]
gap> DEqG := DecompositionEquationGroup(EqG);
GrigorchukGroup*FX*FX
gap> constr := GroupHomomorphismByImages(Group(EquationVariables(Eq)),SymmetricGroup(2),[(),()]);
[ x1, x2 ] -> [ (), () ]
gap> DEq:=DecompositionEquation(DEqG,Eq,constr);
DecomposedEquation in [ x11, x12, x21, x22 ]
gap> h := EquationHomomorphism(EqG,[F.1],[[F.2,a]]);
[ x1 ]"->"[ [ x2, a ] ]
gap> ev := EquationEvaluation(Eq,[F.1,F.2],[b,a]);
MappingByFunction( GrigorchukGroup*FX, GrigorchukGroup, function( q ) ... end,\
 <Trivial Mealy element on alphabet [ 1 .. 2 ]> )
gap> IsSolution(ev,Eq);
true
gap> STOP_TEST( "equations.tst", 5000 );
