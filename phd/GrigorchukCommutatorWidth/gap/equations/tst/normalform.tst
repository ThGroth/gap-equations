#############################################################################
##
#A  normalform.tst 	           Equations package                Thorsten Groth
##
gap> START_TEST("Equations package: normalform.tst");
gap> EqG := EquationGroup(G,F);
GrigorchukGroup*FX
gap> ForAll(elms,function(e) local x,xn; x := Equation(EqG,e);xn := EquationNormalForm(x); return x^xn.hom = xn.nf and xn.nf^xn.homInv = x; end);
true
gap> EqG2 := EquationGroup(G2,F);
F5*FX
gap> ForAll(others,function(e) local x,xn; x := Equation(EqG2,e);xn := EquationNormalForm(x); return x^xn.hom = xn.nf and xn.nf^xn.homInv = x; end);
true
gap> STOP_TEST( "normalform.tst", 5000 );