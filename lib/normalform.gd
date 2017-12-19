#############################################################################
##
#O EquationNormalForm . . . . . . . . .Compute the normal form of an equation
#O Genus . . . . . . . . . . . . . Compute the genus of a quadratic equation
##
## <#GAPDoc Label="EquationNormalForm">
## <ManSection>
## <Oper Name="EquationNormalForm" Arg="E"
##		 Label="equation"/>
##   <Returns>A record with two <M>3</M> components:  <A>nf</A>, <A>hom</A> and <A>homInv</A></Returns>
##   <Description>
##		The argument <A>E</A> needs to be a quadratic equation. For each such
##		equation there exists an equivalent equation in normal form.<P/>
##		The component <A>nf</A> is an equation in one of the forms
##		<M>O_{n,m},U_{n,m}</M> equivalent to the equation <A>E</A>. 
##		The component <A>hom</A> is an equation homomorphism which maps
##		<A>E</A> to <A>nf</A>. The component <A>homInv</A> is the inverse of this 
##		homomorphism.
## <Example><![CDATA[
## gap> F3 := FreeGroup("x","y","z");; SetName(F3,"F3");
## gap> S4 := SymmetricGroup(4);; SetName(S4,"S4");
## gap> G := EquationGroup(S4,F3);
## S4*F3
## gap> e := Equation(G,[Comm(F3.2,F3.1)*F3.3^2,(1,2)]);
## Equation in [ x, y, z ]
## gap>  nf := EquationNormalForm(e);;
## gap> Print(nf.nf);
## FreeProductElm([ x^2*y^2*z^2, (1,2) ])
## gap> e^(nf.hom)=nf.nf;
## true
## gap> nf.nf^(nf.homInv)=e;
## true
## ]]></Example></Description>
##</ManSection>
##
## <ManSection>
## <Oper Name="NormalFormOfEquation" Arg="E"
##		 Label="equation"/>
##   <Returns>The normal form of the equation <A>E</A></Returns>
##   <Description>
##		The argument <A>E</A> needs to be a quadratic equation. For each such
##		equation there exists an equivalent equation in normal form.<P/>
##		The result is an equation in one of the forms
##		<M>O_{n,m},U_{n,m}</M> equivalent to the equation <A>E</A>.
##		The resulting equation has the attributes <E>NormalizingHomomorphism</E>
##		and <E>NormalizingInverseHomomorphism</E> storing in the first case the
##		homomorphism that maps <A>E</A> to the result and in the second case the
##		inverse of this homomorphism. 
## <Example><![CDATA[
## gap> F3 := FreeGroup("x","y","z");; SetName(F3,"F3");
## gap> S4 := SymmetricGroup(4);; SetName(S4,"S4");
## gap> G := EquationGroup(S4,F3);
## S4*F3
## gap> e := Equation(G,[Comm(F3.2,F3.1)*F3.3^2,(1,2)]);
## Equation in [ x, y, z ]
## gap>  nf := NormalFormOfEquation(e);;
## gap> Print(nf);
## FreeProductElm([ x^2*y^2*z^2, (1,2) ])
## gap> e^NormalizingHomomorphism(nf)=nf;
## true
## gap> nf^NormalizingInverseHomomorphism(nf)=e;
## true
## ]]></Example></Description>
##</ManSection>
## <ManSection>
## <Oper Name="Genus" Arg="E"
##		 Label="equation"/>
##   <Returns>The integer that is the genus of the equation</Returns>
##</ManSection>
## <ManSection>
## <Oper Name="EquationSignature" Arg="E"
##		 Label="equation"/>
##   <Returns>The list <A>[n,m]</A> of integers that is the signature of the equation</Returns>
##</ManSection>
## <#/GAPDoc>
DeclareAttribute("EquationNormalForm", IsEquation);
DeclareAttribute("EquationNormalFormNoRename", IsEquation);

DeclareAttribute("NormalFormOfEquation", IsEquation);
DeclareAttribute("NormalizingHomomorphism", IsEquation);
DeclareAttribute("NormalizingInverseHomomorphism", IsEquation);

DeclareAttribute("Genus", IsEquation);
DeclareAttribute("EquationSignature", IsEquation);