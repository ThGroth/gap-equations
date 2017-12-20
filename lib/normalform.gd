#############################################################################
##
#O EquationNormalForm . . . . . . . . .Compute the normal form of an equation
#O Genus . . . . . . . . . . . . . Compute the genus of a quadratic equation
##
## <#GAPDoc Label="EquationNormalForm">
##
## <ManSection>
## <Attr Name="NormalFormOfEquation" Arg="E"
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
##		</Description>
##</ManSection>
## <ManSection>
## <Attr Name="NormalizingHomomorphism" Arg="E"
##		 Label="equation"/>
##   <Returns>The <C>EquationHomomorphism</C> that maps to <A>E</A></Returns>
##   <Description>
##		Only available if <A>E</A> was obtained via <C>NormalFormOfEquation</C>.
##		</Description>
##</ManSection>
## <ManSection>
## <Attr Name="NormalizingInverseHomomorphism" Arg="E"
##		 Label="equation"/>
##   <Returns>The <C>EquationHomomorphism</C> that maps from <A>E</A></Returns>
##   <Description>
##		Only available if <A>E</A> was obtained via <C>NormalFormOfEquation</C>.
##		This is the inverse homomorphism to <C>NormalizingInverseHomomorphism(E)</C>
### <Example><![CDATA[
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

