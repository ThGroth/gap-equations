#############################################################################
##
#O DecompositionEquationGroup . . .create the Decomposition of an EquationGroup
#O DecompositionEquation . . . . . . . . . . . . . .Decompose an Equation
#O EquationComponent
#O EquationComponents
##
## <#GAPDoc Label="DecompositionEquation">
## <ManSection>
## <Oper Name="DecompositionEquationGroup" Arg="G"
##		 Label="group"/>
##   <Returns>A new <A>EquationGroup</A>.</Returns>
##   <Description>
##		If <M>F</M> is the free group on the generating set <M>X</M> then
##		the free group on the gerating set <M>X^n</M> is isomorphic to <M>F^{*n}</M> the
##		<M>n</M>-fold free product of <M>F</M> . 
##		<P/> This method returns the <A>EquationGroup</A> <M>G*F^{*n}</M>.
## </Description>
## </ManSection>
## <ManSection>
## <Oper Name="DecompositionEquation" Arg="G,E,sigma"
##		 Label="equation"/>
##   <Returns>A new equation in <A>G</A> which is the
##	 decomposed of the equation <A>E</A>.</Returns>
##   <Description>
##		The group <A>G</A> needs to be a <A>DecompositionEqationGroup(H)</A>,
##		the equation <A>E</A> needs to be a member of the EquationGroup <M>H=K*F</M>.
##		
##		<P/> The argument <A>sigma</A> needs to be a group homomorphism
##		<M>\simga\colon F\to S_n</M>.
##
##		<P/>
##		The representation of the returned equation stores a list of 
## 		words such that the <M>i</M>-th word represents an element in 
##		<M>G*\phi_i(F)</M>.
## <Example><![CDATA[
## gap> F := FreeGroup(1);; SetName(F,"F");
## gap> G := EquationGroup(GrigorchukGroup,F);
## GrigorchukGroup*F
## gap> DG := DecompositionEquationGroup(G);
## GrigorchukGroup*F*F
## gap>  sigma := GroupHomomorphismByImages(F,SymmetricGroup(2),[(1,2)]);
## [ f1 ] -> [ (1,2) ]
## gap>  e := Equation(G,[F.1^2,GrigorchukGroup.2]);
## Equation in [ f1 ]
## gap>  de := DecompositionEquation(DG,e,sigma);
## DecomposedEquation in [ f11, f12 ]
## gap> Print(de);
## Equation([ FreeProductElm([ f11*f12,a ]), FreeProductElm([ f12*f11,c ]) ])
## ]]></Example>
##   </Description>
##</ManSection>
## <#/GAPDoc>
DeclareOperation("DecompositionEquationGroup", [IsEquationGroup]);
DeclareAttribute("IsDecompositionEquationGroup",IsEquationGroup);

DeclareRepresentation("IsDecomposedEquationRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["words","factors","group","free","const","activity"]
);

DeclareOperation("DecompositionEquation", [IsEquationGroup,IsEquation,IsGroupHomomorphism]);
DeclareOperation("EquationComponent", [IsEquation,IsInt]);
DeclareOperation("EquationComponents", [IsEquation]); 

DeclareAttribute("DecomposedEquationDisjointForm", IsEquation);

DeclareOperation("LiftSolution",[IsEquation, IsEquation, IsGroupHomomorphism, IsList]);