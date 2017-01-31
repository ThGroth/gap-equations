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
##		This method needs <A>G</A> to be an equation group where the
##		group of constants is an fr-group. For <A>G</A> a group with
##		free constant group see 
##		<Ref Oper="DecompositionEquationGroup" Label="group,int,list" Style="Text"/>.
##		If <M>F</M> is the free group on the generating set <M>X</M> then
##		the free group on the gerating set <M>X^n</M> is isomorphic to <M>F^{*n}</M> the
##		<M>n</M>-fold free product of <M>F</M> . 
##		<P/> This method returns the <A>EquationGroup</A> <M>G*F^{*n}</M>.<P/>
## </Description>
## <Oper Name="DecompositionEquationGroup" Arg="G,deg,acts"
##		 Label="group,int,list"/>
##   <Returns>A new <A>EquationGroup</A>.</Returns>
##   <Description>
##		This method needs <A>G</A> to be an equation group where the
##		group of constants is a free group on <M>n&lt;\infty</M> generators.
##		The integer <A>deg</A> is the number of states each element will have.
##		The list <A>acts</A> should be of length <M>n</M> and all elements should
##		be permutation of <A>deg</A> elements. These will represent the activity
##		of the generators of the free group.
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
##		<M>\sigma\colon F\to S_n</M>. Alternatively it can be a list of 
##		elements of <M>S_n</M> it is then regarded as the group homomorphism
##		that maps the <M>i</M>-th variable of <A>eq</A> to the <M>i</M>-th
##		element of the list.
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
## <Example><![CDATA[
## gap> F := FreeGroup("x1","x2");; SetName(F,"F");
## gap> G := FreeGroup("g");; SetName(G,"G");
## gap> eG := EquationGroup(G,F);
## G*F
## gap> DeG := DecompositionEquationGroup(eG,2,[(1,2)]);
## G*G*F*F
## gap>  e := Equation(eG,[Comm(F.1,F.2),G.1^2]);
## Equation in [ x1, x2 ]
## gap>  Print(DecompositionEquation(DeG,e,[(),()]));
## Equation([ FreeProductElm([ x11^-1*x21^-1*x11*x21, g1*g2 ]), 
##  FreeProductElm([ x12^-1*x22^-1*x12*x22, g2*g1 ]) ])
## ]]></Example>
##   </Description>
##</ManSection>
## <ManSection>
## <Oper Name="EquationComponent" Arg="E,i"
##		 Label="equation,int"/>
##   <Returns>The <A>i</A>-th component of the decomposed equation <A>E</A>.</Returns>
##   <Description>
##		Denote by <M>p_i</M> the natural projection <M>(G*F_{X^n})^n\rtimes S_n\to G*F_{X^n}</M>
##		to the <M>i</M>-th factor of the product. Given a decomposed Equation <A>E</A> and 
##		an integer <M>0&lt;</M><A>i</A><M>\leq n</M> 
##		this method returns <M>p_i(E)</M>.<P/>
## </Description>
## <Oper Name="EquationComponents" Arg="E"
##		 Label="equation,int"/>
##   <Returns>The list of all components of the decomposed equation <A>E</A>.</Returns>
##   <Description>
##		Denote by <M>p_i</M> the natural projection <M>p_i\colon(G*F_{X^n})^n\rtimes S_n\to G*F_{X^n}</M>
##		to the <M>i</M>-th factor of the product. Given a decomposed Equation <A>E</A> 
##		this method returns the list <M>[p_1(E),p_2(E),\ldots,p_n(E)]</M>.<P/>
## </Description>
## <Oper Name="EquationActivity" Arg="E"
##		 Label="equation"/>
##   <Returns>The activity of the decomposed equation <A>E</A>.</Returns>
##   <Description>
##		Denote by <M>act</M> the natural projection <M>(G*F_{X^n})\wr S_n\to S_n</M>.
##		Given a decomposed Equation <A>E</A> this method returns <M>act(E)</M>.
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareOperation("DecompositionEquationGroup", [IsEquationGroup]);
DeclareAttribute("IsDecompositionEquationGroup",IsEquationGroup);

DeclareRepresentation("IsDecomposedEquationRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["words","factors","group","free","const","activity"]
);

DeclareOperation("DecompositionEquation", [IsEquationGroup,IsEquation,IsGroupHomomorphism]);
DeclareOperation("EquationComponent", [IsEquation,IsInt]);
DeclareOperation("EquationActivity", [IsEquation]);
DeclareOperation("EquationComponents", [IsEquation]); 

#############################################################################
##
#A DecomposedEquationDisjointForm . . . . . . . . . . . . .DecomposedEquation 
#A LiftSolution. . . . . . Lift solution from decomposed equation to equation
##
## <#GAPDoc Label="DecomposedEquationDisjointForm">
## <ManSection>
## <Oper Name="DecomposedEquationDisjointForm" Arg="E"
##		 Label="equation"/>
##   <Returns>A record with components <A>eq</A> 
##	 and <A>hom</A>.</Returns>
##   <Description>
##		If <A>E</A> is a decomposed equation there may be an 
##		overlap of the set of variables of some components. If <A>E</A> is a quadratic
##		equation there is an equation homomorphism <M>\varphi</M> that 
##		maps each component to a new quadratic equation. Hence all maped components have
##		pairwise disjoint sets of variables. This method computes such an homomorphism
##		<M>\varphi</M> such that the solvability of the system of components remains 
##		unchanged. If <M>s</M> is a solution for the new system of components, then
##		<M>s\circ\varphi</M> is a solution for the old system.<P/> 
##		The method returns a record with two components. <A>hom</A> 
##		is the homomorphism <M>\varphi</M> and <A>eq</A> the new decomposed equation.
## </Description>
## </ManSection>
## <ManSection>
## <Oper Name="LiftSolution" Arg="DE,E,sigma,sol"
##		 Label="equation,equation,equationhom,equationhom"/>
##   <Returns>An evaluation for E <A>eq</A>.</Returns>
##   <Description>
##		Given an equation <A>E</A> and a solution <A>sol</A> for its decomposed equation 
##		<A>DE</A> under the decomposition with activity <A>sigma</A> this method computes a 
##		solution for the equation <A>E</A>.<P/>
##		Note that the solution not neccecarily maps to the group of constants of <A>E</A>
##		but can map to the group where all elements of the group of constants can appear 
##		as states. If the group of constants is layered, this two groups will coincide.
## <Example><![CDATA[
## gap> F := FreeGroup(2);; SetName(F,"F");
## gap> Gr := GrigorchukGroup;; a:=Gr.1;; d:=Gr.4;;
## gap> G := EquationGroup(Gr,F);;
## gap> DG := DecompositionEquationGroup(G);;
## gap>  sigma := GroupHomomorphismByImages(F,SymmetricGroup(2),[(1,2),()]);
## [ f1, f2 ] -> [ (1,2), () ]
## gap>  e := Equation(G,[Comm(F.1,F.2),Comm(d,a)]);
## Equation in [ f1, f2 ]
## gap>  de := DecompositionEquation(DG,e,sigma);
## DecomposedEquation in [ f11, f21, f12, f22 ]
## gap> dedj := DecomposedEquationDisjointForm(de);
## rec( eq := DecomposedEquation in [ f11, f12, f22 ], 
##   hom := [ f21 ]"->"[ FreeProductElm of length 3 ] )
## gap> EquationComponents(dedj.eq);
## [ Equation in [ f11, f12, f22 ], Equation in [  ] ]
## gap> s := EquationEvaluation(DG,EquationVariables(dedj.eq),[One(Gr),One(Gr),Gr.2]);
## MappingByFunction( GrigorchukGroup*F*F, GrigorchukGroup, function( q ) ... end )
## gap> IsSolution(s,EquationComponent(dedj.eq,1));
## true
## gap> ns := dedj.hom*s;; IsEvaluation(ns);
## true
## gap> ForAll(EquationComponents(de),F->IsSolution(ns,F));
## true
## gap> ls := LiftSolution(de,e,sigma,ns);;
## gap> IsSolution(ls,e);
## true
## gap> ForAll(EquationVariables(e),x->Equation(G,[x])^ls in Gr);
## true //only good luck
## ]]></Example>
## </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute("DecomposedEquationDisjointForm", IsEquation);
DeclareOperation("LiftSolution",[IsEquation,IsEquation, IsGroupHomomorphism, IsGroupHomomorphism]);