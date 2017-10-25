###########################################################################
####                                                                   ####
####                    Categories and Representations                 ####
####                                                                   ####
###########################################################################

#############################################################################
##
#C IsEquationGroup. . . . . . . . . . . . . . . . . .free product groups
#O EquationGroup . . . . . . . . . . . . . . . . create an EquationGroup
##
## <#GAPDoc Label="EquationGroup">
## <ManSection>
##   <Filt Name="IsEquationGroup" Arg="obj"/>
##   <Returns><K>true</K> if <A>obj</A> is a general free product over to groups
##		<K>G,F</K> where <K>F</K> is a free group.</Returns>
##   <Description>
##      The free factor <K>F</K> represents the group of variables for the equations.
##   </Description></ManSection><ManSection>
## <Oper Name="EquationGroup" Arg="G,F"
##		 Label="group,group"/>
##   <Returns>A a new <A>G</A>-group for equations over <A>G</A>.</Returns>
##   <Description>
##		Uses the <C>FreeProduct</C> method to create the free product
##		object. The second argument <A>F</A> must be a free group.
## <Example><![CDATA[
## gap> S2 := SymmetricGroup(2);; SetName(S2,"S2");
## gap> F := FreeGroup(infinity,"xn",["x1","x2"]);;SetName(F,"F");
## gap> EqG := EquationGroup(S2,F);
## S2*F
## ]]></Example>
##   </Description>
## </ManSection>
## <#/GAPDoc>
DeclareAttribute( "IsEquationGroup", IsGeneralFreeProduct);
DeclareOperation( "EquationGroup", [IsGroup,IsGroup]);

#############################################################################
##
#O Equation . . . . . . . . . . . . . . . . . . . . .create an EquationGroup
#A EquationVariables . . . . . . . . . . . . . . . . . Variables of Equation
#A EquationLetterRep . . . . . . . . . . . . . . . . . 
#P IsQuadraticEquation . . . . . . . . . . . . . . . . . 
#P IsOrientedEquation . . . . . . . . . . . . . . . . . 
##
## <#GAPDoc Label="Equation">
##<ManSection>
## <Oper Name="Equation" Arg="G,L"
##		 Label="group,list"/>
##   <Returns>A a new element of the equation group <A>G</A></Returns>
##   <Description>
##		Creates a <C>FreeProductElm</C> from the list <A>L</A>. By default 
#		this elements will be cyclical reduced.  
##   </Description>
##</ManSection>
##<ManSection>
## <Attr Name="EquationVariables" Arg="E"
##		 Label="groupelement"/>
##   <Returns>A list of all variables occuring in <A>E</A>.</Returns>
##</ManSection>
##<ManSection>
## <Attr Name="EquationLetterRep" Arg="E"
##		 Label="equation"/>
##   <Returns>A a new element of the equation group <A>G</A> in letter 
## representation which is equal to <A>E</A></Returns>
##   <Description>
##		In the standard representation of an equation the elements of the
##		free group that are not devided by a constant are collected. 
##		In the letter representation they are seperate letters. 
## <Example><![CDATA[
## gap> F2 := FreeGroup(2);; SetName(F2,"F2");
## gap> S4 := SymmetricGroup(4);; SetName(S4,"S4");
## gap> G := EquationGroup(S4,F2);
## S4*F2
## gap> e := Equation(G,[F2.1,F2.2,(1,2),F2.1]);
## Equation in [ f1, f2 ]
## gap> Print(e);
## FreeProductElm([ f1*f2, (1,2), f1 ])
## gap> Print(EquationLetterRep(e));
## FreeProductElm([ f1, f2, (1,2), f1 ])
## ]]></Example>
##   </Description>
##</ManSection>
##<ManSection>
## <Attr Name="EquationLetterRep" Arg="G,L"
##		 Label="group,list"/>
##   <Returns>Creates a new equation in letter representation</Returns>
##</ManSection>
##<ManSection>
## <Prop Name="IsQuadraticEquation" Arg="E"
##		 Label="equation"/>
##   <Returns><K>true</K> if <A>E</A> is an quadratic equation.</Returns>
##   <Description> 
##   </Description>
##</ManSection>
##<ManSection>
## <Prop Name="IsOrientedEquation" Arg="E"
##		 Label="equation"/>
##   <Returns><K>true</K> if <A>E</A> is an oriented quadratic equation.</Returns>
##   <Description>
##   </Description>
##</ManSection>
## <#/GAPDoc>
DeclareOperation("Equation", [IsEquationGroup,IsList]);
DeclareProperty("IsEquation", IsFreeProductElm);

DeclareAttribute("EquationVariables",IsEquation);
DeclareAttribute("EquationLetterRep",IsEquation);

DeclareProperty("IsQuadraticEquation", IsEquation);
DeclareProperty("IsOrientedEquation", IsQuadraticEquation);
#############################################################################
##
#P IsConstrainedEquation . . . . . . . . . . . . . . . . . 
##
## <#GAPDoc Label="ConstrainedEquation">
## <Prop Name="IsConstrainedEquation" Arg="E"
##		 Label="equation"/>
##   <Returns>True if <A>E</A> is a constrained equation.</Returns>
##</ManSection>
## <#/GAPDoc>
DeclareProperty("IsConstrainedEquation", IsEquation);

DeclareOperation("SetEquationConstraint", [IsEquation, IsList, IsGroupHomomorphism	]);

#############################################################################
##
#O EquationHomomorphism . . . . . . . . . . . .create an EquationHomomorphism
#O EquationEvaluation . . . . . . . . . . . . . .create an EquationEvalutaion
#P IsEvalutation . . . . . . . . . . . . . . . Is Homomorphism an evalutation
#O IsSolution . . . . . . . . . . . . . . . . . . .Is an evalution a solution
#A EquationHomomorphismImageData. . . . . . . . . . . . . . . . . . . . . . .
##
## <#GAPDoc Label="EquationHom">
## <ManSection>
## <Oper Name="EquationHomomorphism" Arg="G,vars,imgs"
##		 Label="group,list,list"/>
##   <Returns>A a new homomorphism from <A>G</A> to <A>G</A></Returns>
##   <Description>
##		If <A>G</A> is the group <M>H*F_X</M> the result of this command is
##		a <M>H</M>-homomorphism that maps the <M>i</M>-th variable of the
##		list <A>vars</A> to the <M>i</M>-th member of <A>imgs</A>.
##		Therefore <A>vars</A> can be a list without duplicates of variables.
##		The list <A>imgs</A> can contain elements of the following type:
##		<List>
##		<Item>Element of the group <M>F_X</M></Item>
##		<Item>Elements of the group <M>H</M></Item>
##		<Item>Lists of elements from the groups <M>F_X</M> and <M>H</M>. 
##		The list is then regarded as the corresponding word in <M>G</M></Item>
##		<Item>Elements of the group <M>G</M></Item>
##		</List>
## <Example><![CDATA[
## gap> F3 := FreeGroup(3);; SetName(F3,"F3");
## gap> S4 := SymmetricGroup(4);; SetName(S4,"S4");
## gap> G := EquationGroup(S4,F3);
## S4*F3
## gap> e := Equation(G,[Comm(F3.2,F3.1)*F3.3^2,(1,2)]);
## Equation in [ f1, f2, f3 ]
## gap>  h := EquationHomomorphism(G,[F3.1,F3.2,F3.3],
## > [F3.1*F3.2*F3.3,(F3.2*F3.3)^(F3.1*F3.2*F3.3),(F3.2^-1*F3.1^-1)^F3.3]);
## [ f1, f2, f3 ]"->"[ f1*f2*f3, f3^-1*f2^-1*f1^-1*f2*f3*f1*f2*f3, f3^-1*f2^-1*f1^-1*f3 ]
## gap> Print(e^h);
## FreeProductElm([ f1^2*f2^2*f3^2, (1,2) ])
## ]]></Example></Description>
## </ManSection>
## <ManSection>
## <Oper Name="EquationEvaluation" Arg="G,vars,imgs"
##		 Label="group,list,list"/>
##   <Returns>A a new evaluation from <A>G</A></Returns>
##   <Description>
##	 Works the same as <E>EquationHomomorphism</E> but the 
##	 target of the homomorphism is the group of constants 
##   and all variables which are not specified in in <A>vars</A>
##   are maped to the identity. Hence the only allowed input
##	 for <A>imgs</A> are elements of the group of constants.
## <Example><![CDATA[
## gap> F3 := FreeGroup(3);; SetName(F3,"F3");
## gap> S4 := SymmetricGroup(4);; SetName(S4,"S4");
## gap> G := EquationGroup(S4,F3);
## S4*F3
## gap> e := Equation(G,[Comm(F3.2,F3.1)*F3.3^2,(1,2,3)]);
## Equation in [ f1, f2, f3 ]
## gap>  h := EquationHomomorphism(G,[F3.1,F3.2,F3.3],[(),(),(1,2,3)]);
## [ f1, f2, f3 ]"->"[ (), (), (1,3,2) ]
## gap>  he := EquationEvaluation(G,[F3.1,F3.2,F3.3],[(),(),(1,2,3)]);
## MappingByFunction( S4*F3, S4, function( q ) ... end )
## gap> e^he;
## ()
## gap> IsSolution(he,e);
## true
## ]]></Example>
##   </Description>
##</ManSection>
## <#/GAPDoc>
DeclareProperty("IsEquationHomomorphism",IsFreeProductHomomorphism);

DeclareOperation("EquationHomomorphism", [IsEquationGroup, IsList, IsList]);

DeclareAttribute("EquationHomomorphismImageData", IsGroupHomomorphism, "mutable" );

DeclareOperation("EquationEvaluation", [IsEquation, IsList, IsList]);

DeclareProperty("IsEvaluation", IsGroupHomomorphism);

DeclareOperation("IsSolution", [IsEvaluation, IsEquation]);


###########################################################################
####                                                                   ####
####                             Info                                  ####
####                                                                   ####
###########################################################################
InfoEQFP := NewInfoClass("InfoEQFP");
SetInfoLevel(InfoEQFP,1);
