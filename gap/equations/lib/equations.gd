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
DeclareOperation("EquationGroup", [IsGroup,IsGroup]);


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
##		 Label="group,list"/>
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
## F2*S4
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
