###########################################################################
####                                                                   ####
####                    Categories and Representations                 ####
####                                                                   ####
###########################################################################


DeclareAttribute( "IsEquationGroup", IsGeneralFreeProduct);

DeclareOperation("EquationGroup", [IsGroup,IsGroup]);

DeclareOperation("DecompositionEquationGroup", [IsEquationGroup]);
DeclareAttribute("IsDecompositionEquationGroup",IsEquationGroup);

DeclareOperation("Equation", [IsEquationGroup,IsList]);
DeclareAttribute("IsEquation", IsFreeProductElm);
DeclareOperation("EquationComponent", [IsEquation,IsInt]);
DeclareOperation("EquationComponents", [IsEquation]);
DeclareAttribute("EquationVariables",IsEquation);
DeclareAttribute("EquationLetterRep",IsEquation);

DeclareProperty("IsQuadraticEquation", IsEquation);
DeclareProperty("IsOrientedEquation", IsQuadraticEquation);

DeclareCategory("IsEquationHomomorphism",IsGroupHomomorphism);
DeclareRepresentation("IsEquationHomomorphismRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["mapFree","mapGroup","SourceEqG","Range"]
);

#DeclareCategory("IsFREquation",IsMultiplicativeElementWithInverse);
#InstallTrueMethod(IsEquation,IsFREquation);

#DeclareCategoryCollections("IsEquation");

DeclareRepresentation("IsDecomposedEquationRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["words","group","free","eqG","activity"]
);

#DeclareRepresentation("IsEquationDecomposableRep",
#	IsEquationRep,["word","group","hom"]
#);
#DeclareRepresentation("IsEquationHomRep", 
# IsComponentObjectRep  and IsAttributeStoringRep,
# ["rules"]
#);
#DeclareRepresentation("IsFREquationStateRep", 
# IsComponentObjectRep  and IsAttributeStoringRep,
# ["states","activity"]
#);
#DeclareRepresentation("IsEquationStateRep", 
# IsEquationDecomposableRep,
# ["word","states","activity","hom","group"]
#);

###########################################################################
####                                                                   ####
####                         Constructors                              ####
####                                                                   ####
###########################################################################
#Equation: Defines the equation object given a List L, a Group G and 
# a free group F. The list contains elements of both groups regarding
# the elements of G as constants and the elments of F as variables.
#
#EquationHom: Defines the GroupWordHom object given a finite list of transitions. The i-th
#						 Entry of the list corresponds to the image of i. So in this way group word homomorphisms
#						 F_\NN * G \to F_\NN *G with finite support can be defined.
#FREquation: Defines the FREquation object given a list L, a permutation p\in S_n and a Group G. 
#						The list L should consist of groupwords over the Group G.
#						The resultin object is an implementation of an element of (F_NN * G)^n \wr S_n
#FREquationUnknown: Defines a FRGroupWord object wich represents the unknowns of the corresponding group.
#									 TODO 

							




DeclareOperation("EquationEvaluation", [IsGroupHomomorphism, IsEquation]);
DeclareOperation("EquationPartialEvaluation", [IsGroupHomomorphism, IsEquation]);
DeclareOperation("EquationHomomorphism", [IsEquationGroup, IsGroup, IsGroupHomomorphism, IsGroupHomomorphism]);

DeclareAttribute( "EquationHomomorphismImageData", IsEquationHomomorphism, "mutable" );
#DeclareOperation("FREquation",[IsList,IsPerm,IsGroup]);
#DeclareOperation("FREquationUnknown",[IsInt,IsPerm,IsFRGroup]);


###########################################################################
####                                                                   ####
####                   Attributes and Properties                       ####
####                                                                   ####
###########################################################################





#DeclareAttribute("EquationNormalFormInverseHom", IsEquation);
#DeclareAttribute("EquationNormalForm", IsEquation);
#DeclareAttribute("LengthOfEquation",IsEquation);

#DeclareProperty("IsPermEquation",IsEquation);
DeclareProperty("IsReducedEquation", IsEquation);
DeclareProperty("IsEquationLetterRep", IsEquation);
);
DeclareOperation("IsSolution", [IsEquationHomomorphism, IsEquation]);


###########################################################################
####                                                                   ####
####                          Operations                               ####
####                                                                   ####
###########################################################################

DeclareOperation("EquationEvaluation", [IsEquation,IsList]);



DeclareOperation("DecompositionEquation", [IsEquation,IsGroupHomomorphism,IsEquationGroup]);


#DeclareOperation("EquationAsElement",[IsEquation]);
#DeclareOperation("EquationHomCompose",[IsEquationHom,IsList,IsGroup]);
#DeclareOperation("EquationDecomposed",[IsEquation]);
#DeclareOperation("ImageOfEquationHom",[IsEquationHom,IsEquation]);
#DeclareOperation("EquationToStates", [IsEquation, IsPerm]);

#DeclareOperation("EquationSolve",[IsEquation]);


###########################################################################
####                                                                   ####
####                             Info                                  ####
####                                                                   ####
###########################################################################
InfoFRGW := NewInfoClass("InfoFRGW");
SetInfoLevel(InfoFRGW,1);
