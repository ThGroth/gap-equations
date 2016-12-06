###########################################################################
####                                                                   ####
####                    Categories and Representations                 ####
####                                                                   ####
###########################################################################


DeclareCategory("IsEquationGroup", IsGroup);


DeclareCategory("IsEquation", IsMultiplicativeElementWithInverse);
DeclareCategoryCollections("IsEquation");

DeclareCategory("IsEquationHomomorphism",IsGroupHomomorphism);
#DeclareCategory("IsFREquation",IsMultiplicativeElementWithInverse);
#InstallTrueMethod(IsEquation,IsFREquation);

#DeclareCategoryCollections("IsEquation");

DeclareRepresentation("IsEquationRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["word","group","free","eqG"]
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
DeclareOperation("EquationGroup", [IsGroup,IsGroup]);
DeclareOperation("Equation", [IsList, IsEquationGroup]);

DeclareOperation("EquationEvaluation", [IsGroupHomomorphism, IsEquation]);
DeclareOperation("EquationPartialEvaluation", [IsGroupHomomorphism, IsEquation]);
DeclareOperation("EquationHomomorphism", [IsEquationGroup, IsGroupHomomorphism, IsGroupHomomorphism]);
#DeclareOperation("FREquation",[IsList,IsPerm,IsGroup]);
#DeclareOperation("FREquationUnknown",[IsInt,IsPerm,IsFRGroup]);


###########################################################################
####                                                                   ####
####                   Attributes and Properties                       ####
####                                                                   ####
###########################################################################

DeclareAttribute("EquationVariables",IsEquation);

DeclareAttribute("EquationReducedForm",IsEquation);
#DeclareAttribute("EquationNormalFormInverseHom", IsEquation);
#DeclareAttribute("EquationNormalForm", IsEquation);
#DeclareAttribute("LengthOfEquation",IsEquation);

#DeclareProperty("IsPermEquation",IsEquation);
DeclareProperty("IsQuadraticEquation", IsEquation);
DeclareProperty("IsOrientedEquation", IsQuadraticEquation);
DeclareOperation("IsSolution", [IsEquationHomomorphism, IsEquation]);


###########################################################################
####                                                                   ####
####                          Operations                               ####
####                                                                   ####
###########################################################################

DeclareOperation("EquationEvaluation", [IsEquation,IsList]);
#DeclareOperation("EquationDecomposable", [IsEquation]);

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
