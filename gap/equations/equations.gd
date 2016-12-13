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
DeclareProperty("IsEquation", IsFreeProductElm);

DeclareAttribute("EquationVariables",IsEquation);
DeclareAttribute("EquationLetterRep",IsEquation);

DeclareProperty("IsQuadraticEquation", IsEquation);
DeclareProperty("IsOrientedEquation", IsQuadraticEquation);

DeclareRepresentation("IsDecomposedEquationRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["words","factors","group","free","const","activity"]
);

DeclareOperation("DecompositionEquation", [IsEquationGroup,IsEquation,IsGroupHomomorphism]);
DeclareOperation("EquationComponent", [IsEquation,IsInt]);
DeclareOperation("EquationComponents", [IsEquation]); 

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
