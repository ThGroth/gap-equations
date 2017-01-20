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