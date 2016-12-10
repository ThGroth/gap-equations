DeclareCategory("IsGeneralFreeProduct", IsGroup);
DeclareRepresentation("IsGeneralFreeProductRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["groups"]
);

DeclareCategory("IsFreeProductElm", IsMultiplicativeElementWithInverse);
DeclareCategoryCollections("IsFreeProductElm");

DeclareRepresentation("IsFreeProductElmRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["word","factors","group"]
);

DeclareCategory("IsFreeProductHomomorphism",IsGroupHomomorphism);
DeclareRepresentation("IsFreeProductHomomorphismRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["homs,Source,Range"]
);
###########################################################################
####                                                                   ####
####                         Constructors                              ####
####                                                                   ####
###########################################################################

DeclareOperation("FreeProductElm", [IsGeneralFreeProduct,IsList,IsList]);


DeclareOperation("Abs", [IsObject]);
DeclareOperation("FreeProductHomomorphism", [IsGeneralFreeProduct, IsGroup, IsList]);