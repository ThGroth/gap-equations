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


###########################################################################
####                                                                   ####
####                         Constructors                              ####
####                                                                   ####
###########################################################################

DeclareOperation("FreeProductElm", [IsGeneralFreeProduct,IsList,IsList]);