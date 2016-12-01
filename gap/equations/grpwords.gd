###########################################################################
####                                                                   ####
####                    Categories and Representations                 ####
####                                                                   ####
###########################################################################
DeclareCategory("IsGrpWord", IsMultiplicativeElementWithInverse);
DeclareCategory("IsGrpWordHom",IsMultiplicativeElementWithOne);
DeclareCategory("IsFRGrpWord",IsMultiplicativeElementWithInverse);
InstallTrueMethod(IsGrpWord,IsFRGrpWord);

DeclareCategoryCollections("IsGrpWord");

DeclareRepresentation("IsGrpWordRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["word","group"]
);
DeclareRepresentation("IsGrpWordDecomposableRep",
	IsGrpWordRep,["word","group","hom"]
);
DeclareRepresentation("IsGrpWordHomRep", 
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["rules"]
);
DeclareRepresentation("IsFRGrpWordStateRep", 
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["states","activity"]
);
DeclareRepresentation("IsGrpWordStateRep", 
 IsGrpWordDecomposableRep,
 ["word","states","activity","hom","group"]
);

###########################################################################
####                                                                   ####
####                         Constructors                              ####
####                                                                   ####
###########################################################################
#GrpWord: Defines the Group word object given a List L and a Group G. The List can contain 
#					positive numbers representing variables and group elements from the group G.
#					The corresponding Group word is an element of F_\NN * G
#
#GrpWordHom: Defines the GroupWordHom object given a finite list of transitions. The i-th
#						 Entry of the list corresponds to the image of i. So in this way group word homomorphisms
#						 F_\NN * G \to F_\NN *G with finite support can be defined.
#FRGrpWord: Defines the FRGrpWord object given a list L, a permutation p\in S_n and a Group G. 
#						The list L should consist of groupwords over the Group G.
#						The resultin object is an implementation of an element of (F_NN * G)^n \wr S_n
#FRGrpWordUnknown: Defines a FRGroupWord object wich represents the unknowns of the corresponding group.
#									 TODO 
DeclareOperation("GrpWord", [IsList, IsGroup]);
DeclareOperation("GrpWordHom",[IsList]);
DeclareOperation("FRGrpWord",[IsList,IsPerm,IsGroup]);
DeclareOperation("FRGrpWordUnknown",[IsInt,IsPerm,IsFRGroup]);


###########################################################################
####                                                                   ####
####                   Attributes and Properties                       ####
####                                                                   ####
###########################################################################

DeclareAttribute("UnknownsOfGrpWord",IsGrpWord);
DeclareAttribute("GrpWordReducedForm",IsGrpWord);
DeclareAttribute("GrpWordCyclReducedForm",IsGrpWord);
DeclareAttribute("GrpWordNormalFormInverseHom", IsGrpWord);
DeclareAttribute("GrpWordNormalForm", IsGrpWord);
DeclareAttribute("LengthOfGrpWord",IsGrpWord);

DeclareProperty("IsPermGrpWord",IsGrpWord);
DeclareProperty("IsSquareGrpWord", IsGrpWord);
DeclareProperty("IsOrientedGrpWord", IsSquareGrpWord);


###########################################################################
####                                                                   ####
####                          Operations                               ####
####                                                                   ####
###########################################################################

DeclareOperation("GrpWordDecomposable", [IsGrpWord]);

DeclareOperation("GrpWordAsElement",[IsGrpWord]);
DeclareOperation("GrpWordHomCompose",[IsGrpWordHom,IsList,IsGroup]);
DeclareOperation("GrpWordDecomposed",[IsGrpWord]);
DeclareOperation("ImageOfGrpWordHom",[IsGrpWordHom,IsGrpWord]);
DeclareOperation("GrpWordToStates", [IsGrpWord, IsPerm]);

DeclareOperation("GrpWordSolve",[IsGrpWord]);


###########################################################################
####                                                                   ####
####                             Info                                  ####
####                                                                   ####
###########################################################################
InfoFRGW := NewInfoClass("InfoFRGW");
SetInfoLevel(InfoFRGW,1);
