#############################################################################
##
#W freeproducts.gd                                             Thorsten Groth
##
#H   @(#)$Id$
##
#Y 2016
##
#############################################################################
##
##  This file declares abstract free products of arbitrary groups.
##	In difference to the existing free product methods now free products
##  of free groups are possible.
##
#############################################################################

#############################################################################
##
#C IsGeneralFreeProduct. . . . . . . . . . . . . . . . . .free product groups
#C IsFreeProductElm . . . . . . . . . . . . . elements of free product groups
#C IsFreeProductHomomorphism. . . . . . . homomorphism of free product groups
##
## <#GAPDoc Label="IsGeneralFreeProduct">
## <ManSection>
##   <Filt Name="IsGeneralFreeProduct" Arg="obj"/>
##   <Filt Name="IsFreeProductElm" Arg="obj"/>
##   <Filt Name="IsFreeProductHomomorphism" Arg="obj"/>
##   <Returns><K>true</K> if <A>obj</A> is a general free product,a free 
##			product element, a free product homomorphism.</Returns>
##   <Description>
##      These filters can be used to check weather a given group was created as 
##		general free product etc.
##   </Description>
## </ManSection>
## <#/GAPDoc>
DeclareCategory("IsGeneralFreeProduct", IsGroup);
DeclareCategory("IsFreeProductElm", IsMultiplicativeElementWithInverse);
DeclareCategoryCollections("IsFreeProductElm");
DeclareCategory("IsFreeProductHomomorphism",IsGroupHomomorphism);

###########################################################################
####                                                                   ####
####                         Constructors                              ####
####                                                                   ####
###########################################################################
#O FreeProductElm . . . . . . . . . . . . . . create a free product element
#O FreeProductElmLetterReo . . . . . . . . . create a f.p.e. in letter repr
##
## <#GAPDoc Label="FreeProductElm">
## <ManSection>
##   <Oper Name="FreeProductElm" Arg="group,word,factors"
##		 Label="group,list,list"/>
##   <Oper Name="FreeProductElmLetterRep" Arg="group,word,factors"
##		 Label="group,list,list"/>
##   <Returns>A new element in the group <A>group</A>.</Returns>
##   <Description>
##		This function constructs a new free product element,
##		belonging to the group <A>group</A>.
##	   
##		<P/> <A>words</A> is a dense list of elements of any of the factors
##		of <A>group</A>.
##
##		<P/> <A>factors</A> is a list of integers.
##     <A>word</A>[i] must lie in the factor <A>factors</A>[<A>i</A>] of 
##		<A>group</A>. If this is not the case an error is thrown.
##
##		<P/> <C>FreeProductElmLetterRep</C> does not simplify the word by
##		multipliying neighbored equal factor elements but stores the letters
##		as given.
##
## <Example><![CDATA[
## gap> F2 := FreeGroup(2);; SetName(F2,"F2");
## gap> S4 := SymmetricGroup(4);; SetName(S4,"S4");
## gap> G := FreeProduct(F2,S4);
## F2*S4
## gap> e := FreeProductElm(G,[F2.1,F2.2,(1,2),F2.1],[1,1,2,1]);
## FreeProductElm of length 3
## gap> Print(e^2);
## FreeProductElm([ f1*f2, (1,2), f1^2*f2, (1,2), f1 ])
## gap> Print(FreeProductElmLetterRep(G,[F2.1,F2.2,(1,2),F2.1],[1,1,2,1]));
## FreeProductElm([ f1, f2, (1,2), f1 ])
## ]]></Example>
##   </Description>
## </ManSection>
## <#/GAPDoc>
DeclareOperation("FreeProductElm", [IsGeneralFreeProduct,IsList,IsList]);
DeclareOperation("FreeProductElmLetterRep", [IsGeneralFreeProduct,IsList,IsList]);
#############################################################################
##
#O FreeProductHomomorphism. . . . . . . . . . . create a free product element
##
## <#GAPDoc Label="FreeProductHomomorphism">
## <ManSection>
##   <Oper Name="FreeProductHomomorphism" Arg="source,target,homs"
##		 Label="group,group,list"/>
##   <Returns>A new group homomorphism from <A>source</A> to <A>target</A>.</Returns>
##   <Description>
##		This function constructs a new group homomorphism from the general free
##		product group <A>source</A> to the general free product group <A>target</A>
##		by mapping the factor <C>i</C> by the group homomorphism 
##		<A>homs</A>[<C>i</C>] to the <C>i</C>th factor of <A>target</A>.
##	   
##		<P/> <A>homs</A> is a dense list of group homomorphisms where the source
##		of <A>homs</A>[<C>i</C>] must be the <C>i</C>th factor of <A>source</A> and 
##		the range of <A>homs</A>[<C>i</C>] must be the <C>i</C>th factor of <A>target</A>.
##
## <Example><![CDATA[
## gap> F2 := FreeGroup(2);; SetName(F2,"F2");
## gap> S4 := SymmetricGroup(4);; SetName(S4,"S4");
## gap> A4 := AlternatingGroup(4);; SetName(A4,"A4");
## gap> G := FreeProduct(F2,S4); H := FreeProduct(F2,A4);
## F2*S4
## F2*A4
## gap> hf := GroupHomomorphismByImages(F2,F2,[F2.2,F2.1]);;
## gap> hg := GroupHomomorphismByFunction(S4,A4,s->Comm(s,S4.2));;
## gap> h := FreeProductHomomorphism(G,H,[hf,hg]);
## <mapping: F2*S4 -> F2*A4 >
## gap> e := FreeProductElm(G,[F2.1,F2.2,(1,2),F2.1],[1,1,2,1]);
## FreeProductElm of length 3
## gap> Print(e^h);
## FreeProductElm([ f2*f1*f2 ])
## ]]></Example>
##   </Description>
## </ManSection>
## <#/GAPDoc>
DeclareOperation("FreeProductHomomorphism", [IsGeneralFreeProduct, IsGroup, IsList]);


#############################################################################
##
#R IsGeneralFreeProductRep
##
## <#GAPDoc Label="IsGeneralFreeProductRep">
## <ManSection>
##   <Filt Name="IsGeneralFreeProductRep" Arg="obj"/>
##   <Returns><K>true</K> if <A>obj</A> is a general free product group in standard representation.</Returns>
##   <Description>
##   </Description>
## </ManSection>
## <#/GAPDoc>
##
DeclareRepresentation("IsGeneralFreeProductRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["groups"]
);
#############################################################################
##
#R IsFreeProductElmRep
#R IsFreeProductElmLetterRep
##
## <#GAPDoc Label="IsFreeProductElmRep">
## <ManSection>
##   <Filt Name="IsGeneralFreeProductRep" Arg="obj"/>
##   <Returns><K>true</K> if <A>obj</A> is a general free product element 
##	 in standard/letter storing representation.</Returns>
##   <Description>
##   </Description>
## </ManSection>
## <#/GAPDoc>
##
DeclareRepresentation("IsFreeProductElmRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["word","factors","group"]
);
DeclareRepresentation("IsFreeProductElmLetterRep",
 IsFreeProductElmRep,
 ["word","factors","group"]
);
#############################################################################
##
#R IsFreeProductHomomorphismRep
##
## <#GAPDoc Label="IsFreeProductHomomorphismRep">
## <ManSection>
##   <Filt Name="IsGeneralFreeProductRep" Arg="obj"/>
##   <Returns><K>true</K> if <A>obj</A> is a general free product element 
##	 in standard/letter storing representation.</Returns>
##   <Description>
##   </Description>
## </ManSection>
## <#/GAPDoc>
##
DeclareRepresentation("IsFreeProductHomomorphismRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["homs","Source","Range"]
);
#############################################################################
##
#O Abs. . . . . . . . . . . . . . . . . Ignores the inverses in an assocword
##
## <#GAPDoc Label="Abs">
## <ManSection>
##   <Oper Name="Abs" Arg="obj"
##		 Label="assocword"/>
##   <Returns>An assocword without inverses of generators</Returns>
##   <Description>
##		In the word <A>obj</A> all occurencies of inverse generators are
##		replaced by the coresponding generators.
## <Example><![CDATA[
## gap> F2 := FreeGroup(2);; SetName(F2,"F2");
## gap> w := F2.1^-1*F2.2*F2.1*F2.2^-1;
## f1^-1*f2*f1*f2^-1
## gap> Abs(w);
## (f1*f2)^2
## ]]></Example>
##   </Description>
## </ManSection>
## <#/GAPDoc>
DeclareOperation("Abs", [IsObject]);

DeclareGlobalFunction("FREE_PRODUCTS_REDUCE_WORDS");