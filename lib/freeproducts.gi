#################################################################################
####                                                                         ####
####	                 Free Products of Free groups                        ####
####                                                                         ####
#################################################################################
#
# Taken analously to Position in lib/wordrep.gi
InstallMethod( \in, "for infinite list of generators",
	[IsObject,IsList and IsInfiniteListOfGeneratorsRep],
	function(elm,List)
		local ext;
	    if FamilyObj( elm ) <> List![1] then
    	  return false;
    	fi;
	    if IsAssocWord( elm ) then
      		ext:=LetterRepAssocWord(elm);
      		if Length(ext)<> 1 or ext[1]<0 then
        		return false;
      		else
        		return true;
      		fi;
    	else
      		ext:= ExtRepOfObj( elm );
      		if not IsInt( ext ) then
        		return false;
      		else
        		return true;
      		fi;
    	fi;
    end );



InstallMethod(FreeProductOp, "for f.g. free groups",
	[IsList,IsFreeGroup],
	function(L,G)
		local embeddings,names,genInList,FP,last,i,sorter;
		if not ForAll(L,IsFreeGroup) then 
			TryNextMethod();
		fi;
		if not ForAll(L,IsFinitelyGeneratedGroup) then 
			TryNextMethod();
		fi;
		genInList  := List(L, H->Length(GeneratorsOfGroup(H)));
		embeddings :=[];
		names := Concatenation(List([1..Length(L)],
				i->List([1..genInList[i]],
					j->Concatenation(String(L[i].(j)),String(i)) )));
		sorter:=Sortex(names); #want to collect all states of one element
		FP:=FreeGroup(names);
		if ForAll(L,HasName) then
			SetName(FP,Concatenation(Concatenation(
				List(L{[1..Size(L)-1]},H->Concatenation(Name(H),"*")),
				[Name(L[Size(L)])])));
		fi;

    	last := 0;
    	for i in [1..Length(L)] do
    		Add(embeddings,GroupHomomorphismByImages(
    				L[i],
    				FP,
    				GeneratorsOfGroup(FP){List([last+1..last+genInList[i]],i->i^sorter)}));
    				#GeneratorsOfGroup(FP){[last+1..last+genInList[i]]}));
    		last := last+genInList[i];
    	od;
        SetFreeProductInfo( FP, 
        rec( groups := L,
             embeddings := embeddings ) );
    	return FP;   
	end);

InstallOtherMethod(Abs, "for associative words",
	[IsAssocWord],
	w-> AssocWordByLetterRep(FamilyObj(w),List(LetterRepAssocWord(w),AbsInt))
	);

InstallMethod(FreeProductOp, "for infinitely generated free groups",
	[IsList,IsFreeGroup],
	function(L,G)
		local embeddings,FP,i,names,nameLen,construct_map;
		if not ForAll(L,IsFreeGroup) then 
			TryNextMethod();
		fi;
		if ForAny(L,IsFinitelyGeneratedGroup) then 
			TryNextMethod();
		fi;
		embeddings :=[];
		#If all groups have the same length of init names
		#give good new names
		nameLen := Length(FamilyObj(Representative(G))!.names![2]);
		if ForAll(L,H->Length(FamilyObj(Representative(H))!.names![2])=nameLen) then
			names := Concatenation(List([1..nameLen],
				i->List([1..Length(L)],
				j->Concatenation(FamilyObj(Representative(L[j]))!.names![2][i],String(j)) )));	
		else
			names := [];
		fi;
				
		FP := FreeGroup(infinity,"Xn",names);
		if ForAll(L,HasName) then
			SetName(FP,Concatenation(Concatenation(
				List(L{[1..Size(L)-1]},H->Concatenation(Name(H),"*")),
				[Name(L[Size(L)])])));
		fi;
		#Thanks to Alexander Konovalov,
		#See http://math.stackexchange.com/questions/2048106
		construct_map := i -> (w-> AssocWordByLetterRep(FamilyObj(Representative(FP)),
    					List(LetterRepAssocWord(w),k->SignInt(k)*(Length(L)*(AbsInt(k)-1)+i)) ));
    	for i in [1..Length(L)] do
    			Add(embeddings,GroupHomomorphismByFunction(
    				L[i],
    				FP,
    				construct_map(i) ));
       	od;
        SetFreeProductInfo( FP, 
        rec( groups := L,
             embeddings := embeddings ) );
    	return FP;   
	end);
#################################################################################
####                                                                         ####
####	         Free Products of arbitrary groups     			 			 ####
####                                                                         ####
#################################################################################
FREE_PRODUCT_GROUP_FAMILIES := [];
InstallMethod(FreeProductOp, "For arbitrary groups",
	[IsList,IsGroup],
	function(L,G)
		local H;
		#How to avoid using this method when 
		#IsomorphismFpGroup(G) gives a result?
		if ForAll(L,G->	IsFpGroup(G) and IsFinitelyGeneratedGroup(G)or 
						#IsSymmetricGroup(G) or 
						#IsAlternatingGroup(G) or 
						(IsFreeGroup(G) and IsFinitelyGeneratedGroup(G)) )then
			TryNextMethod(); #Here the standard version from lib/gprd.gi works	
		fi;
		if ForAll(L,IsFreeGroup) and ForAll(L,H->not IsFinitelyGeneratedGroup(H)) then
			TryNextMethod();
		fi;
		H := Group([()]);
		SetFreeProductInfo(H,rec(groups:=L));
		return GeneralFreeProduct(H);
	end);

InstallMethod( \[\], "for infinite list of generators",
	[IsList and IsFreeProductInfiniteListOfGenerators,IsInt],
	function(L,i)
		local G,j,groups;
		if Length(L![2])>= i then
			return L![2][i];
		fi;
		G := First(FREE_PRODUCT_GROUP_FAMILIES,K->K[3]=L![1]);
		for j in [1..Size(G[1])] do
			if not IsFinitelyGeneratedGroup(G[1][j]) then
				return ImageElm(Embedding(G[2],j), G[1][j].(i-Length(L![2])));
			fi;
		od;
    end );

InstallMethod(GeneralFreeProduct, "For a group",
	[ IsGroup and HasFreeProductInfo],
	function(G)
		local L,Ob, embeddings,i,construct_map;
		if IsGeneralFreeProduct(G) then
			return G;
		fi;
		L := FreeProductInfo(G).groups;
		Ob := First(FREE_PRODUCT_GROUP_FAMILIES,f->f[1]=L);
		if Ob = fail then
			Ob := Objectify(NewType(
					CollectionsFamily(NewFamily("GeneralFreeProductGroup(..)")), IsGeneralFreeProduct and IsGeneralFreeProductRep),
    				rec(groups := L));
			Add(FREE_PRODUCT_GROUP_FAMILIES,[L,Ob,FamilyObj(Ob)]);
			SetIsWholeFamily(Ob,true);
		else
			Ob := Ob[2];
		fi;
		#Set the name to L[1]*L[2]*…*L[n]
		if ForAll(L,HasName) then
			SetName(Ob,Concatenation(Concatenation(
				List(L{[1..Size(L)-1]},H->Concatenation(Name(H),"*")),
				[Name(L[Size(L)])])));
		fi;
		embeddings := [];
		construct_map := i -> (x->FreeProductElm(Ob,[x],[i]));
		for i in [1..Length(L)] do
    		Add(embeddings,GroupHomomorphismByFunction(
    				L[i],
    				Ob,
    				construct_map(i) ));
       	od;
       	Ob!.embeddings := embeddings;
		SetKnowsHowToDecompose(Ob,false);
		SetFreeProductInfo( Ob, 
        rec( groups := L,
             embeddings := embeddings ) );
		if Size(Filtered([1..Length(L)],i->not IsFinitelyGeneratedGroup(L[i])))<2 then
			GeneratorsOfGroup(Ob);
		fi;
		return Ob;
		
	end);

InstallMethod( PrintObj, "for a GeneralFreeProduct",
   [IsGeneralFreeProduct],
    function( x )
		if HasName (x) then
			Print(Name(x));	
		else
			Print("<free product group>");
		fi;
	end);
InstallMethod( ViewObj, "for a GeneralFreeProduct",
   [IsGeneralFreeProduct],
    function( x )
		if HasName (x) then
			Print(Name(x));	
		else
			Print("<free product group>");
		fi;
	end);

InstallMethod( \=,  "for two GeneralFreeProducts",
	IsIdenticalObj,
    [ IsGeneralFreeProduct, IsGeneralFreeProduct],0,
    function( x, y )
			return x!.groups = y!.groups;
		end 
);

InstallMethod(GeneratorsOfGroup, "for an f.g. GeneralFreeProduct",
	[IsGeneralFreeProduct],
	function(G)
		local inf,fin,init,res;
		inf := Filtered([1..Length(G!.groups)],i->not IsFinitelyGeneratedGroup(G!.groups[i]));
		if Length(inf)=1 then
			fin := Filtered([1..Length(G!.groups)],i->IsFinitelyGeneratedGroup(G!.groups[i]));
			init := Concatenation(List(fin,i->List(GeneratorsOfGroup(G!.groups[i]),
						gen -> gen^Embedding(G,i) )));
			res:= InfiniteListOfGenerators(FamilyObj(G),init);
			SetIsFreeProductInfiniteListOfGenerators(res,true);
			return res;

		elif Length(inf)=0 then
			return Concatenation(List([1..Length(G!.groups)],
				i->List(GeneratorsOfGroup(G!.groups[i]),
					gen -> gen^Embedding(G,i) )));
		else
			TryNextMethod();
		fi;
	end);

InstallMethod( \=,  "for two GeneralFreeProducts",
	IsIdenticalObj,
    [ IsGeneralFreeProduct, IsGeneralFreeProduct],0,
    function( x, y )
			return x!.groups = y!.groups;
		end 
);
#################################################################################
####                                                                         ####
####					         Free ProductsElm     			 			 ####
####                                                                         ####
#################################################################################
InstallGlobalFunction(FREE_PRODUCTS_REDUCE_WORDS,function(w,factors)
	local lastfactor,newword,newfactors,first,i,elm;
		lastfactor := 0;
		newword := [];
		newfactors := [];
		first := true;
		for i in [1..Length(w)] do
			if lastfactor = factors[i] then
				elm := elm*w[i];
			else
				if first then
					first := false;
					elm := w[i];
					lastfactor := factors[i];
				else
					if not IsOne(elm) then
						Add(newword,elm);
						Add(newfactors,lastfactor);
						elm := w[i];
						lastfactor := factors[i];
					elif Length(newfactors)>0 and factors[i]=newfactors[Length(newfactors)] then
						lastfactor := Remove(newfactors);
						elm := Remove(newword)*w[i];
					else
						elm := w[i];
						lastfactor := factors[i];
					fi;
				fi;
			fi;
		od;
		if Length(w)>0 and not IsOne(elm)then
			Add(newword,elm);
			Add(newfactors,lastfactor);
		fi;
		return rec(word:=newword,factors:=newfactors);
	end);

InstallMethod( FreeProductElm, "For a FreeProduct and a list of letters and a list of corresponding factors",
	[IsGeneralFreeProduct,IsList,IsList],
	function(G,elms,factors)
		local red;
		if not Length(elms) = Length(factors) then
			Error("The list of letters must be of the same length as the list of factors");
		fi;
		#if not ForAll([1..Length(elms)],i->elms[i] in G!.groups[factors[i]]) then
		if not ForAll([1..Length(elms)],
			i->CollectionsFamily(FamilyObj(elms[i])) = FamilyObj(G!.groups[factors[i]])) then
			Error("elements must be in the corresponding free factor");
		fi;
		#Reduce the word
		red := FREE_PRODUCTS_REDUCE_WORDS(elms,factors);
		return Objectify(NewType(ElementsFamily(FamilyObj(G)), IsFreeProductElm and IsFreeProductElmRep),
    		rec(word := red.word,
    			factors := red.factors,
       			group := G));
	end);

InstallMethod( FreeProductElmNC, "For a FreeProduct and a list of letters and a list of corresponding factors",
	[IsGeneralFreeProduct,IsList,IsList],
	function(G,elms,factors)
		local red;
		if not Length(elms) = Length(factors) then
			Error("The list of letters must be of the same length as the list of factors");
		fi;
		#Reduce the word
		red := FREE_PRODUCTS_REDUCE_WORDS(elms,factors);
		return Objectify(NewType(ElementsFamily(FamilyObj(G)), IsFreeProductElm and IsFreeProductElmRep),
    		rec(word := red.word,
    			factors := red.factors,
       			group := G));
	end);

InstallMethod( FreeProductElmLetterRep, "For a FreeProduct and a list of letters and a list of corresponding factors",
	[IsGeneralFreeProduct,IsList,IsList],
	function(G,elms,factors)
		local lastfactor,newword,newfactors,i,first,elm,Ob;
		if not Length(elms) = Length(factors) then
			Error("The list of letters must be of the same length as the list of factors");
		fi;
		if not ForAll([1..Length(elms)],i->elms[i] in G!.groups[factors[i]]) then
			Error("elements must be in the corresponding free factor");
		fi;
		Ob := Objectify(NewType(ElementsFamily(FamilyObj(G)), IsFreeProductElm and IsFreeProductElmLetterRep),
    		rec(word := elms,
    			factors := factors,
       			group := G));
		return Ob;
	end);

InstallMethod( FreeProductElmLetterRepNC, "For a FreeProduct and a list of letters and a list of corresponding factors",
	[IsGeneralFreeProduct,IsList,IsList],
	function(G,elms,factors)
		local lastfactor,newword,newfactors,i,first,elm,Ob;
		if not Length(elms) = Length(factors) then
			Error("The list of letters must be of the same length as the list of factors");
		fi;
		Ob := Objectify(NewType(ElementsFamily(FamilyObj(G)), IsFreeProductElm and IsFreeProductElmLetterRep),
    		rec(word := elms,
    			factors := factors,
       			group := G));
		return Ob;
	end);

InstallOtherMethod( FreeProductElmLetterRep, "For a FreeProductElm",
	[IsFreeProductElm and IsFreeProductElmRep],
	function(elm)
		local nw,nfactors,i,l;
		nw := [];
		nfactors := [];
		for i in [1..Length(elm)] do
			if IsAssocWord(elm!.word[i]) then
				for l in LetterRepAssocWord(elm!.word[i]) do
					Add(nw,AssocWordByLetterRep(FamilyObj(elm!.word[i]),[l]));
					Add(nfactors,elm!.factors[i]);
				od;
			else
				Add(nw,elm!.word[i]);
				Add(nfactors,elm!.factors[i]);
			fi;
		od;
		return FreeProductElmLetterRepNC(elm!.group,nw,nfactors);
	end);

InstallOtherMethod( FreeProductElmLetterRep, "For a FreeProductElm and an integer",
	[IsFreeProductElm and IsFreeProductElmRep, IsInt],
	function(elm,factor)
		local nw,nfactors,i,l;
		nw := [];
		nfactors := [];
		for i in [1..Length(elm)] do
			if elm!.factors[i] = factor and IsAssocWord(elm!.word[i]) then
				for l in LetterRepAssocWord(elm!.word[i]) do
					Add(nw,AssocWordByLetterRep(FamilyObj(elm!.word[i]),[l]));
					Add(nfactors,elm!.factors[i]);
				od;
			else
				Add(nw,elm!.word[i]);
				Add(nfactors,elm!.factors[i]);
			fi;
		od;
		return FreeProductElmLetterRepNC(elm!.group,nw,nfactors);
	end);

InstallOtherMethod( Length, "for a FreeProductElm",
	[IsFreeProductElm and IsFreeProductElmRep],
	function(x)
		return Length(x!.word);
	end);

InstallOtherMethod( Position, "for an FreeProductElm and a group element and an offset",
	[IsFreeProductElm and IsFreeProductElmRep,IsMultiplicativeElementWithInverse, IsInt],
	function(x,elm,from)
		return Position(x!.word,elm,from);
	end);

InstallMethod( PrintObj, "for a FreeProductElm",
   [IsFreeProductElm and IsFreeProductElmRep],
    function( x )
		local s;
		if ForAll(x!.word,HasName) then
			Print("FreeProductElm(",List(x!.word,Name),")");	
		else
			Print("FreeProductElm(",x!.word,")");
		fi;
	end);

InstallMethod( ViewObj, "for a FreeProductElm",
   [IsFreeProductElm and IsFreeProductElmRep],
    function( x )
		local s,l;
		if Length(x!.word)=0 then
			Print("<identity>");
		elif ForAll(x!.word,y->HasName(y) or Length(StringView(y))<8) then
			s := "(";
			l := 0;
			for l in [1..Size(x!.word)-1] do
				Append(s,Concatenation(StringView(x!.word[l]),","));
			od;
			Append(s,Concatenation(StringView(x!.word[l+1]),")"));
			Print(s);
		else
			Print("<Free product element of length ",Length(x),">");
		fi;
	end);

InstallMethod( \=,  "for two FreeProductElms",
		IsIdenticalObj,
    [IsFreeProductElm and IsFreeProductElmRep, IsFreeProductElm and IsFreeProductElmRep],0,
    function( x, y )
			return x!.word = y!.word and x!.factors = y!.factors ; 
		end );
InstallMethod( \=,  "for two FreeProductElms first in LetterRep",
		IsIdenticalObj,
    [IsFreeProductElm and IsFreeProductElmLetterRep, IsFreeProductElm and IsFreeProductElmRep],0,
    function( x, y )
			return FreeProductElm(x!.group,x!.word,x!.factors) = y ; 
		end );
InstallMethod( \=,  "for two FreeProductElms both in LetterRep",
		IsIdenticalObj,
    [IsFreeProductElm and IsFreeProductElmLetterRep, IsFreeProductElm and IsFreeProductElmLetterRep],0,
    function( x, y )
			return FreeProductElm(x!.group,x!.word,x!.factors) = FreeProductElm(y!.group,y!.word,y!.factors) ; 
		end );
InstallMethod( \=,  "for two FreeProductElms second in LetterRep",
		IsIdenticalObj,
    [IsFreeProductElm and IsFreeProductElmRep, IsFreeProductElm and IsFreeProductElmLetterRep],0,
    function( x, y )
			return x = FreeProductElm(y!.group,y!.word,y!.factors) ;
		end 
);

InstallMethod(\<,"for two FreeProductElms",IsIdenticalObj,
  [IsFreeProductElm and IsFreeProductElmRep, IsFreeProductElm and IsFreeProductElmRep],0,
	function(x,y)
	local i;
	  if x!.factors = y!.factors then
	  	i := First([1..Length(x!.word)],i-> not x!.word[i] = y!.word[i]);
	  	if i = fail then return false; fi;
	  	return x!.word[i]<y!.word[i];
	  else 
	  	return x!.factors < y!.factors;
	  fi;
	end);

InstallMethod( OneOp, "for a FreeProductElm",
	[IsFreeProductElm and IsFreeProductElmRep],
	x -> FreeProductElm(x!.group,[],[]) 
);

InstallOtherMethod( One,"for a GeneralFreeProduct",
    [ IsGeneralFreeProduct ],
    G -> FreeProductElm(G,[],[]) 
);

InstallOtherMethod( \[\], "for an FreeProductElm",
	[IsFreeProductElm and IsFreeProductElmRep,IsInt],
	function(w,i) 
		return FreeProductElmNC(w!.group,[w!.word[i]],[w!.factors[i]]);
	end);

InstallOtherMethod( \{\}, "for an FreeProductElm",
	[IsFreeProductElm and IsFreeProductElmRep,IsList],
	function(w,i) 
		return FreeProductElmNC(w!.group,w!.word{i},w!.factors{i});
	end);

InstallMethod( \*,   "for two FreeProductElms",
	IsIdenticalObj,
    [ IsFreeProductElm and IsFreeProductElmRep, IsFreeProductElm and IsFreeProductElmRep ],0,
    function( x, y )
		return FreeProductElmNC(x!.group,
							Concatenation(x!.word,y!.word),
							Concatenation(x!.factors,y!.factors));
   
    end );

InstallMethod( InverseOp, "for a FreeProductElms",
	[IsFreeProductElm and IsFreeProductElmRep],
	function(x)
		return FreeProductElmNC(x!.group,
							Reversed(List(x!.word,InverseOp)),
							Reversed(x!.factors) );	
	end);

#################################################################################
####                                                                         ####
####    	         Free Products Homomorphisms     			 			 ####
####                                                                         ####
#################################################################################
InstallMethod(FreeProductHomomorphism ,"For a GeneralFreeProduct and a list of group homomorphisms",
	[IsGeneralFreeProduct, IsGeneralFreeProduct, IsList],
	function(G,H,homs)
		local fam;
		if not Length(G!.groups) = Length(homs) then
			Error("There need to be as many homomorphisms as free factors in the source.");
		elif not Length(H!.groups) = Length(homs) then
			TryNextMethod();
			#Error("There need to be as many homomorphisms as free factors in the image.");
		elif not ForAll([1..Length(G!.groups)],i->Source(homs[i])=G!.groups[i]) then
			Error("Sources do not match.");
		elif not ForAll([1..Length(G!.groups)],i->Range(homs[i])=H!.groups[i]) then
			TryNextMethod();
			#Error("Ranges do not match.");
		fi;
		fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(G)),
									 ElementsFamily(FamilyObj(H)) );
		return Objectify(NewType(fam,IsFreeProductHomomorphism and IsFreeProductHomomorphismFactorwiseRep),
							rec(	homs := homs,
									Source := G,
									Range := H));
	end);

InstallMethod(FreeProductHomomorphism ,"For a GeneralFreeProduct and a list of group homomorphisms",
	[IsGeneralFreeProduct, IsGroup, IsList],
	function(G,H,homs)
		local fam;
		if not Length(G!.groups) = Length(homs) then
			Error("There need to be as many homomorphisms as free factors in the source.");
		elif not ForAll([1..Length(G!.groups)],i->Source(homs[i])=G!.groups[i]) then
			Error("Sources do not match.");
		elif not ForAll([1..Length(G!.groups)],i->Range(homs[i])=H) then
			TryNextMethod();
		fi;

		fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(G)),
									 ElementsFamily(FamilyObj(H)) );
		return Objectify(NewType(fam,IsFreeProductHomomorphism and IsFreeProductHomomorphismRep),
							rec(	homs := homs,
									Source := G,
									Range := H));
	end);

InstallMethod(Source ,"For a FreeProductHomomorphism",
	[IsFreeProductHomomorphism],
	function(hom)
		return hom!.Source;
	end);

InstallMethod(Range ,"For a FreeProductHomomorphism",
	[IsFreeProductHomomorphism],
	function(hom)
		return hom!.Range;
	end);

InstallMethod( CompositionMapping2, "For two FreeProductHomomorphisms",
	FamSource1EqFamRange2,
	[IsFreeProductHomomorphism,IsFreeProductHomomorphism],0,
	function(hom2,hom1)
		return FreeProductHomomorphism(Source(hom1),Range(hom2),
			List([1..Length(hom1!.homs)],i->hom1!.homs[i]*hom2!.homs[i]) );
	end	);

#InstallMethod( IdentityMapping,
#    "for a FreeProduct Group",
#    true,
#    [ IsGeneralFreeProduct], 0,
#    function( G )
#	    return FreeProductHomomorphism(G,G,List(G!.groups,IdentityMapping));
#    end );

InstallMethod(ImageElm ,"For a FreeProductHomomorphism and a GeneralFreeProduct",
	[IsFreeProductHomomorphism and IsFreeProductHomomorphismFactorwiseRep,IsFreeProductElm and IsFreeProductElmRep],
	function(hom,elm)
		local img;
		img := List([1..Length(elm!.word)],i->
				Image(hom!.homs[elm!.factors[i]],elm!.word[i]));
		return FreeProductElm(Range(hom),img,elm!.factors);
	end);

InstallMethod(ImageElm ,"For a FreeProductHomomorphism and a GeneralFreeProduct",
	[IsFreeProductHomomorphism and IsFreeProductHomomorphismRep,IsFreeProductElm and IsFreeProductElmRep],
	function(hom,elm)
		return Product([1..Length(elm!.word)],i->
				Image(hom!.homs[elm!.factors[i]],elm!.word[i]));
	end);