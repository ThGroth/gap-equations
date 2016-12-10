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
		local embeddings,names,genInList,FP,last,i;
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
		#FP := FreeGroup(Sum(genInList));
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
    				GeneratorsOfGroup(FP){[last+1..last+genInList[i]]}));
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
				
		FP := FreeGroup(infinity,"yn",names);
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
		local Ob, embeddings,i,construct_map;
		if ForAll(L,IsFreeGroup) then
			TryNextMethod();
		fi;
		Ob := First(FREE_PRODUCT_GROUP_FAMILIES,f->f[1]=L);
		if Ob = fail then
			Ob := Objectify(NewType(
					CollectionsFamily(NewFamily("GeneralFreeProductGroup(..)")), IsGeneralFreeProduct and IsGeneralFreeProductRep),
    				rec(groups := L));
			Add(FREE_PRODUCT_GROUP_FAMILIES,[L,Ob]);
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
		return Ob;
	end);

InstallMethod(GeneratorsOfGroup, "for an GeneralFreeProduct",
	[IsGeneralFreeProduct],
	function(G)
		return List(G!.groups,GeneratorsOfGroup);
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

InstallMethod( FreeProductElm, "For a FreeProduct and a list of letters and a list of corresponding factors",
	[IsGeneralFreeProduct,IsList,IsList],
	function(G,elms,factors)
		local lastfactor,newword,newfactors,i,first,elm,Ob;
		if not Length(elms) = Length(factors) then
			Error("The list of letters must be of the same length as the list of factors");
		fi;
		if not ForAll([1..Length(elms)],i->elms[i] in G!.groups[factors[i]]) then
			Error("elements must be in the corresponding free factor");
		fi;
		#Reduce the word
		lastfactor := 0;
		newword := [];
		newfactors := [];
		first := true;
		for i in [1..Length(elms)] do
			if lastfactor = factors[i] then
				elm := elm*elms[i];
			else
				if first then
					first := false;
				else
					Add(newword,elm);
					Add(newfactors,lastfactor);
				fi;
				lastfactor := factors[i];
				elm := elms[i];
			fi;
		od;
		Add(newword,elm);
		Add(newfactors,lastfactor);
		Ob := Objectify(NewType(ElementsFamily(FamilyObj(G)), IsFreeProductElm and IsFreeProductElmRep),
    		rec(word := newword,
    			factors := newfactors,
       			group := G));
		return Ob;
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
		Print("FreeProductElm(",x!.word,")");
	end);

InstallMethod( ViewObj, "for a FreeProductElm",
   [IsFreeProductElm and IsFreeProductElmRep],
    function( x )
		local s;
		Print("FreeProductElm of length ",Length(x));
	end);

InstallMethod( \=,  "for two FreeProductElms",
		IsIdenticalObj,
    [IsFreeProductElm and IsFreeProductElmRep, IsFreeProductElm and IsFreeProductElmRep],0,
    function( x, y )
			return x!.word = y!.word and x!.factors = y!.factors ; 
		end 
);

InstallMethod( OneOp, "for a FreeProductElm",
	[IsFreeProductElm and IsFreeProductElmRep],
	x -> FreeProductElm(x!.group,[],[]) 
);

InstallOtherMethod( One,"for a GeneralFreeProduct",
    [ IsGeneralFreeProduct ],
    G -> FreeProductElm(G,[],[]) 
);

InstallOtherMethod( \[\], "for an FreeProductElm",
	[IsFreeProductElm and IsFreePrdoductElmRep,IsInt],
	function(w,i) 
		return FreeProductElm(w!.group,[w!.word[i]],[w!.factors[i]]);
	end);

InstallOtherMethod( \{\}, "for an FreeProductElm",
	[IsFreeProductElm and IsFreeProductElmRep,IsList],
	function(w,i) 
		return FreeProductElm(w!.group,w!.word{i},w!.factors{i});
	end);

InstallMethod( \*,   "for two FreeProductElms",
	IsIdenticalObj,
    [ IsFreeProductElm and IsFreeProductElmRep, IsFreeProductElm and IsFreeProductElmRep ],0,
    function( x, y )
		return FreeProductElm(x!.group,
							Concatenation(x!.word,y!.word),
							Concatenation(x!.factors,y!.factors));
   
    end );

InstallMethod( InverseOp, "for a FreeProductElms",
	[IsFreeProductElm and IsFreeProductElmRep],
	function(x)
		return FreeProductElm(x!.group,
							Reversed(List(x!.word,InverseOp)),
							Reversed(x!.factors) );	
	end);