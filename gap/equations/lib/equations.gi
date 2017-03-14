#################################################################################
####                                                                         ####
####	                          EquationGroup                              ####
####                                                                         ####
#################################################################################
InstallMethod( IsEquationGroup,   "for a FreeProduct)",
   [ IsGeneralFreeProduct],
    G->Length(G!.groups)=2 and IsFreeGroup(G!.groups[2])
	);

InstallMethod( EquationGroup, "for two groups",
	[IsGroup,IsFreeGroup],
	function(G,Free)
		local Ob;
		Ob := GeneralFreeProduct(FreeProduct(G,Free));
		Ob!.free :=Free;
		Ob!.const :=G;
		SetIsEquationGroup(Ob,true);
		return Ob;
	end);


#################################################################################
####                                                                         ####
####	                          Equations                                  ####
####                                                                         ####
#################################################################################
InstallMethod( Equation, "(Equation) for a list of group elements and unknowns and boolean",
	[IsEquationGroup,IsList],
	function(eqG,elms)
		local eq;
		#always reduce equation cyclicaly 
		if Length(elms)>= 1 and elms[1] in eqG!.const then
			elms := Concatenation(elms{[2..Size(elms)]},[elms[1]]);
		fi;
		eq := FreeProductElm(eqG,elms,List(elms,function(e)
													if e in eqG!.const then
														return 1; 
													fi; return 2;
												 end) );
		eq!.const := eqG!.const;
		eq!.free := eqG!.free;
		SetIsEquation(eq,true);
		return eq;
	end);

InstallOtherMethod( Equation, "For a FreeProductElm",
	[IsFreeProductElm],
	function(elm)
		if not IsEquationGroup(elm!.group) then
			TryNextMethod();
		fi;
		elm!.const := elm!.group!.const;
		elm!.free := elm!.group!.free;
		SetIsEquation(elm,true);
		return elm;
	end);

InstallMethod( IsEquation, "For a FreeProductElm",
	[IsFreeProductElm],
	function(elm)
		return IsEquationGroup(elm!.group) and IsBound(elm!.const) and IsBound(elm!.free);
	end);

InstallMethod(EquationLetterRep, "for an Equation",
	[IsEquation and IsFreeProductElmRep],
	function(eq)
		local nw,elm,i,Eq;
		nw := [];
		for elm in eq!.word do
			if elm in eq!.const then
				Add(nw,elm); 
			else
				for i in LetterRepAssocWord(elm) do
					Add(nw,AssocWordByLetterRep(FamilyObj(elm),[i]));
				od;
			fi;
		od;
		Eq:= FreeProductElmLetterRep(eq!.group,nw,List(nw,function(e)
													if e in eq!.const then
														return 1;
													fi; return 2;
												 end) );
		return Equation(Eq);
	end);

InstallMethod( EquationVariables, "for a Equation",
	[IsEquation and IsFreeProductElmRep],
	function(x)
		return List(Set(List(Concatenation(
			List(Filtered(x!.word,e->e in x!.free),	fw -> LetterRepAssocWord(fw))
			),i->AbsInt(i))),
			v->AssocWordByLetterRep(FamilyObj(One(x!.free)),[v]));
	end);

InstallMethod( ViewObj,   "for Equations)",
   [ IsEquation and IsFreeProductElmRep ],
    function( x )
		local s;
		Print("Equation in ",EquationVariables(x));
	end);

InstallMethod( OneOp, "for an Equation",
	[IsEquation and IsFreeProductElmRep],
	x -> Equation(x!.group,[]) 
	);

InstallOtherMethod( One,"for an EquationGroup",
    [ IsEquationGroup ],
    eqG -> Equation(eqG,[]) 
	);



InstallMethod( IsQuadraticEquation, "for a Equation",
		[IsEquation and IsFreeProductElmRep],
		function(x)
			local i,Val;
			Val := rec();
			for i in Concatenation(List(
					Filtered(x!.word,e->e in x!.free),
					fw -> LetterRepAssocWord(fw)
					)) do
				i := AbsInt(i);
				if IsBound(Val.(i)) then
					if Val.(i) > 1 then
						return false;
					fi;
					Val.(i) := 2;	
				else
					Val.(i) := 1;
				fi;
			od;
			return true;
		end
);

InstallMethod( IsOrientedEquation, "for a square Equation",
		[IsQuadraticEquation],
		function(x)
			local LetterRep;
			LetterRep := Concatenation(List(
						Filtered(x!.word,e->e in x!.free),
						fw -> LetterRepAssocWord(fw)
						));
			return ForAll(LetterRep,i->-i in LetterRep);
		end
);
#################################################################################
####                                                                         ####
####	                     Constrained Equation                            ####
####                                                                         ####
#################################################################################
InstallMethod( SetEquationConstraint, "for an equation and a list of images",
	[IsEquation,IsList,IsGroupHomomorphism],
	function(eq,const,hom)
		if not Length(const) = Length(EquationVariables(eq)) then 
			Error("There need to be as many images as equation variables.");
		fi;
		if not ForAll(const,x->x in Range(hom)) then
			Error("All constraint components need to be in the image of hom");
		fi;
		eq!.constraint := const;
		eq!.constrainthom := hom;
		SetIsConstrainedEquation(eq,true);
	end
);
InstallOtherMethod( Equation, "for an equation Group, a list of group elements, a constraint and a corresponding homomorphism.",
	[IsEquationGroup, IsList, IsList, IsGroupHomomorphism],
	function(eqG,word,const,hom)
		local eq;
		eq := Equation(eqG,word);
		SetEquationConstraint(eq,const,hom);
		return eq;
	end
);
InstallMethod( IsConstrainedEquation, "for an equation",
	[IsEquation],
	function(eq)
		return IsBound(eq!.constraint) and IsBound(eq!.constrainthom);
	end
);
#################################################################################
####                                                                         ####
####	                     EquationsHomomorphism                           ####
####                                                                         ####
#################################################################################

InstallMethod( EquationHomomorphism, "For an EquationGroup, a list of variables, and a list of images",
	[IsEquationGroup,IsList,IsList],
	function(eqG,gens,imgs)
		local ngens,nimgs,hom,fac;
		if not Length(gens) = Length(imgs) then
			Error("There must be as many images as generators");
		fi;
		if Length(gens) = 0 then
			hom := IdentityMapping(eqG);
		    SetName(hom,"<Identity EqHom>");
		    SetIsEquationHomomorphism(hom,true);
			return hom;
		fi;
		if not ForAll(gens,g->g in GeneratorsOfGroup(eqG!.free)) then
			TryNextMethod();
		fi;
		fac := (w->List(w,function(e)
								if e in eqG!.const then
									return 1; 
								fi; return 2;
								end));

		ngens := List(gens,gen->LetterRepAssocWord(gen)[1]);
		
		nimgs := List(imgs,function(x)
				if IsList(x) then
					return FreeProductElm(eqG,x,fac(x));
				elif x in eqG then
					return x;
				elif x in eqG!.const then
					return FreeProductElm(eqG,[x],[1]);
				elif x in eqG!.free then
					return FreeProductElm(eqG,[x],[2]);
				else
					Error("Wrong Input!");
				fi; end);
		hom := GroupHomomorphismByFunction(eqG,eqG,function(eq)
			local newword;
			newword := Flat(List(eq!.word,function(x)
					if x in eq!.group!.const then
						return x;
					fi;
					return List(LetterRepAssocWord(x),function(l)
						local pos,q;
							pos := Position(ngens,AbsInt(l));
							if pos = fail then
								return AssocWordByLetterRep(FamilyObj(x),[l]);
							else
								q := nimgs[pos]^SignInt(l);
								return q!.word;
							fi;	
						end);
					end));
				return FreeProductElm(eqG,newword,fac(newword));
			end);

		SetEquationHomomorphismImageData(hom,rec(imgs:=imgs,gens:=gens));
		SetIsEquationHomomorphism(hom,true);
		return hom;
	end);

InstallMethod( ViewObj, "For an EquationHomomorphism",
	[IsEquationHomomorphism],
	function(hom)
		local imDa;
		if HasEquationHomomorphismImageData(hom) then
			imDa := EquationHomomorphismImageData(hom);
			View(imDa.gens,"->",imDa.imgs);
		else
			TryNextMethod();
		fi;
	end);

InstallMethod( CompositionMapping2, "For two EquationHomomorphisms",
	FamSource1EqFamRange2,
	[ IsEquationHomomorphism, IsEquationHomomorphism ], 0,
	function(hom1,hom2)
		local mapi,reshom;
  		reshom:= CompositionMapping2General(hom1,hom2);
  		SetIsEquationHomomorphism(reshom,true);
  		return reshom;
	end);

InstallOtherMethod( ImageElm,
    "For an EquationHomomorphisms in CompositionMappingRep and an element",
    FamSourceEqFamElm,
    [ IsEquationHomomorphism and IsCompositionMappingRep, IsFreeProductElm ], 0,
    function( map, elm )
    return ImageElm( map!.map2, ImageElm( map!.map1, elm ));
    end );

InstallMethod( EquationEvaluation, "For an Equation, the list of variables and a list of images",
	[IsEquation, IsList, IsList],
	function(eq,gens,imgs)
		local var,hom,hom2;
		if not ForAll(imgs,elm->elm in eq!.const) then
			Error("All images need to be in the group of constants.");
		fi;
		var := EquationVariables(eq);
		if not Length(var)=Length(gens) then
			Error("There must be as many images as variables.");
		fi;
		if not Length(imgs)=Length(gens) then
			Error("There must be as many images as generators.");
		fi;
		if not ForAll(var,v->v in gens) then
			Error("All free variables must have an image.");
		fi;
		hom := EquationHomomorphism(eq!.group,gens,imgs);
		hom2 := GroupHomomorphismByFunction(eq!.group,eq!.const,q->Product(Image(hom,q)!.word),One(eq!.const));
		SetIsEquationHomomorphism(hom2,true);
		SetIsEvaluation(hom2,true);
		return hom2;
	end);

InstallOtherMethod( EquationEvaluation, "For an Equation, the list of variables and a list of images",
	[IsEquationGroup, IsList, IsList],
	function(eqG,gens,imgs)
		local var,hom,hom2;
		if not ForAll(imgs,elm->elm in eqG!.const) then
			Error("All images need to be in the group of constants.");
		fi;
		if not Length(imgs)=Length(gens) then
			Error("There must be as many images as generators.");
		fi;
		hom := EquationHomomorphism(eqG,gens,imgs);
		hom2 := GroupHomomorphismByFunction(eqG,eqG!.const,q->Product(Image(hom,q)!.word,One(eqG!.const)));
		SetIsEquationHomomorphism(hom2,true);
		SetIsEvaluation(hom2,true);
		return hom2;
	end);

InstallMethod( IsEvaluation, "For a group homomorphism",
	[IsGroupHomomorphism],
	h->IsEquationGroup(Source(h)) and Range(h)=Source(h)!.const);
	
InstallMethod( IsSolution, "For an EquationsHomomorphism and an Equation",
	[IsEvaluation, IsEquation],
	function(hom,eq)
		return IsOne(eq^hom); 
	end);

