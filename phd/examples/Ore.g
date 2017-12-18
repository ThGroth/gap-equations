ListToCycle := function(L)
	local newL,i;
	newL := [1..Maximum(L)];
	for i in [1..Length(L)-1] do
		newL[L[i]] := L[i+1];
	od;
	newL[L[Length(L)]] := L[1];
	return PermList(newL);
end;
CommuOfNormalCyc := function(n) #(1,2,…,2n+1)
	local c1,c2,i;
	if n <= 1 then
		Error("CommuOfNormalCyc: Needs Cycle of length at least 3");
	fi;
	if n mod 2=0 then
		c2 := [n+2..2*n+1];
		c2 := ListToCycle(Concatenation([1],c2));
		c1 := ();
		for i in [1..n] do
			c1 := c1*(1+i,2*n-i+2);
		od;
		#c1 = (2,2n+1)(3,2n)(4,2n-1)…(n+1,n+2)
		#c2 = (1,n+2,n+3,…,2n+1)
		return [c1,c2];
	fi;
	#n >= 3
	c2 := [n+3..2*n+1];
	c2 := ListToCycle(Concatenation([1,n+2,2],c2));
	c1 := (1,2)(2*n+1,3,2*n,4);
	for i in [5..n+1] do
		c1 := c1*(i,2*n+4-i);
	od;
	#c1 = (1,2)(2n+1,3,2n,4)(5,2n-1)…(n+1,n+3)
	#c2 = (1,n+2,2,n+3,…2n+1)
	return [c1,c2];
end;
MixedCommuOfNormalCyc := function(n) #(1,2,…,2n+1)
	local c1,c2,i;
	if n <= 1 then
		Error("CommuOfNormalCyc: Needs Cycle of length at least 3");
	fi;
	if n mod 2=0 then
		c2 := [n+2..2*n+1];
		c2 := ListToCycle(Concatenation([1],c2));
		c1 := (2*n+1,2,2*n,3);
		for i in [3..n] do
			c1 := c1*(1+i,2*n-i+2);
		od;
		#c1 = (2n+1,2,2n,3)(4,2n-1)…(n+1,n+2) odd
		#c2 = (1,n+2,n+3,…,2n+1)
		return [c1,c2];
	fi;
	#n >= 3
	c2 := [n+3..2*n+1];
	c2 := ListToCycle(Concatenation([1,n+2,2],c2));
	c1 := (1,2)(2*n+1,3)(2*n,4);
	for i in [5..n+1] do
		c1 := c1*(i,2*n+4-i);
	od;
	#c1 = (1,2)(2n+1,3)(2n,4)(5,2n-1)…(n+1,n+3) odd 
	##c2 = (1,n+2,2,n+3,…2n+1) even
	return [c1,c2];
end;
CommuOfTwoNormalCyc := function(a,n) # (1,2,…2a)(2a+1,…2n)
	local c1,c2,i;
	if n+1 <= 2*a then
		Error("CommuOfTwoNormalCyc: not compatible arguments ",a,",",n);
	fi;
	if n mod 2 =0 then
		c1 := (2*a+1,2);
		for i in [2..n] do
			c1 := c1 *(2*n+2-i,i+1);
		od;
		c2 := ListToCycle(Concatenation([1],[n+2..2*n],[2*a+1]));
		#c1 = (2a+1,2)(2n,3)(2n-1,4)…(n+2,n+1)
		#c2 = (1,n+2,n+3…2n,2a+1)
		return [c1,c2];
	fi;
	c1 := (1,2);
	if (a<>1) then
		c1 := c1 * (2*a+1,3,4);
	fi;
	for i in [3..n] do
		c1 := c1 * (2*n+3-i,i+1);
	od;
	c2 := ListToCycle(Concatenation([1,n+2,2],[n+3..2*n],[2*a+1]));
	#c1 = (1,2)(2n,4)(2n-1,5)…(n+3,n+1) if a=1
	#c1 = (1,2)(2a+1,3,2n,4)(2n-1,5)…(n+3,n+1) if a>1
	#c2 = (1,n+2,2,n+3,n+4,…2n,2a+1)
	return[c1,c2];
end;
MixedCommuOfTwoNormalCyc := function(a,n) # (1,2,…2a)(2a+1,…2n)
	local c1,c2,i;
	if n+1 <= 2*a then
		Error("CommuOfTwoNormalCyc: not compatible arguments ",a,",",n);
	fi;
	if n mod 2 =0 then
		if  a<> 1  then
			c1 := (2*a+1,2,2*n,3);
			for i in [3..n] do
				c1 := c1 *(2*n+2-i,i+1);
			od;
		else
			if n<> 2 then
				c1 := (2*a+1,2)*(2*n,3,2*n-1,4);
				for i in [4..n] do
					c1 := c1 *(2*n+2-i,i+1);
				od;
			else
				return [(1,2),(1,3)(2,4)];
			fi;
		fi;
		c2 := ListToCycle(Concatenation([1],[n+2..2*n],[2*a+1]));
		#c1 = (2a+1,2,2n,3)(2n-1,4)…(n+2,n+1) odd a>1
		#c1 = (2a+1,2)(2n,3,2n-1,4)…(n+2,n+1) odd a=1, n>2
		#c2 = (1,n+2,n+3…2n,2a+1)
		#c1 = (1,2), c2 = (1,3)(2,4) odd a=1, n=2
		return [c1,c2];
	fi;
	#n>=3
	c1 := (1,2);
	if (a<>1) then
		c1 := c1 * (2*a+1,3)(2*n,4);
		for i in [4..n] do
			c1 := c1 * (2*n+3-i,i+1);
		od;
	else
		if  n>3  then
			c1 := c1 *(2*n,4,2*n-1,5);
			for i in [5..n] do
				c1 := c1 * (2*n+3-i,i+1);
			od;
		else
			return [(1,4,3,6),(1,2,3,5,4)];
		fi;
	fi;
	c2 := ListToCycle(Concatenation([1,n+2,2],[n+3..2*n],[2*a+1]));
	#c1 = (1,2)(2a+1,3)(2n,4)(2n-1,5)…(n+3,n+1) odd a>1
	#c1 = (1,2)(2n,4,2n-1,5)…(n+3,n+1) if a=1 n>3
	#c2 = (1,n+2,2,n+3,n+4,…2n,2a+1)
	#c1 = (1,4,3,6) c2= (1,2,3,5,4) a=1,n=3
	return[c1,c2];
end;
ConjugateCycleToNormal := function(L)
	local j,p,i;
	p := ();
	L := ShallowCopy(L);
	for i in [1..Length(L)] do
		if i <> L[i] then
			j := L[i];
			p := p*(i,j);
			Apply(L,x->x^(i,j));
		fi;
	od;
	return p;	
end;
ConjugateCycleTupToNormal := function(L,K)
	local Lc,Kc,k,l,p,i,j;
	if Length(K)<Length(L) then
		Lc := ShallowCopy(K);
		Kc := ShallowCopy(L);
	else 
		Lc := ShallowCopy(L);
		Kc := ShallowCopy(K);
	fi;
	l:=Length(Lc);
	k:=Length(Kc);
	if l mod 2 <> 0 or k mod 2 <> 0 then
		Error("ConjugateCycleTupToNormal: Only applicable for even cycles. Given ",L,", ",K);
	fi;
	p := ();
	for i in [1..l] do
		if i <> Lc[i] then
			j := Lc[i];
			p := p*(i,j);
			Apply(Lc,x->x^(i,j));
			Apply(Kc,x->x^(i,j));
		fi;
	od;
	for i in [l+1..l+k] do
		if i <> Kc[i-l] then
			j := Kc[i-l];
			p := p*(i,j);
			Apply(Kc,x->x^(i,j));
		fi;
	od;
	return p;
end;

CommuOfOddCycle := function(L)
	local i,p;
	if Length(L) mod 2 <> 1 then
		Error("CommuOfOddCycle: Must get an odd Cylce given: ",L);
	fi;
	p := ConjugateCycleToNormal(L);
	L := CommuOfNormalCyc((Length(L)-1)/2);
	return [L[1]^(p^-1),L[2]^(p^-1)];
end;
CommuOfEvenCyclePair := function(L,K)
	local i,p;
	p := ConjugateCycleTupToNormal(L,K);
	L := CommuOfTwoNormalCyc(Minimum(Length(L),Length(K))/2,(Length(L)+Length(K))/2);
	return [L[1]^(p^-1),L[2]^(p^-1)];
end;
CommuOfSingle3Cycle := function(L)
	local l,K;
	K := [1..5];
	for l in L do
		RemoveSet(K,l);
	od;
	#return [ListToCycle(L),(L[2],L[3])(K[1],K[2])];
	#(1,2,3) = [(1,3,5),(1,3,5,2,4);
	return [(L[1],L[3],K[2]),(L[1],L[3],K[2],L[2],K[1])];
end;
CommuOfPairOf3Cylces := function(L,K)
	#(1,2,3)(4,5,6) = [(2,3)(5,6),(1,3),(4,6)]
	#return [(L[2],L[3])(K[2],K[3]),(L[1],L[3])(K[1],K[3])];
	#(1,2,3)(4,5,6) = [ (1,3)(5,6), (1,3,2,6,4) ]
	return [(L[1],L[3])(K[2],K[3]),(L[1],L[3],L[2],K[3],K[1])];
end;
CommuOf3CycleAndOddCycle := function(L,K)
	local n,p;
	n := Length(K);
	p := ConjugateCycleToNormal(K);
	K := MixedCommuOfNormalCyc((n-1)/2);
	return [(L[1],L[3])*K[1]^(p^-1),(L[1],L[3],L[2])*K[2]^(p^-1)];
end;
CommuOf3CycleAndTwoEvenCycles := function(L,K1,K2)
	local p;
	p := ConjugateCycleTupToNormal(K1,K2);
	K1 := MixedCommuOfTwoNormalCyc(Minimum(Length(K1),Length(K2))/2,(Length(K1)+Length(K2))/2);
	return [(L[1],L[3])*K1[1]^(p^-1),(L[1],L[3],L[2])*K1[2]^(p^-1)];
end;
GetCommutators := function(sig)
	local C3,Codd,Ceven,c,i,A,B,C,An,K1,K2;
	C3 := [];
	Codd := [];
	Ceven := [];
	K1 := ();
	K2 := ();
	An := Maximum(LargestMovedPoint(sig),5);
	#classify the cycles in length-3, odd, even
	if sig = () then
		return [(),()];
	fi;
	for c in Cycles(sig,[1..LargestMovedPoint(sig)]) do
		if Length(c)=1 then
			continue;
		fi;
		if Length(c)=3 then
			Add(C3,c);
		elif Length(c) mod 2 = 0 then
			Add(Ceven,c);
		else
			Add(Codd,c);
		fi;
	od;
	if Length(C3) mod 2 = 1 then
		if Length(Codd) = 0 then
			if Length(Ceven) = 0 then
				if Length(C3) = 1 then
					return CommuOfSingle3Cycle(C3[1]);
				fi;
				#|C3|>=3
				A := C3[1]; B:= C3[2]; C:= C3[3];
				#K1 := K1 * (A[1],A[2])(B[2],C[2],C[1],B[3]);
				#K2 := K2 * (A[1],A[3],B[3],B[1],C[2],C[3],A[2]);
				
				#(1,2,3)(4,5,6)(7,8,9) = [(1,7,4)(2,8,5)(3,9,6) , (1,9,8,7,4,2,3)]
				K1 := K1 * (A[1],C[1],B[1])(A[2],C[2],B[2])(A[3],C[3],B[3]);
				K2 := K2 * (A[1],C[3],C[2],C[1],B[1],A[2],A[3]);

				C3 := C3{[4..Length(C3)]};
				
			else
				# |Ceven|>=2
				A := CommuOf3CycleAndTwoEvenCycles(C3[1],Ceven[1],Ceven[2]);
				K1 := K1 * A[1];
				K2 := K2 * A[2];
				C3 := C3{[2..Length(C3)]};
				Ceven := Ceven{[3..Length(Ceven)]};
			fi;
		else
			A := CommuOf3CycleAndOddCycle(C3[1],Codd[1]);
			K1 := K1 * A[1];
			K2 := K2 * A[2];
			C3 := C3{[2..Length(C3)]};
			Codd := Codd{[2..Length(Codd)]};
		fi;
	fi;
	#Now |C3| is even.
	for i in [1,3..Length(C3)-1] do
		A := CommuOfPairOf3Cylces(C3[i],C3[i+1]);
		K1 := K1 * A[1];
		K2 := K2 * A[2];
	od;
	for i in [1,3..Length(Ceven)-1] do
		A := CommuOfEvenCyclePair(Ceven[i],Ceven[i+1]);
		K1 := K1 * A[1];
		K2 := K2 * A[2];
	od;
	for c in Codd do
		A := CommuOfOddCycle(c);
		K1 := K1 * A[1];
		K2 := K2 * A[2];
	od;
	return [K1,K2];
end;
###################################################################################
###################################################################################
###################################################################################
# Example use:
###################################################################################
###################################################################################
###################################################################################

GetCommutators((1,2,3)(4,5)(7,8,9,10));
#[ (1,3)(4,8,7,10), (1,3,2)(4,5,7,9,8), 10 ]
RandomCheck := function(n,num)
	local An,i,s,L;
	An := AlternatingGroup(n);
	i := 0;
	while i < num do
		s := Random(An);
		L := GetCommutators(s);
		if not SignPerm(L[1])+SignPerm(L[2]) = 2 then
			Print("Aaah not in A_n\n",s,"\n");
			break;
		fi;
		if not Comm(L) = s then
			Print("Aaah not a commutator\n",s,"\n");
			break;
		fi;
		i := i+1;
	od;
end;

###################################################################################
##  Some examples for
##  Proposition 4.20
# G := FreeGroup("g"); F := FreeGroup(2,"Z");
# n := 14;
# EqG := EquationGroup(G,F);
# eq := Equation(EqG,[Comm(F.1,F.2),G.1]);
# for g in ConjugacyClasses(AlternatingGroup(n)) do
# 	g := Representative(g);
# 	DEqG := DecompositionEquationGroup(EqG,n,[g]);
# 	gamma := GetCommutators(g^-1);
# 	deq := DecompositionEquation(DEqG,eq,gamma);
# 	Print(List(EquationComponents(DecomposedEquationDisjointForm(deq).eq),Genus),"\n");
# od;

