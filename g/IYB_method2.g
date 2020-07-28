#
# This files produces non-degenerate involutive solutions 
#
# Examples:
#
# gap> compute_IYB(6);
# Running savilerow for T=(). I found 68 solutions
# Running savilerow for T=(1,2). I found 127 solutions
# Running savilerow for T=(1,2)(3,4). I found 140 solutions
# Running savilerow for T=(1,2)(3,4)(5,6). I found 77 solutions
# Running savilerow for T=(1,2,3). I found 41 solutions
# Running savilerow for T=(1,2,3)(4,5). I found 36 solutions
# Running savilerow for T=(1,2,3)(4,5,6). I found 11 solutions
# Running savilerow for T=(1,2,3,4). I found 46 solutions
# Running savilerow for T=(1,2,3,4)(5,6). I found 38 solutions
# Running savilerow for T=(1,2,3,4,5). I found 5 solutions
# Running savilerow for T=(1,2,3,4,5,6). I found 6 solutions
# I constructed 595 solutions in 18318ms (= 0:00:18.318)
#
# gap> compute_IYB(7);
# Running savilerow for T=(). I found 336 solutions
# Running savilerow for T=(1,2). I found 671 solutions
# Running savilerow for T=(1,2)(3,4). I found 764 solutions
# Running savilerow for T=(1,2)(3,4)(5,6). I found 476 solutions
# Running savilerow for T=(1,2,3). I found 218 solutions
# Running savilerow for T=(1,2,3)(4,5). I found 258 solutions
# Running savilerow for T=(1,2,3)(4,5)(6,7). I found 120 solutions
# Running savilerow for T=(1,2,3)(4,5,6). I found 80 solutions
# Running savilerow for T=(1,2,3,4). I found 218 solutions
# Running savilerow for T=(1,2,3,4)(5,6). I found 218 solutions
# Running savilerow for T=(1,2,3,4)(5,6,7). I found 30 solutions
# Running savilerow for T=(1,2,3,4,5). I found 20 solutions
# Running savilerow for T=(1,2,3,4,5)(6,7). I found 10 solutions
# Running savilerow for T=(1,2,3,4,5,6). I found 36 solutions
# Running savilerow for T=(1,2,3,4,5,6,7). I found 1 solutions
# I constructed 3456 solutions in 85093ms (= 0:01:25.093)
#
# gap> compute_IYB(8);
# Running savilerow for T=(). I found 2041 solutions
# Running savilerow for T=(1,2). I found 4988 solutions
# Running savilerow for T=(1,2)(3,4). I found 7030 solutions
# Running savilerow for T=(1,2)(3,4)(5,6). I found 5906 solutions
# Running savilerow for T=(1,2)(3,4)(5,6)(7,8). I found 2474 solutions
# Running savilerow for T=(1,2,3). I found 1530 solutions
# Running savilerow for T=(1,2,3)(4,5). I found 2184 solutions
# Running savilerow for T=(1,2,3)(4,5)(6,7). I found 1386 solutions
# Running savilerow for T=(1,2,3)(4,5,6). I found 516 solutions
# Running savilerow for T=(1,2,3)(4,5,6)(7,8). I found 279 solutions
# Running savilerow for T=(1,2,3,4). I found 1512 solutions
# Running savilerow for T=(1,2,3,4)(5,6). I found 2222 solutions
# Running savilerow for T=(1,2,3,4)(5,6)(7,8). I found 1380 solutions
# Running savilerow for T=(1,2,3,4)(5,6,7). I found 324 solutions
# Running savilerow for T=(1,2,3,4)(5,6,7,8). I found 212 solutions
# Running savilerow for T=(1,2,3,4,5). I found 115 solutions
# Running savilerow for T=(1,2,3,4,5)(6,7). I found 100 solutions
# Running savilerow for T=(1,2,3,4,5)(6,7,8). I found 15 solutions
# Running savilerow for T=(1,2,3,4,5,6). I found 183 solutions
# Running savilerow for T=(1,2,3,4,5,6)(7,8). I found 112 solutions
# Running savilerow for T=(1,2,3,4,5,6,7). I found 7 solutions
# Running savilerow for T=(1,2,3,4,5,6,7,8). I found 14 solutions
# I constructed 34530 solutions in 3828320ms (= 1:03:48.320)

LoadPackage("IO");

create_file := function(n, T)
  local m,f,k,lines,perms,tmp1,tmp2;

  tmp1 := "";
  tmp2 := "";

  if T=() then
    perms := AsList(ConjugacyClass(SymmetricGroup(n),(1,2)));
  else
    perms := GeneratorsOfGroup(Centralizer(SymmetricGroup(n), T));
  fi;

  for k in perms do
    Append(tmp1, Concatenation(String(ListPerm(k,n)),",\n"));
    Append(tmp2, Concatenation(String(ListPerm(Inverse(k),n)),",\n"));
  od;

  lines := [ 
  "language ESSENCE' 1.0\n",
  Concatenation("letting n be ", String(n), "\n"),
  "letting perms be [\n", tmp1, "]\n",
  "letting inverses be [\n", tmp2, "]\n",
  "find M : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n",
  "such that\n",
  "forAll x : int(1..n) .",
  "  allDiff(M[x,..]),\n",
  "forAll x,y,z : int(1..n) .", 
  "  M[M[x,y],M[x,z]]=M[M[y,x],M[y,z]],\n",
  ];

  if T=() then
    Add(lines, "forAll x : int(1..n) .");
    Add(lines, "  M[x,x] = x,\n");
  else
    for k in [1..n] do
      Add(lines, Concatenation("M[", String(k), ",", String(k), "] = ", String(ListPerm(T, n)[k]),","));
    od;
  fi;

  Add(lines, Concatenation("forAll p : int(1..", String(Size(perms)), ") .\n\\
    flatten( [ M[i,j] | i : int(1..n), j : int(1..n)] )\n\\
    <=lex flatten( [ inverses[p,M[perms[p,i],perms[p,j]]] | i : int(1..n), j : int(1..n)] ),"));

  Add(lines, "\ntrue\n");
  return lines;
end;

create_files := function(n)
  local T,k,s,f,x; 
  k := 1;
  for T in List(ConjugacyClasses(SymmetricGroup(n)), Representative) do
    s := create_file(n, T);
    f := IO_File(Concatenation("size", String(n), "_", String(k), ".eprime"), "w");
    for x in s do
      IO_WriteLine(f, x);
    od;
    IO_Flush(f);
    IO_Close(f);
    k := k+1;
  od;
end;

twist_matrix := function(obj, f)
  local i,j,m,n;
  n := Size(obj);
  m := NullMat(n,n);
  for i in [1..n] do
    for j in [1..n] do
      if obj[i^Inverse(f)][j^Inverse(f)] <> 0 then
        m[i][j] := obj[i^Inverse(f)][j^Inverse(f)]^f;
      fi;
    od;
  od;
  return m;
end;

is_minimal := function(m, centralizer)
  local p;
  for p in centralizer do
    if Flat(m) > Flat(twist_matrix(m, p)) then
      return false;
      fi;
  od;
  return true;
end;

keep_minimal := function(n, filename, group, T)
  local l, k, x, m, f, done;
    
  l := [];
  k := 0;

  f := IO_File(filename, "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
      if is_minimal(m, group) then
        k := k+1;
        Add(l, m);
      fi; 
    fi;
  od; 
  Print("I found ", k, " solutions\n");  
  return l; 
end;

read_file := function(n, filename, T)
  local l, k, x, m, f, done;
    
  l := [];
  k := 0;

  f := IO_File(filename, "r");
  done := false;

  while not done do
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
      k := k+1;
      Add(l, m);
    fi;
  od; 
  Print("I found ", k, " solutions\n");  
  return l;
end;

compute_IYB := function(n)
  local m, l,T,k,s,f,x,t,output, t0, t1, mytime;

  t0 := NanosecondsSinceEpoch();

  t := [];
  k := Size(ConjugacyClasses(SymmetricGroup(n)));
  m := 0;
  s := "savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  LogTo();
  LogTo(Concatenation("IYB", String(n), "_method2.log"));

  create_files(n);

  for T in Reversed(List(ConjugacyClasses(SymmetricGroup(n)), Representative)) do
    Print("Running savilerow for T=", T, ". ");
    output := Concatenation("output", String(n), "_", String(k));
    Exec(Concatenation(s, "size", String(n), "_", String(k), ".eprime >", output));
    k := k-1;
    for x in keep_minimal(n, output, Centralizer(SymmetricGroup(n), T), T) do
      Add(t, x);
      m := m+1;
    od;
  od;

  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", m, " solutions in ", mytime, "ms (=", StringTime(mytime), ")\n");

  f := IO_File(Concatenation("CSsize", String(n), ".g"), "w");
  IO_WriteLine(f, Concatenation("CSsize", String(n), " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),",")); 
  od;
  IO_WriteLine(f, "];");
  IO_Flush(f);
  IO_Close(f);
end;


