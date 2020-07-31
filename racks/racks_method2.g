# gap> compute_racks(6);
# Running savilerow for T=(). I found 73 solutions
# Running savilerow for T=(1,2). I found 84 solutions
# Running savilerow for T=(1,2)(3,4). I found 62 solutions
# Running savilerow for T=(1,2)(3,4)(5,6). I found 21 solutions
# Running savilerow for T=(1,2,3). I found 43 solutions
# Running savilerow for T=(1,2,3)(4,5). I found 36 solutions
# Running savilerow for T=(1,2,3)(4,5,6). I found 6 solutions
# Running savilerow for T=(1,2,3,4). I found 14 solutions
# Running savilerow for T=(1,2,3,4)(5,6). I found 8 solutions
# Running savilerow for T=(1,2,3,4,5). I found 5 solutions
# Running savilerow for T=(1,2,3,4,5,6). I found 1 solutions
# I constructed 353 racks in 12737ms (= 0:00:12.737)
# gap> compute_racks(7);
# Running savilerow for T=(). I found 298 solutions
# Running savilerow for T=(1,2). I found 460 solutions
# Running savilerow for T=(1,2)(3,4). I found 392 solutions
# Running savilerow for T=(1,2)(3,4)(5,6). I found 156 solutions
# Running savilerow for T=(1,2,3). I found 219 solutions
# Running savilerow for T=(1,2,3)(4,5). I found 234 solutions
# Running savilerow for T=(1,2,3)(4,5)(6,7). I found 84 solutions
# Running savilerow for T=(1,2,3)(4,5,6). I found 48 solutions
# Running savilerow for T=(1,2,3,4). I found 76 solutions
# Running savilerow for T=(1,2,3,4)(5,6). I found 64 solutions
# Running savilerow for T=(1,2,3,4)(5,6,7). I found 12 solutions
# Running savilerow for T=(1,2,3,4,5). I found 20 solutions
# Running savilerow for T=(1,2,3,4,5)(6,7). I found 10 solutions
# Running savilerow for T=(1,2,3,4,5,6). I found 6 solutions
# Running savilerow for T=(1,2,3,4,5,6,7). I found 1 solutions
# I constructed 2080 racks in 76283ms (= 0:01:16.283)
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
  "  M[x,M[y,z]]=M[M[x,y],M[x,z]],\n",
 
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

compute_racks := function(n)
  local m, l,T,k,s,f,x,t,output, t0, t1, mytime;

  t0 := NanosecondsSinceEpoch();

  t := [];
  k := 1;
  m := 0;
  s := "savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  LogTo();
  LogTo(Concatenation("racks", String(n), "_method2.log"));

  create_files(n);

  for T in List(ConjugacyClasses(SymmetricGroup(n)), Representative) do
    Print("Running savilerow for T=", T, ". ");
    output := Concatenation("output", String(n), "_", String(k));
    Exec(Concatenation(s, "size", String(n), "_", String(k), ".eprime >", output));
    k := k+1;
    for x in keep_minimal(n, output, Centralizer(SymmetricGroup(n), T), T) do
      Add(t, x);
      m := m+1;
    od;
  od;

  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", m, " racks in ", mytime, "ms (=", StringTime(mytime), ")\n");

  f := IO_File(Concatenation("Rsize", String(n), ".g"), "w");
  IO_WriteLine(f, Concatenation("Rsize", String(n), " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),",")); 
  od;
  IO_WriteLine(f, "];");
  IO_Flush(f);
  IO_Close(f);
end;


