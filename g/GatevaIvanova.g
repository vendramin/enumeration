LoadPackage("yang");

is_irretractable := function(obj)
  return not IsRetractable(CycleSet2YB(obj));
end;

count := function(n)
  return Number([1..NrSmallCycleSets(n)], x->is_irretractable(SmallCycleSet(n,x))=true);
end;


# This files produces counterexamples to the conjecture of Gateva-Ivanova
# This means the script produces non-degenerate involutive square-free irretractable solutions 
#
# Examples:
#
LoadPackage("IO");

create_file := function(n)
  local x,y,tmp,m,f,k,lines,perms,tmp1,tmp2;

  tmp1 := "";
  tmp2 := "";

  perms := AsList(ConjugacyClass(SymmetricGroup(n),(1,2)));

  for k in perms do
    Append(tmp1, Concatenation(String(ListPerm(k,n)),",\n"));
    Append(tmp2, Concatenation(String(ListPerm(Inverse(k),n)),",\n"));
  od;
  
  tmp := "";
  for x in [1..n] do
    for y in [x+1..n] do
      Append(tmp, "exists y : int(1..n) .\n");
      Append(tmp, Concatenation("  M[",String(x),",y] != M[",String(y),",y],\n\n"));
    od;
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
  tmp,
  ];

  Add(lines, "forAll x : int(1..n) .");
  Add(lines, "  M[x,x] = x,\n");

  Add(lines, Concatenation("forAll p : int(1..", String(Size(perms)), ") .\n\\
    flatten( [ M[i,j] | i : int(1..n), j : int(1..n)] )\n\\
    <=lex flatten( [ inverses[p,M[perms[p,i],perms[p,j]]] | i : int(1..n), j : int(1..n)] ),"));

  Add(lines, "\ntrue\n");
  return lines;
end;

create_files := function(n)
  local T,k,s,f,x; 

  s := create_file(n);
  f := IO_File(Concatenation("GatevaIvanova", String(n), ".eprime"), "w");
  for x in s do
    IO_WriteLine(f, x);
  od;
  IO_Flush(f);
  IO_Close(f);
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

compute_irrIYB := function(n)
  local m, l,T,k,s,f,x,t,output,sym_n, t0, t1, mytime;

  t0 := NanosecondsSinceEpoch();

  t := [];
  k := 1;
  m := 0;
  s := "savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  LogTo();
  LogTo(Concatenation("GatevaIvanova", String(n), "_method1.log"));

  create_files(n);
  sym_n := SymmetricGroup(n);

  output := Concatenation("GatevaIvanova", String(n), ".output");
  Exec(Concatenation(s, "GatevaIvanova", String(n), ".eprime >", output));
  for x in keep_minimal(n, output, sym_n, ()) do
    Add(t, x);
    m := m+1;
  od;

  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", m, " counterexamples in ", mytime, "ms (=", StringTime(mytime), ")\n");

  f := IO_File(Concatenation("GatevaIvanova", String(n), ".g"), "w");
  IO_WriteLine(f, Concatenation("GatevaIvanova", String(n), " := ["));
  for x in t do
    IO_WriteLine(f, Concatenation(String(x),",")); 
  od;
  IO_WriteLine(f, "];");
  IO_Flush(f);
  IO_Close(f);
end;


