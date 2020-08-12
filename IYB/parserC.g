
LoadPackage("IO");

nr_products := 3;

create_file := function(n, T, perms, filename)
  local x,f,k,lines,tmp1,tmp2;

  tmp1 := "";
  tmp2 := "";

  for k in perms do
    Append(tmp1, Concatenation(String(List(ListPerm(k,n), y->y)),",\n"));
    Append(tmp2, Concatenation(String(List(ListPerm(Inverse(k),n), y->y)),",\n"));
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

  f := IO_File(filename, "w");
  for x in lines do
    IO_WriteLine(f, x);
  od;
  IO_Flush(f);
  IO_Close(f);
  
end;

compare := function(n, m, p, q)
  local i,j,old,new;
  for i in [1..n] do
    for j in [1..n] do
      old := m[i][j];
      new := m[i^p][j^p]^q;
      if old > new then
        return 1;
      elif old < new then
        return -1;
      fi;
    od;
  od;
  return 0;
end;

parser := function(n, T, centralizer, filename, output)
  local l, f, good, bad, x, p, q, out, r, m, done;

  good := 0;
  bad := 0;
  l := [];

  f := IO_File(filename, "r");
  out := IO_File(output, "w");
  
  IO_WriteLine(out, Concatenation(output, " := ["));
  
  done := false;

  while not done do 
    x := IO_ReadLine(f);
    if StartsWith(x, "Created information file") then
      done := true;
    elif StartsWith(x, "Solution") then
      m := EvalString(String(x{[46..Size(x)]}));
  #    Add(l, m);
  #  fi;
  #od;

  #Print("Savilerow produced ", Size(l), " solutions.\n");

  #for m in l do
    for p in centralizer do
      q := Inverse(p);
      r := compare(n, m, p, q);
      if r > 0 then 
        bad := bad+1;
        break;
      fi;
    od;
    if r <= 0 then
      good := good+1;
      IO_WriteLine(out, String(m));
    fi;
    fi;
  od;

  IO_WriteLine(out, "];");
  IO_Flush(out);
  IO_Close(out);

  IO_Flush(f);
  IO_Close(f);

  return good;

end;

run := function(n, T, filename)
  local k,l,cmd,f,x,t,output,gens, t0, t1, ta, tb, mytime, centralizer;

  t0 := NanosecondsSinceEpoch();

  cmd := "savilerow -run-solver -all-solutions -solutions-to-stdout-one-line ";

  centralizer := Centralizer(SymmetricGroup(n), T);
  gens := GeneratorsOfGroup(centralizer);

  create_file(n, T, Set(List(Tuples(gens, nr_products), Product)), Concatenation(filename, ".eprime"));

  ta := NanosecondsSinceEpoch();
  Print("Running savilerow for T=", T, ". ");
  output := Concatenation(filename, ".output");
  Exec(Concatenation(cmd, filename, ".eprime >", output));
  tb := NanosecondsSinceEpoch();

  mytime := Int(Float((tb-ta)/10^6));
  Print("Time: ", mytime, "ms (=", StringTime(mytime), ").\n");

  ta := NanosecondsSinceEpoch();
  k := parser(n, T, AsList(centralizer), Concatenation(filename, ".output"), Concatenation(filename, ".g"));
  tb := NanosecondsSinceEpoch();

  mytime := Int(Float((tb-ta)/10^6));
  Print("Repetitions removed in ", mytime, "ms (=", StringTime(mytime), ").\n");
    
  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print(k, " solutions in ", mytime, "ms (=", StringTime(mytime), ")\n");
  return k;

end;

construct := function(n)
  local t0, t1, Ts, T, k, mytime, s;
  
  t0 := NanosecondsSinceEpoch();

  LogTo();
  LogTo(Concatenation(String(n), ".log"));

  Ts := Reversed(List(ConjugacyClasses(SymmetricGroup(n)), Representative));
  k := Size(Ts);
  s := 0;
  
  for T in Ts do
    s := s+run(n, T, Concatenation(String(n), "_", String(k)));
    k := k-1;
    Print("--\n");
  od;

  t1 := NanosecondsSinceEpoch();
  mytime := Int(Float((t1-t0)/10^6));
  Print("I constructed ", s, " solutions in ", mytime, "ms (=", StringTime(mytime), ")\n");
end;
